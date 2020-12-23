%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EXQHwZonZp

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:56 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  240 (1096 expanded)
%              Number of leaves         :   39 ( 340 expanded)
%              Depth                    :   30
%              Number of atoms          : 2393 (29655 expanded)
%              Number of equality atoms :  198 (1724 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
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

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('9',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,
    ( ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('20',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ( ( k5_relat_1 @ X15 @ ( k2_funct_1 @ X15 ) )
        = ( k6_partfun1 @ X16 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relset_1 @ X16 @ X14 @ X15 )
       != X14 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X13: $i] :
      ( ( k6_partfun1 @ X13 )
      = ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ( ( k5_relat_1 @ X15 @ ( k2_funct_1 @ X15 ) )
        = ( k6_relat_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relset_1 @ X16 @ X14 @ X15 )
       != X14 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('34',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('37',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) ) )
        = ( k1_relat_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('41',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('42',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('43',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ( ( k5_relat_1 @ X15 @ ( k2_funct_1 @ X15 ) )
        = ( k6_relat_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relset_1 @ X16 @ X14 @ X15 )
       != X14 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('50',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','55','56','61','62'])).

thf('64',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) ) )
        = ( k1_relat_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('66',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('69',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67','70','71','72'])).

thf('74',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('78',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['76','80'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42','86','87','88','89'])).

thf('91',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('92',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['98','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

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

thf('107',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X19 @ X21 )
       != X19 )
      | ~ ( v2_funct_1 @ X21 )
      | ( ( k2_tops_2 @ X20 @ X19 @ X21 )
        = ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('108',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('111',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('112',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['110','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('121',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['120','125'])).

thf('127',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','109','118','119','128'])).

thf('130',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('132',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','97','132'])).

thf('134',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('136',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('138',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('139',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('143',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('145',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X19 @ X21 )
       != X19 )
      | ~ ( v2_funct_1 @ X21 )
      | ( ( k2_tops_2 @ X20 @ X19 @ X21 )
        = ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('146',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('149',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('151',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','147','148','149','150'])).

thf('152',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('154',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['139','140','143','154'])).

thf('156',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('157',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('158',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('159',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('161',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('162',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('163',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('164',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['9'])).

thf('165',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['162','167'])).

thf('169',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('170',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['161','170'])).

thf('172',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('173',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('174',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['171','172','173','174'])).

thf('176',plain,
    ( ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['160','175'])).

thf('177',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['159','178'])).

thf('180',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['134','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('182',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['180','181','182','183'])).

thf('185',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['9'])).

thf('187',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['185','186'])).

thf('188',plain,(
    ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['133','187'])).

thf('189',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('190',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('191',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['188','191'])).

thf('193',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','192'])).

thf('194',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('195',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['68','69'])).

thf('196',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['193','194','195','196','197'])).

thf('199',plain,(
    $false ),
    inference(simplify,[status(thm)],['198'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EXQHwZonZp
% 0.16/0.38  % Computer   : n015.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 19:08:53 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 369 iterations in 0.124s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.62  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.41/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.41/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.41/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.62  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.41/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.41/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.41/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.62  thf(t55_funct_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.62       ( ( v2_funct_1 @ A ) =>
% 0.41/0.62         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.41/0.62           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      (![X2 : $i]:
% 0.41/0.62         (~ (v2_funct_1 @ X2)
% 0.41/0.62          | ((k1_relat_1 @ X2) = (k2_relat_1 @ (k2_funct_1 @ X2)))
% 0.41/0.62          | ~ (v1_funct_1 @ X2)
% 0.41/0.62          | ~ (v1_relat_1 @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.41/0.62  thf(d3_struct_0, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.62  thf(t62_tops_2, conjecture,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( l1_struct_0 @ A ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.41/0.62           ( ![C:$i]:
% 0.41/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.62                 ( m1_subset_1 @
% 0.41/0.62                   C @ 
% 0.41/0.62                   ( k1_zfmisc_1 @
% 0.41/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.62               ( ( ( ( k2_relset_1 @
% 0.41/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.41/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.41/0.62                   ( v2_funct_1 @ C ) ) =>
% 0.41/0.62                 ( ( ( k1_relset_1 @
% 0.41/0.62                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.62                       ( k2_tops_2 @
% 0.41/0.62                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.41/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.41/0.62                   ( ( k2_relset_1 @
% 0.41/0.62                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.62                       ( k2_tops_2 @
% 0.41/0.62                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.41/0.62                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i]:
% 0.41/0.62        ( ( l1_struct_0 @ A ) =>
% 0.41/0.62          ( ![B:$i]:
% 0.41/0.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.41/0.62              ( ![C:$i]:
% 0.41/0.62                ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.62                    ( v1_funct_2 @
% 0.41/0.62                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.41/0.62                    ( m1_subset_1 @
% 0.41/0.62                      C @ 
% 0.41/0.62                      ( k1_zfmisc_1 @
% 0.41/0.62                        ( k2_zfmisc_1 @
% 0.41/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.41/0.62                  ( ( ( ( k2_relset_1 @
% 0.41/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.41/0.62                        ( k2_struct_0 @ B ) ) & 
% 0.41/0.62                      ( v2_funct_1 @ C ) ) =>
% 0.41/0.62                    ( ( ( k1_relset_1 @
% 0.41/0.62                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.62                          ( k2_tops_2 @
% 0.41/0.62                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.41/0.62                        ( k2_struct_0 @ B ) ) & 
% 0.41/0.62                      ( ( k2_relset_1 @
% 0.41/0.62                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.41/0.62                          ( k2_tops_2 @
% 0.41/0.62                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.41/0.62                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.62         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.41/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.62         = (k2_relat_1 @ sk_C))),
% 0.41/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.62         = (k2_struct_0 @ sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('6', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62          != (k2_struct_0 @ sk_B))
% 0.41/0.62        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62            != (k2_struct_0 @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62          != (k2_struct_0 @ sk_A)))
% 0.41/0.62         <= (~
% 0.41/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62                = (k2_struct_0 @ sk_A))))),
% 0.41/0.62      inference('split', [status(esa)], ['9'])).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62           != (k2_struct_0 @ sk_A))
% 0.41/0.62         | ~ (l1_struct_0 @ sk_B)))
% 0.41/0.62         <= (~
% 0.41/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62                = (k2_struct_0 @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['8', '10'])).
% 0.41/0.62  thf('12', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62          != (k2_struct_0 @ sk_A)))
% 0.41/0.62         <= (~
% 0.41/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62                = (k2_struct_0 @ sk_A))))),
% 0.41/0.62      inference('demod', [status(thm)], ['11', '12'])).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62           != (k2_struct_0 @ sk_A))
% 0.41/0.62         | ~ (l1_struct_0 @ sk_A)))
% 0.41/0.62         <= (~
% 0.41/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62                = (k2_struct_0 @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['7', '13'])).
% 0.41/0.62  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62          != (k2_struct_0 @ sk_A)))
% 0.41/0.62         <= (~
% 0.41/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62                = (k2_struct_0 @ sk_A))))),
% 0.41/0.62      inference('demod', [status(thm)], ['14', '15'])).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62          != (k2_struct_0 @ sk_A)))
% 0.41/0.62         <= (~
% 0.41/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62                = (k2_struct_0 @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['6', '16'])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62           != (k2_struct_0 @ sk_A))
% 0.41/0.62         | ~ (l1_struct_0 @ sk_B)))
% 0.41/0.62         <= (~
% 0.41/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62                = (k2_struct_0 @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['1', '17'])).
% 0.41/0.62  thf('19', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('21', plain,
% 0.41/0.62      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.41/0.62          != (k2_struct_0 @ sk_A)))
% 0.41/0.62         <= (~
% 0.41/0.62             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.62                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.62                = (k2_struct_0 @ sk_A))))),
% 0.41/0.62      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.41/0.62  thf('22', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t35_funct_2, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.41/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.41/0.62           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.41/0.62             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.62         (((X14) = (k1_xboole_0))
% 0.41/0.62          | ~ (v1_funct_1 @ X15)
% 0.41/0.62          | ~ (v1_funct_2 @ X15 @ X16 @ X14)
% 0.41/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 0.41/0.62          | ((k5_relat_1 @ X15 @ (k2_funct_1 @ X15)) = (k6_partfun1 @ X16))
% 0.41/0.62          | ~ (v2_funct_1 @ X15)
% 0.41/0.62          | ((k2_relset_1 @ X16 @ X14 @ X15) != (X14)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.41/0.62  thf(redefinition_k6_partfun1, axiom,
% 0.41/0.62    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.41/0.62  thf('25', plain, (![X13 : $i]: ((k6_partfun1 @ X13) = (k6_relat_1 @ X13))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.62         (((X14) = (k1_xboole_0))
% 0.41/0.62          | ~ (v1_funct_1 @ X15)
% 0.41/0.62          | ~ (v1_funct_2 @ X15 @ X16 @ X14)
% 0.41/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 0.41/0.62          | ((k5_relat_1 @ X15 @ (k2_funct_1 @ X15)) = (k6_relat_1 @ X16))
% 0.41/0.62          | ~ (v2_funct_1 @ X15)
% 0.41/0.62          | ((k2_relset_1 @ X16 @ X14 @ X15) != (X14)))),
% 0.41/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.62  thf('27', plain,
% 0.41/0.62      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.62          != (u1_struct_0 @ sk_B))
% 0.41/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.41/0.62        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.41/0.62            = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.41/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['23', '26'])).
% 0.41/0.62  thf('28', plain,
% 0.41/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.62         = (k2_struct_0 @ sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('29', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      ((((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B))
% 0.41/0.62        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.41/0.62            = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.41/0.62  thf('33', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf('34', plain,
% 0.41/0.62      ((((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B))
% 0.41/0.62        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.41/0.62            = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['32', '33'])).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.41/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.41/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.41/0.62        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.41/0.62            = (k6_relat_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['22', '34'])).
% 0.41/0.62  thf('36', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf('37', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('38', plain,
% 0.41/0.62      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.41/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.41/0.62        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.41/0.62            = (k6_relat_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.41/0.62          = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['38'])).
% 0.41/0.62  thf(t58_funct_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.62       ( ( v2_funct_1 @ A ) =>
% 0.41/0.62         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.41/0.62             ( k1_relat_1 @ A ) ) & 
% 0.41/0.62           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.41/0.62             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.41/0.62  thf('40', plain,
% 0.41/0.62      (![X3 : $i]:
% 0.41/0.62         (~ (v2_funct_1 @ X3)
% 0.41/0.62          | ((k2_relat_1 @ (k5_relat_1 @ X3 @ (k2_funct_1 @ X3)))
% 0.41/0.62              = (k1_relat_1 @ X3))
% 0.41/0.62          | ~ (v1_funct_1 @ X3)
% 0.41/0.62          | ~ (v1_relat_1 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.41/0.62  thf('41', plain,
% 0.41/0.62      ((((k2_relat_1 @ (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62          = (k1_relat_1 @ sk_C))
% 0.41/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.41/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.41/0.62      inference('sup+', [status(thm)], ['39', '40'])).
% 0.41/0.62  thf(t71_relat_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.41/0.62       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.41/0.62  thf('42', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.62  thf('43', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.62  thf('44', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.62  thf('45', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('46', plain,
% 0.41/0.62      (((m1_subset_1 @ sk_C @ 
% 0.41/0.62         (k1_zfmisc_1 @ 
% 0.41/0.62          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.41/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['44', '45'])).
% 0.41/0.62  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.41/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.62  thf('49', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.62         (((X14) = (k1_xboole_0))
% 0.41/0.62          | ~ (v1_funct_1 @ X15)
% 0.41/0.62          | ~ (v1_funct_2 @ X15 @ X16 @ X14)
% 0.41/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 0.41/0.62          | ((k5_relat_1 @ X15 @ (k2_funct_1 @ X15)) = (k6_relat_1 @ X16))
% 0.41/0.62          | ~ (v2_funct_1 @ X15)
% 0.41/0.62          | ((k2_relset_1 @ X16 @ X14 @ X15) != (X14)))),
% 0.41/0.62      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.62  thf('50', plain,
% 0.41/0.62      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.62          != (k2_struct_0 @ sk_B))
% 0.41/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.41/0.62        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.41/0.62            = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.41/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.41/0.62  thf('51', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.62  thf('52', plain,
% 0.41/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.62         = (k2_struct_0 @ sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('53', plain,
% 0.41/0.62      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.62          = (k2_struct_0 @ sk_B))
% 0.41/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['51', '52'])).
% 0.41/0.62  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('55', plain,
% 0.41/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.62         = (k2_struct_0 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['53', '54'])).
% 0.41/0.62  thf('56', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('57', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.62  thf('58', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('59', plain,
% 0.41/0.62      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.41/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['57', '58'])).
% 0.41/0.62  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('61', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['59', '60'])).
% 0.41/0.62  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('63', plain,
% 0.41/0.62      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.41/0.62        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.41/0.62            = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['50', '55', '56', '61', '62'])).
% 0.41/0.62  thf('64', plain,
% 0.41/0.62      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.41/0.62        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.41/0.62            = (k6_relat_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.62      inference('simplify', [status(thm)], ['63'])).
% 0.41/0.62  thf('65', plain,
% 0.41/0.62      (![X3 : $i]:
% 0.41/0.62         (~ (v2_funct_1 @ X3)
% 0.41/0.62          | ((k2_relat_1 @ (k5_relat_1 @ X3 @ (k2_funct_1 @ X3)))
% 0.41/0.62              = (k1_relat_1 @ X3))
% 0.41/0.62          | ~ (v1_funct_1 @ X3)
% 0.41/0.62          | ~ (v1_relat_1 @ X3))),
% 0.41/0.62      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.41/0.62  thf('66', plain,
% 0.41/0.62      ((((k2_relat_1 @ (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.62          = (k1_relat_1 @ sk_C))
% 0.41/0.62        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.41/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.41/0.62      inference('sup+', [status(thm)], ['64', '65'])).
% 0.41/0.62  thf('67', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.41/0.62  thf('68', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(cc1_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( v1_relat_1 @ C ) ))).
% 0.41/0.62  thf('69', plain,
% 0.41/0.62      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.62         ((v1_relat_1 @ X4)
% 0.41/0.62          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.62  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.41/0.62  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('72', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('73', plain,
% 0.41/0.62      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.41/0.62        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['66', '67', '70', '71', '72'])).
% 0.41/0.62  thf('74', plain,
% 0.41/0.62      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.41/0.62        | ~ (l1_struct_0 @ sk_A)
% 0.41/0.62        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['43', '73'])).
% 0.41/0.62  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('76', plain,
% 0.41/0.62      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.41/0.62        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['74', '75'])).
% 0.41/0.62  thf('77', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.62  thf(fc2_struct_0, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.62       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.62  thf('78', plain,
% 0.41/0.62      (![X18 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X18))
% 0.41/0.62          | ~ (l1_struct_0 @ X18)
% 0.41/0.62          | (v2_struct_0 @ X18))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.41/0.62  thf('79', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.41/0.62          | ~ (l1_struct_0 @ X0)
% 0.41/0.62          | (v2_struct_0 @ X0)
% 0.41/0.62          | ~ (l1_struct_0 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['77', '78'])).
% 0.41/0.62  thf('80', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((v2_struct_0 @ X0)
% 0.41/0.62          | ~ (l1_struct_0 @ X0)
% 0.41/0.62          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['79'])).
% 0.41/0.62  thf('81', plain,
% 0.41/0.62      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.41/0.62        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.41/0.62        | ~ (l1_struct_0 @ sk_B)
% 0.41/0.62        | (v2_struct_0 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['76', '80'])).
% 0.41/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.41/0.62  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.62  thf('83', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('84', plain,
% 0.41/0.62      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.41/0.62  thf('85', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('86', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.41/0.62      inference('clc', [status(thm)], ['84', '85'])).
% 0.41/0.62  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.41/0.62  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('89', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('90', plain,
% 0.41/0.62      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 0.41/0.62        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['41', '42', '86', '87', '88', '89'])).
% 0.41/0.62  thf('91', plain,
% 0.41/0.62      (![X18 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X18))
% 0.41/0.62          | ~ (l1_struct_0 @ X18)
% 0.41/0.62          | (v2_struct_0 @ X18))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.41/0.62  thf('92', plain,
% 0.41/0.62      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.41/0.62        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 0.41/0.62        | (v2_struct_0 @ sk_B)
% 0.41/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['90', '91'])).
% 0.41/0.62  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.62  thf('94', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('95', plain,
% 0.41/0.62      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.41/0.62  thf('96', plain, (~ (v2_struct_0 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('97', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.41/0.62      inference('clc', [status(thm)], ['95', '96'])).
% 0.41/0.62  thf('98', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.62  thf('99', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.62  thf('100', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('101', plain,
% 0.41/0.62      (((m1_subset_1 @ sk_C @ 
% 0.41/0.62         (k1_zfmisc_1 @ 
% 0.41/0.62          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.41/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.62      inference('sup+', [status(thm)], ['99', '100'])).
% 0.41/0.62  thf('102', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('103', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.41/0.62      inference('demod', [status(thm)], ['101', '102'])).
% 0.41/0.62  thf('104', plain,
% 0.41/0.62      (((m1_subset_1 @ sk_C @ 
% 0.41/0.62         (k1_zfmisc_1 @ 
% 0.41/0.62          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.41/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['98', '103'])).
% 0.41/0.62  thf('105', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('106', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_C @ 
% 0.41/0.62        (k1_zfmisc_1 @ 
% 0.41/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.41/0.62      inference('demod', [status(thm)], ['104', '105'])).
% 0.41/0.62  thf(d4_tops_2, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.41/0.62         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.41/0.62  thf('107', plain,
% 0.41/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.41/0.62         (((k2_relset_1 @ X20 @ X19 @ X21) != (X19))
% 0.41/0.62          | ~ (v2_funct_1 @ X21)
% 0.41/0.62          | ((k2_tops_2 @ X20 @ X19 @ X21) = (k2_funct_1 @ X21))
% 0.41/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.41/0.62          | ~ (v1_funct_2 @ X21 @ X20 @ X19)
% 0.41/0.62          | ~ (v1_funct_1 @ X21))),
% 0.41/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.41/0.62  thf('108', plain,
% 0.41/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.41/0.62        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.41/0.62        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.62            = (k2_funct_1 @ sk_C))
% 0.41/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.41/0.62        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.62            != (k2_struct_0 @ sk_B)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['106', '107'])).
% 0.41/0.62  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('110', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.62  thf('111', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.62  thf('112', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('113', plain,
% 0.41/0.62      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.41/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.62      inference('sup+', [status(thm)], ['111', '112'])).
% 0.41/0.62  thf('114', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('115', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['113', '114'])).
% 0.41/0.62  thf('116', plain,
% 0.41/0.62      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.41/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['110', '115'])).
% 0.41/0.62  thf('117', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('118', plain,
% 0.41/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['116', '117'])).
% 0.41/0.62  thf('119', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('120', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.62  thf('121', plain,
% 0.41/0.62      (![X17 : $i]:
% 0.41/0.62         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.62  thf('122', plain,
% 0.41/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.62         = (k2_struct_0 @ sk_B))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('123', plain,
% 0.41/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.62          = (k2_struct_0 @ sk_B))
% 0.41/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.62      inference('sup+', [status(thm)], ['121', '122'])).
% 0.41/0.62  thf('124', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('125', plain,
% 0.41/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.41/0.62         = (k2_struct_0 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['123', '124'])).
% 0.41/0.62  thf('126', plain,
% 0.41/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.62          = (k2_struct_0 @ sk_B))
% 0.41/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.41/0.62      inference('sup+', [status(thm)], ['120', '125'])).
% 0.41/0.62  thf('127', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('128', plain,
% 0.41/0.63      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.63         = (k2_struct_0 @ sk_B))),
% 0.41/0.63      inference('demod', [status(thm)], ['126', '127'])).
% 0.41/0.63  thf('129', plain,
% 0.41/0.63      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.63          = (k2_funct_1 @ sk_C))
% 0.41/0.63        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.41/0.63      inference('demod', [status(thm)], ['108', '109', '118', '119', '128'])).
% 0.41/0.63  thf('130', plain,
% 0.41/0.63      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.63         = (k2_funct_1 @ sk_C))),
% 0.41/0.63      inference('simplify', [status(thm)], ['129'])).
% 0.41/0.63  thf('131', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.63  thf('132', plain,
% 0.41/0.63      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.41/0.63         = (k2_funct_1 @ sk_C))),
% 0.41/0.63      inference('demod', [status(thm)], ['130', '131'])).
% 0.41/0.63  thf('133', plain,
% 0.41/0.63      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.63          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.41/0.63         <= (~
% 0.41/0.63             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63                = (k2_struct_0 @ sk_A))))),
% 0.41/0.63      inference('demod', [status(thm)], ['21', '97', '132'])).
% 0.41/0.63  thf('134', plain,
% 0.41/0.63      (![X2 : $i]:
% 0.41/0.63         (~ (v2_funct_1 @ X2)
% 0.41/0.63          | ((k2_relat_1 @ X2) = (k1_relat_1 @ (k2_funct_1 @ X2)))
% 0.41/0.63          | ~ (v1_funct_1 @ X2)
% 0.41/0.63          | ~ (v1_relat_1 @ X2))),
% 0.41/0.63      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.41/0.63  thf('135', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_C @ 
% 0.41/0.63        (k1_zfmisc_1 @ 
% 0.41/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.41/0.63      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.63  thf('136', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.63  thf('137', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_C @ 
% 0.41/0.63        (k1_zfmisc_1 @ 
% 0.41/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.41/0.63      inference('demod', [status(thm)], ['135', '136'])).
% 0.41/0.63  thf(dt_k2_tops_2, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i]:
% 0.41/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.63       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.41/0.63         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.41/0.63         ( m1_subset_1 @
% 0.41/0.63           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.41/0.63           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.41/0.63  thf('138', plain,
% 0.41/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.41/0.63         ((m1_subset_1 @ (k2_tops_2 @ X22 @ X23 @ X24) @ 
% 0.41/0.63           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.41/0.63          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.41/0.63          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.41/0.63          | ~ (v1_funct_1 @ X24))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.41/0.63  thf('139', plain,
% 0.41/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.41/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.41/0.63        | (m1_subset_1 @ 
% 0.41/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.41/0.63           (k1_zfmisc_1 @ 
% 0.41/0.63            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['137', '138'])).
% 0.41/0.63  thf('140', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('141', plain,
% 0.41/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.41/0.63      inference('demod', [status(thm)], ['59', '60'])).
% 0.41/0.63  thf('142', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.63  thf('143', plain,
% 0.41/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.41/0.63      inference('demod', [status(thm)], ['141', '142'])).
% 0.41/0.63  thf('144', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_C @ 
% 0.41/0.63        (k1_zfmisc_1 @ 
% 0.41/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.41/0.63      inference('demod', [status(thm)], ['46', '47'])).
% 0.41/0.63  thf('145', plain,
% 0.41/0.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.41/0.63         (((k2_relset_1 @ X20 @ X19 @ X21) != (X19))
% 0.41/0.63          | ~ (v2_funct_1 @ X21)
% 0.41/0.63          | ((k2_tops_2 @ X20 @ X19 @ X21) = (k2_funct_1 @ X21))
% 0.41/0.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.41/0.63          | ~ (v1_funct_2 @ X21 @ X20 @ X19)
% 0.41/0.63          | ~ (v1_funct_1 @ X21))),
% 0.41/0.63      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.41/0.63  thf('146', plain,
% 0.41/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.41/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.41/0.63        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.63            = (k2_funct_1 @ sk_C))
% 0.41/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.41/0.63        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.63            != (k2_struct_0 @ sk_B)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['144', '145'])).
% 0.41/0.63  thf('147', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('148', plain,
% 0.41/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.41/0.63      inference('demod', [status(thm)], ['59', '60'])).
% 0.41/0.63  thf('149', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('150', plain,
% 0.41/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.63         = (k2_struct_0 @ sk_B))),
% 0.41/0.63      inference('demod', [status(thm)], ['53', '54'])).
% 0.41/0.63  thf('151', plain,
% 0.41/0.63      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.63          = (k2_funct_1 @ sk_C))
% 0.41/0.63        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.41/0.63      inference('demod', [status(thm)], ['146', '147', '148', '149', '150'])).
% 0.41/0.63  thf('152', plain,
% 0.41/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.41/0.63         = (k2_funct_1 @ sk_C))),
% 0.41/0.63      inference('simplify', [status(thm)], ['151'])).
% 0.41/0.63  thf('153', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.63  thf('154', plain,
% 0.41/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.41/0.63         = (k2_funct_1 @ sk_C))),
% 0.41/0.63      inference('demod', [status(thm)], ['152', '153'])).
% 0.41/0.63  thf('155', plain,
% 0.41/0.63      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.63        (k1_zfmisc_1 @ 
% 0.41/0.63         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.41/0.63      inference('demod', [status(thm)], ['139', '140', '143', '154'])).
% 0.41/0.63  thf('156', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.41/0.63      inference('clc', [status(thm)], ['95', '96'])).
% 0.41/0.63  thf('157', plain,
% 0.41/0.63      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.63        (k1_zfmisc_1 @ 
% 0.41/0.63         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.41/0.63      inference('demod', [status(thm)], ['155', '156'])).
% 0.41/0.63  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i]:
% 0.41/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.63  thf('158', plain,
% 0.41/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.63         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.41/0.63          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.41/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.63  thf('159', plain,
% 0.41/0.63      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.63         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['157', '158'])).
% 0.41/0.63  thf('160', plain,
% 0.41/0.63      (![X17 : $i]:
% 0.41/0.63         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.63  thf('161', plain,
% 0.41/0.63      (![X17 : $i]:
% 0.41/0.63         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.63  thf('162', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.63  thf('163', plain,
% 0.41/0.63      (![X17 : $i]:
% 0.41/0.63         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.41/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.63  thf('164', plain,
% 0.41/0.63      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63          != (k2_struct_0 @ sk_B)))
% 0.41/0.63         <= (~
% 0.41/0.63             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63                = (k2_struct_0 @ sk_B))))),
% 0.41/0.63      inference('split', [status(esa)], ['9'])).
% 0.41/0.63  thf('165', plain,
% 0.41/0.63      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63           != (k2_struct_0 @ sk_B))
% 0.41/0.63         | ~ (l1_struct_0 @ sk_B)))
% 0.41/0.63         <= (~
% 0.41/0.63             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63                = (k2_struct_0 @ sk_B))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['163', '164'])).
% 0.41/0.63  thf('166', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('167', plain,
% 0.41/0.63      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63          != (k2_struct_0 @ sk_B)))
% 0.41/0.63         <= (~
% 0.41/0.63             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63                = (k2_struct_0 @ sk_B))))),
% 0.41/0.63      inference('demod', [status(thm)], ['165', '166'])).
% 0.41/0.63  thf('168', plain,
% 0.41/0.63      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63          != (k2_struct_0 @ sk_B)))
% 0.41/0.63         <= (~
% 0.41/0.63             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63                = (k2_struct_0 @ sk_B))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['162', '167'])).
% 0.41/0.63  thf('169', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.63  thf('170', plain,
% 0.41/0.63      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63          != (k2_relat_1 @ sk_C)))
% 0.41/0.63         <= (~
% 0.41/0.63             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63                = (k2_struct_0 @ sk_B))))),
% 0.41/0.63      inference('demod', [status(thm)], ['168', '169'])).
% 0.41/0.63  thf('171', plain,
% 0.41/0.63      (((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63           != (k2_relat_1 @ sk_C))
% 0.41/0.63         | ~ (l1_struct_0 @ sk_B)))
% 0.41/0.63         <= (~
% 0.41/0.63             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63                = (k2_struct_0 @ sk_B))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['161', '170'])).
% 0.41/0.63  thf('172', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.41/0.63      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.63  thf('173', plain,
% 0.41/0.63      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.41/0.63         = (k2_funct_1 @ sk_C))),
% 0.41/0.63      inference('demod', [status(thm)], ['152', '153'])).
% 0.41/0.63  thf('174', plain, ((l1_struct_0 @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('175', plain,
% 0.41/0.63      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.41/0.63         <= (~
% 0.41/0.63             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63                = (k2_struct_0 @ sk_B))))),
% 0.41/0.63      inference('demod', [status(thm)], ['171', '172', '173', '174'])).
% 0.41/0.63  thf('176', plain,
% 0.41/0.63      (((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.63           (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 0.41/0.63         | ~ (l1_struct_0 @ sk_A)))
% 0.41/0.63         <= (~
% 0.41/0.63             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63                = (k2_struct_0 @ sk_B))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['160', '175'])).
% 0.41/0.63  thf('177', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('178', plain,
% 0.41/0.63      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.63          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.41/0.63         <= (~
% 0.41/0.63             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63                = (k2_struct_0 @ sk_B))))),
% 0.41/0.63      inference('demod', [status(thm)], ['176', '177'])).
% 0.41/0.63  thf('179', plain,
% 0.41/0.63      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.41/0.63         <= (~
% 0.41/0.63             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63                = (k2_struct_0 @ sk_B))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['159', '178'])).
% 0.41/0.63  thf('180', plain,
% 0.41/0.63      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.41/0.63         | ~ (v1_relat_1 @ sk_C)
% 0.41/0.63         | ~ (v1_funct_1 @ sk_C)
% 0.41/0.63         | ~ (v2_funct_1 @ sk_C)))
% 0.41/0.63         <= (~
% 0.41/0.63             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63                = (k2_struct_0 @ sk_B))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['134', '179'])).
% 0.41/0.63  thf('181', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.63      inference('sup-', [status(thm)], ['68', '69'])).
% 0.41/0.63  thf('182', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('183', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('184', plain,
% 0.41/0.63      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.41/0.63         <= (~
% 0.41/0.63             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63                = (k2_struct_0 @ sk_B))))),
% 0.41/0.63      inference('demod', [status(thm)], ['180', '181', '182', '183'])).
% 0.41/0.63  thf('185', plain,
% 0.41/0.63      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63          = (k2_struct_0 @ sk_B)))),
% 0.41/0.63      inference('simplify', [status(thm)], ['184'])).
% 0.41/0.63  thf('186', plain,
% 0.41/0.63      (~
% 0.41/0.63       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63          = (k2_struct_0 @ sk_A))) | 
% 0.41/0.63       ~
% 0.41/0.63       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63          = (k2_struct_0 @ sk_B)))),
% 0.41/0.63      inference('split', [status(esa)], ['9'])).
% 0.41/0.63  thf('187', plain,
% 0.41/0.63      (~
% 0.41/0.63       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.41/0.63          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.41/0.63          = (k2_struct_0 @ sk_A)))),
% 0.41/0.63      inference('sat_resolution*', [status(thm)], ['185', '186'])).
% 0.41/0.63  thf('188', plain,
% 0.41/0.63      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.63         (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.41/0.63      inference('simpl_trail', [status(thm)], ['133', '187'])).
% 0.41/0.63  thf('189', plain,
% 0.41/0.63      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.41/0.63        (k1_zfmisc_1 @ 
% 0.41/0.63         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.41/0.63      inference('demod', [status(thm)], ['155', '156'])).
% 0.41/0.63  thf('190', plain,
% 0.41/0.63      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.63         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.41/0.63          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.41/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.63  thf('191', plain,
% 0.41/0.63      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.41/0.63         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['189', '190'])).
% 0.41/0.63  thf('192', plain,
% 0.41/0.63      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.41/0.63      inference('demod', [status(thm)], ['188', '191'])).
% 0.41/0.63  thf('193', plain,
% 0.41/0.63      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.41/0.63        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.63        | ~ (v2_funct_1 @ sk_C))),
% 0.41/0.63      inference('sup-', [status(thm)], ['0', '192'])).
% 0.41/0.63  thf('194', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.41/0.63      inference('clc', [status(thm)], ['84', '85'])).
% 0.41/0.63  thf('195', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.63      inference('sup-', [status(thm)], ['68', '69'])).
% 0.41/0.63  thf('196', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('197', plain, ((v2_funct_1 @ sk_C)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('198', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.41/0.63      inference('demod', [status(thm)], ['193', '194', '195', '196', '197'])).
% 0.41/0.63  thf('199', plain, ($false), inference('simplify', [status(thm)], ['198'])).
% 0.41/0.63  
% 0.41/0.63  % SZS output end Refutation
% 0.41/0.63  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
