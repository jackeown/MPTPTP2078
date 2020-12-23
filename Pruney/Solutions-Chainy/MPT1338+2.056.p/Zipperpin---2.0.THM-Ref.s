%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4or0VBiZGK

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 708 expanded)
%              Number of leaves         :   39 ( 224 expanded)
%              Depth                    :   27
%              Number of atoms          : 1874 (19265 expanded)
%              Number of equality atoms :  153 (1096 expanded)
%              Maximal formula depth    :   16 (   6 average)

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

thf('2',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
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

thf('14',plain,(
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

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('22',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('25',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

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

thf('34',plain,(
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

thf('35',plain,(
    ! [X13: $i] :
      ( ( k6_partfun1 @ X13 )
      = ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
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
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','42','43','48','49'])).

thf('51',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) ) )
        = ( k1_relat_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('53',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( u1_struct_0 @ sk_A ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('54',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('56',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54','57','58','59'])).

thf('61',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('64',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('65',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','11','27','70'])).

thf('72',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('76',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('77',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('83',plain,(
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

thf('84',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('87',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('89',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('90',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('92',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['77','78','81','92'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('94',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('95',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('98',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('100',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('103',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('104',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('105',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('106',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('107',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','115'])).

thf('117',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('120',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','120'])).

thf('122',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','121'])).

thf('123',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['55','56'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('130',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['128','129'])).

thf('131',plain,(
    ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['71','130'])).

thf('132',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['77','78','81','92'])).

thf('133',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('134',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['131','134'])).

thf('136',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['55','56'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['136','137','138','139'])).

thf('141',plain,(
    $false ),
    inference(simplify,[status(thm)],['140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4or0VBiZGK
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:59:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 464 iterations in 0.116s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.57  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.21/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.57  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.57  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.57  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.57  thf(t55_funct_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.57       ( ( v2_funct_1 @ A ) =>
% 0.21/0.57         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.21/0.57           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (![X2 : $i]:
% 0.21/0.57         (~ (v2_funct_1 @ X2)
% 0.21/0.57          | ((k1_relat_1 @ X2) = (k2_relat_1 @ (k2_funct_1 @ X2)))
% 0.21/0.57          | ~ (v1_funct_1 @ X2)
% 0.21/0.57          | ~ (v1_relat_1 @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.57  thf(d3_struct_0, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X17 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf(t62_tops_2, conjecture,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_struct_0 @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.57                 ( m1_subset_1 @
% 0.21/0.57                   C @ 
% 0.21/0.57                   ( k1_zfmisc_1 @
% 0.21/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.57               ( ( ( ( k2_relset_1 @
% 0.21/0.57                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.21/0.57                     ( k2_struct_0 @ B ) ) & 
% 0.21/0.57                   ( v2_funct_1 @ C ) ) =>
% 0.21/0.57                 ( ( ( k1_relset_1 @
% 0.21/0.57                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.57                       ( k2_tops_2 @
% 0.21/0.57                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.57                     ( k2_struct_0 @ B ) ) & 
% 0.21/0.57                   ( ( k2_relset_1 @
% 0.21/0.57                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.57                       ( k2_tops_2 @
% 0.21/0.57                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.57                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i]:
% 0.21/0.57        ( ( l1_struct_0 @ A ) =>
% 0.21/0.57          ( ![B:$i]:
% 0.21/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.57              ( ![C:$i]:
% 0.21/0.57                ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.57                    ( v1_funct_2 @
% 0.21/0.57                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.57                    ( m1_subset_1 @
% 0.21/0.57                      C @ 
% 0.21/0.57                      ( k1_zfmisc_1 @
% 0.21/0.57                        ( k2_zfmisc_1 @
% 0.21/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.57                  ( ( ( ( k2_relset_1 @
% 0.21/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.21/0.57                        ( k2_struct_0 @ B ) ) & 
% 0.21/0.57                      ( v2_funct_1 @ C ) ) =>
% 0.21/0.57                    ( ( ( k1_relset_1 @
% 0.21/0.57                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.57                          ( k2_tops_2 @
% 0.21/0.57                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.57                        ( k2_struct_0 @ B ) ) & 
% 0.21/0.57                      ( ( k2_relset_1 @
% 0.21/0.57                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.57                          ( k2_tops_2 @
% 0.21/0.57                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.21/0.57                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57          != (k2_struct_0 @ sk_B))
% 0.21/0.57        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57            != (k2_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57          != (k2_struct_0 @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_A))))),
% 0.21/0.57      inference('split', [status(esa)], ['2'])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57           != (k2_struct_0 @ sk_A))
% 0.21/0.57         | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.57  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57          != (k2_struct_0 @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.57         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.21/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_relat_1 @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('11', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X17 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d4_tops_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.57       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.21/0.57         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (((k2_relset_1 @ X20 @ X19 @ X21) != (X19))
% 0.21/0.57          | ~ (v2_funct_1 @ X21)
% 0.21/0.57          | ((k2_tops_2 @ X20 @ X19 @ X21) = (k2_funct_1 @ X21))
% 0.21/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.21/0.57          | ~ (v1_funct_2 @ X21 @ X20 @ X19)
% 0.21/0.57          | ~ (v1_funct_1 @ X21))),
% 0.21/0.57      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.21/0.57        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57            = (k2_funct_1 @ sk_C))
% 0.21/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.57        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57            != (u1_struct_0 @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.57  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('18', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57          = (k2_funct_1 @ sk_C))
% 0.21/0.57        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.21/0.57  thf('21', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57          = (k2_funct_1 @ sk_C))
% 0.21/0.57        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.57        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57            = (k2_funct_1 @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['12', '22'])).
% 0.21/0.57  thf('24', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('25', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.21/0.57        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57            = (k2_funct_1 @ sk_C)))),
% 0.21/0.57      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_funct_1 @ sk_C))),
% 0.21/0.57      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (![X17 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (![X17 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_C @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.57  thf(t35_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.57       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.21/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.57           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.21/0.57             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.57         (((X14) = (k1_xboole_0))
% 0.21/0.57          | ~ (v1_funct_1 @ X15)
% 0.21/0.57          | ~ (v1_funct_2 @ X15 @ X16 @ X14)
% 0.21/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 0.21/0.57          | ((k5_relat_1 @ X15 @ (k2_funct_1 @ X15)) = (k6_partfun1 @ X16))
% 0.21/0.57          | ~ (v2_funct_1 @ X15)
% 0.21/0.57          | ((k2_relset_1 @ X16 @ X14 @ X15) != (X14)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.21/0.57  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.57    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.57  thf('35', plain, (![X13 : $i]: ((k6_partfun1 @ X13) = (k6_relat_1 @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.57         (((X14) = (k1_xboole_0))
% 0.21/0.57          | ~ (v1_funct_1 @ X15)
% 0.21/0.57          | ~ (v1_funct_2 @ X15 @ X16 @ X14)
% 0.21/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 0.21/0.57          | ((k5_relat_1 @ X15 @ (k2_funct_1 @ X15)) = (k6_relat_1 @ X16))
% 0.21/0.57          | ~ (v2_funct_1 @ X15)
% 0.21/0.57          | ((k2_relset_1 @ X16 @ X14 @ X15) != (X14)))),
% 0.21/0.57      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57          != (k2_struct_0 @ sk_B))
% 0.21/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.57        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.21/0.57            = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.57        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['33', '36'])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (![X17 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57          = (k2_struct_0 @ sk_B))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.57  thf('41', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.57  thf('43', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      (![X17 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['44', '45'])).
% 0.21/0.57  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.57  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.21/0.57        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.21/0.57            = (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['37', '42', '43', '48', '49'])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.21/0.57        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.21/0.57            = (k6_relat_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.57  thf(t58_funct_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.57       ( ( v2_funct_1 @ A ) =>
% 0.21/0.57         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.21/0.57             ( k1_relat_1 @ A ) ) & 
% 0.21/0.57           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.21/0.57             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      (![X3 : $i]:
% 0.21/0.57         (~ (v2_funct_1 @ X3)
% 0.21/0.57          | ((k2_relat_1 @ (k5_relat_1 @ X3 @ (k2_funct_1 @ X3)))
% 0.21/0.57              = (k1_relat_1 @ X3))
% 0.21/0.57          | ~ (v1_funct_1 @ X3)
% 0.21/0.57          | ~ (v1_relat_1 @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      ((((k2_relat_1 @ (k6_relat_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57          = (k1_relat_1 @ sk_C))
% 0.21/0.57        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.21/0.57        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.57        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.57      inference('sup+', [status(thm)], ['51', '52'])).
% 0.21/0.57  thf(t71_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.57       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.57  thf('54', plain, (![X1 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(cc1_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( v1_relat_1 @ C ) ))).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.57         ((v1_relat_1 @ X4)
% 0.21/0.57          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.57  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.57      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.57  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('59', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('60', plain,
% 0.21/0.57      ((((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.21/0.57        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['53', '54', '57', '58', '59'])).
% 0.21/0.57  thf('61', plain,
% 0.21/0.57      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.57        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['28', '60'])).
% 0.21/0.57  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('63', plain,
% 0.21/0.57      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.21/0.57        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.57  thf(fc5_struct_0, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.57       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.21/0.57  thf('64', plain,
% 0.21/0.57      (![X18 : $i]:
% 0.21/0.57         (~ (v1_xboole_0 @ (k2_struct_0 @ X18))
% 0.21/0.57          | ~ (l1_struct_0 @ X18)
% 0.21/0.57          | (v2_struct_0 @ X18))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.21/0.57  thf('65', plain,
% 0.21/0.57      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.57        | ((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.21/0.57        | (v2_struct_0 @ sk_B)
% 0.21/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.57  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.57  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('68', plain,
% 0.21/0.57      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.21/0.57  thf('69', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('70', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.21/0.57      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['6', '11', '27', '70'])).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      (![X2 : $i]:
% 0.21/0.57         (~ (v2_funct_1 @ X2)
% 0.21/0.57          | ((k2_relat_1 @ X2) = (k1_relat_1 @ (k2_funct_1 @ X2)))
% 0.21/0.57          | ~ (v1_funct_1 @ X2)
% 0.21/0.57          | ~ (v1_relat_1 @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.21/0.57  thf('73', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.57  thf('74', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('75', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.21/0.57      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.57  thf(dt_k2_tops_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.57       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.21/0.57         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.21/0.57         ( m1_subset_1 @
% 0.21/0.57           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.21/0.57           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.21/0.57  thf('76', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (k2_tops_2 @ X22 @ X23 @ X24) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.21/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.21/0.57          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.21/0.57          | ~ (v1_funct_1 @ X24))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.21/0.57  thf('77', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.21/0.57        | (m1_subset_1 @ 
% 0.21/0.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.21/0.57           (k1_zfmisc_1 @ 
% 0.21/0.57            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.57  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('79', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.57  thf('80', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('81', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['79', '80'])).
% 0.21/0.57  thf('82', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.57  thf('83', plain,
% 0.21/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (((k2_relset_1 @ X20 @ X19 @ X21) != (X19))
% 0.21/0.57          | ~ (v2_funct_1 @ X21)
% 0.21/0.57          | ((k2_tops_2 @ X20 @ X19 @ X21) = (k2_funct_1 @ X21))
% 0.21/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.21/0.57          | ~ (v1_funct_2 @ X21 @ X20 @ X19)
% 0.21/0.57          | ~ (v1_funct_1 @ X21))),
% 0.21/0.57      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.21/0.57  thf('84', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.21/0.57        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57            = (k2_funct_1 @ sk_C))
% 0.21/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.21/0.57        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57            != (k2_struct_0 @ sk_B)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['82', '83'])).
% 0.21/0.57  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('86', plain,
% 0.21/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.57  thf('87', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('88', plain,
% 0.21/0.57      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.57  thf('89', plain,
% 0.21/0.57      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57          = (k2_funct_1 @ sk_C))
% 0.21/0.57        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 0.21/0.57  thf('90', plain,
% 0.21/0.57      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.21/0.57         = (k2_funct_1 @ sk_C))),
% 0.21/0.57      inference('simplify', [status(thm)], ['89'])).
% 0.21/0.57  thf('91', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('92', plain,
% 0.21/0.57      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.57         = (k2_funct_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.57  thf('93', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['77', '78', '81', '92'])).
% 0.21/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.57  thf('94', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.21/0.57          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.57  thf('95', plain,
% 0.21/0.57      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['93', '94'])).
% 0.21/0.57  thf('96', plain,
% 0.21/0.57      (![X17 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('97', plain,
% 0.21/0.57      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.57         = (k2_funct_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.57  thf('98', plain,
% 0.21/0.57      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.57          = (k2_funct_1 @ sk_C))
% 0.21/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup+', [status(thm)], ['96', '97'])).
% 0.21/0.57  thf('99', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.21/0.57      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.57  thf('100', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('101', plain,
% 0.21/0.57      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.21/0.57         = (k2_funct_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.21/0.57  thf('102', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.21/0.57      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.57  thf('103', plain,
% 0.21/0.57      (![X17 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('104', plain,
% 0.21/0.57      (![X17 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('105', plain,
% 0.21/0.57      (![X17 : $i]:
% 0.21/0.57         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.57  thf('106', plain,
% 0.21/0.57      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57          != (k2_struct_0 @ sk_B)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('split', [status(esa)], ['2'])).
% 0.21/0.57  thf('107', plain,
% 0.21/0.57      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57           != (k2_struct_0 @ sk_B))
% 0.21/0.57         | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['105', '106'])).
% 0.21/0.57  thf('108', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('109', plain,
% 0.21/0.57      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57          != (k2_struct_0 @ sk_B)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['107', '108'])).
% 0.21/0.57  thf('110', plain,
% 0.21/0.57      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57           != (k2_struct_0 @ sk_B))
% 0.21/0.57         | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['104', '109'])).
% 0.21/0.57  thf('111', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('112', plain,
% 0.21/0.57      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57          != (k2_struct_0 @ sk_B)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['110', '111'])).
% 0.21/0.57  thf('113', plain,
% 0.21/0.57      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57           != (k2_struct_0 @ sk_B))
% 0.21/0.57         | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['103', '112'])).
% 0.21/0.57  thf('114', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('115', plain,
% 0.21/0.57      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57          != (k2_struct_0 @ sk_B)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['113', '114'])).
% 0.21/0.57  thf('116', plain,
% 0.21/0.57      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57          != (k2_struct_0 @ sk_B)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['102', '115'])).
% 0.21/0.57  thf('117', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('118', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('119', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.21/0.57      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.57  thf('120', plain,
% 0.21/0.57      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.21/0.57          != (k2_relat_1 @ sk_C)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.21/0.57  thf('121', plain,
% 0.21/0.57      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['101', '120'])).
% 0.21/0.57  thf('122', plain,
% 0.21/0.57      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['95', '121'])).
% 0.21/0.57  thf('123', plain,
% 0.21/0.57      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.21/0.57         | ~ (v1_relat_1 @ sk_C)
% 0.21/0.57         | ~ (v1_funct_1 @ sk_C)
% 0.21/0.57         | ~ (v2_funct_1 @ sk_C)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['72', '122'])).
% 0.21/0.57  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.57      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.57  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('127', plain,
% 0.21/0.57      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57                = (k2_struct_0 @ sk_B))))),
% 0.21/0.57      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 0.21/0.57  thf('128', plain,
% 0.21/0.57      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57          = (k2_struct_0 @ sk_B)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['127'])).
% 0.21/0.57  thf('129', plain,
% 0.21/0.57      (~
% 0.21/0.57       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57          = (k2_struct_0 @ sk_A))) | 
% 0.21/0.57       ~
% 0.21/0.57       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57          = (k2_struct_0 @ sk_B)))),
% 0.21/0.57      inference('split', [status(esa)], ['2'])).
% 0.21/0.57  thf('130', plain,
% 0.21/0.57      (~
% 0.21/0.57       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.21/0.57          = (k2_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['128', '129'])).
% 0.21/0.57  thf('131', plain,
% 0.21/0.57      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57         (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['71', '130'])).
% 0.21/0.57  thf('132', plain,
% 0.21/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.21/0.57        (k1_zfmisc_1 @ 
% 0.21/0.57         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['77', '78', '81', '92'])).
% 0.21/0.57  thf('133', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.57         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.21/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.57  thf('134', plain,
% 0.21/0.57      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.57         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['132', '133'])).
% 0.21/0.57  thf('135', plain,
% 0.21/0.57      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['131', '134'])).
% 0.21/0.57  thf('136', plain,
% 0.21/0.57      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.21/0.57        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.57        | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '135'])).
% 0.21/0.57  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.57      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.57  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('139', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('140', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['136', '137', '138', '139'])).
% 0.21/0.57  thf('141', plain, ($false), inference('simplify', [status(thm)], ['140'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
