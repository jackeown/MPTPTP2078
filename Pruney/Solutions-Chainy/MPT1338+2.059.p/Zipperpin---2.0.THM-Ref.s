%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pFFEzgw3I4

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:57 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 399 expanded)
%              Number of leaves         :   37 ( 132 expanded)
%              Depth                    :   21
%              Number of atoms          : 1643 (10999 expanded)
%              Number of equality atoms :  123 ( 606 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_struct_0 @ B )
                    = k1_xboole_0 )
                 => ( ( k2_struct_0 @ A )
                    = k1_xboole_0 ) )
               => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                  = ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( l1_struct_0 @ X23 )
      | ( ( k2_struct_0 @ X23 )
        = k1_xboole_0 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) @ X25 @ ( k2_struct_0 @ X23 ) )
        = ( k2_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t52_tops_2])).

thf('17',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( ( k8_relset_1 @ X12 @ X13 @ X11 @ X14 )
        = ( k10_relat_1 @ X11 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('26',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18','19','20','21','24','25','26'])).

thf('28',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('34',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X20 @ X22 )
       != X20 )
      | ~ ( v2_funct_1 @ X22 )
      | ( ( k2_tops_2 @ X21 @ X20 @ X22 )
        = ( k2_funct_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('44',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('47',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','49'])).

thf('51',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('52',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relset_1 @ X17 @ X16 @ X15 )
       != X16 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('55',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('59',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('63',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('66',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('67',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X20 @ X22 )
       != X20 )
      | ~ ( v2_funct_1 @ X22 )
      | ( ( k2_tops_2 @ X21 @ X20 @ X22 )
        = ( k2_funct_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('84',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('93',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77','84','85','93'])).

thf('95',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('97',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['34'])).

thf('99',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('104',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','104'])).

thf('106',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','105'])).

thf('107',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108','109','110'])).

thf('112',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['34'])).

thf('114',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['112','113'])).

thf('115',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['50','114'])).

thf('116',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('117',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('118',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['115','118'])).

thf('120',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','119'])).

thf('121',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('125',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','124'])).

thf('126',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['125'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('127',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['13','126','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pFFEzgw3I4
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:15:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 295 iterations in 0.092s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.36/0.58  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.36/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.58  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.36/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.58  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.36/0.58  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.58  thf(t62_tops_2, conjecture,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( l1_struct_0 @ A ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.36/0.58           ( ![C:$i]:
% 0.36/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.58                 ( m1_subset_1 @
% 0.36/0.58                   C @ 
% 0.36/0.58                   ( k1_zfmisc_1 @
% 0.36/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.58               ( ( ( ( k2_relset_1 @
% 0.36/0.58                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.58                     ( k2_struct_0 @ B ) ) & 
% 0.36/0.58                   ( v2_funct_1 @ C ) ) =>
% 0.36/0.58                 ( ( ( k1_relset_1 @
% 0.36/0.58                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.58                       ( k2_tops_2 @
% 0.36/0.58                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.36/0.58                     ( k2_struct_0 @ B ) ) & 
% 0.36/0.58                   ( ( k2_relset_1 @
% 0.36/0.58                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.58                       ( k2_tops_2 @
% 0.36/0.58                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.36/0.58                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i]:
% 0.36/0.58        ( ( l1_struct_0 @ A ) =>
% 0.36/0.58          ( ![B:$i]:
% 0.36/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.36/0.58              ( ![C:$i]:
% 0.36/0.58                ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.58                    ( v1_funct_2 @
% 0.36/0.58                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.58                    ( m1_subset_1 @
% 0.36/0.58                      C @ 
% 0.36/0.58                      ( k1_zfmisc_1 @
% 0.36/0.58                        ( k2_zfmisc_1 @
% 0.36/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.58                  ( ( ( ( k2_relset_1 @
% 0.36/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.36/0.58                        ( k2_struct_0 @ B ) ) & 
% 0.36/0.58                      ( v2_funct_1 @ C ) ) =>
% 0.36/0.58                    ( ( ( k1_relset_1 @
% 0.36/0.58                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.58                          ( k2_tops_2 @
% 0.36/0.58                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.36/0.58                        ( k2_struct_0 @ B ) ) & 
% 0.36/0.58                      ( ( k2_relset_1 @
% 0.36/0.58                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.36/0.58                          ( k2_tops_2 @
% 0.36/0.58                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.36/0.58                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.36/0.58    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.36/0.58  thf('0', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.58  thf('1', plain,
% 0.36/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.58         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.36/0.58          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.36/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.58  thf('2', plain,
% 0.36/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58         = (k2_relat_1 @ sk_C))),
% 0.36/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.58  thf('3', plain,
% 0.36/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58         = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf(d3_struct_0, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.36/0.58  thf('5', plain,
% 0.36/0.58      (![X18 : $i]:
% 0.36/0.58         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.58  thf(fc2_struct_0, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.58       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.58  thf('6', plain,
% 0.36/0.58      (![X19 : $i]:
% 0.36/0.58         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.36/0.58          | ~ (l1_struct_0 @ X19)
% 0.36/0.58          | (v2_struct_0 @ X19))),
% 0.36/0.58      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.58  thf('7', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.36/0.58          | ~ (l1_struct_0 @ X0)
% 0.36/0.58          | (v2_struct_0 @ X0)
% 0.36/0.58          | ~ (l1_struct_0 @ X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.58  thf('8', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((v2_struct_0 @ X0)
% 0.36/0.58          | ~ (l1_struct_0 @ X0)
% 0.36/0.58          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['7'])).
% 0.36/0.58  thf('9', plain,
% 0.36/0.58      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.36/0.58        | ~ (l1_struct_0 @ sk_B)
% 0.36/0.58        | (v2_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup-', [status(thm)], ['4', '8'])).
% 0.36/0.58  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('11', plain,
% 0.36/0.58      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.36/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.58  thf('12', plain, (~ (v2_struct_0 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('13', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.36/0.58      inference('clc', [status(thm)], ['11', '12'])).
% 0.36/0.58  thf(t169_relat_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( v1_relat_1 @ A ) =>
% 0.36/0.58       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.36/0.58  thf('14', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.36/0.58          | ~ (v1_relat_1 @ X0))),
% 0.36/0.58      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.36/0.58  thf('15', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(t52_tops_2, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( l1_struct_0 @ A ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( l1_struct_0 @ B ) =>
% 0.36/0.58           ( ![C:$i]:
% 0.36/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.36/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.36/0.58                 ( m1_subset_1 @
% 0.36/0.58                   C @ 
% 0.36/0.58                   ( k1_zfmisc_1 @
% 0.36/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.36/0.58               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.58                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.58                 ( ( k8_relset_1 @
% 0.36/0.58                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.36/0.58                     ( k2_struct_0 @ B ) ) =
% 0.36/0.58                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.36/0.58  thf('16', plain,
% 0.36/0.58      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.58         (~ (l1_struct_0 @ X23)
% 0.36/0.58          | ((k2_struct_0 @ X23) = (k1_xboole_0))
% 0.36/0.58          | ((k8_relset_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23) @ X25 @ 
% 0.36/0.58              (k2_struct_0 @ X23)) = (k2_struct_0 @ X24))
% 0.36/0.58          | ~ (m1_subset_1 @ X25 @ 
% 0.36/0.58               (k1_zfmisc_1 @ 
% 0.36/0.58                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))))
% 0.36/0.58          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23))
% 0.36/0.58          | ~ (v1_funct_1 @ X25)
% 0.36/0.58          | ~ (l1_struct_0 @ X24))),
% 0.36/0.58      inference('cnf', [status(esa)], [t52_tops_2])).
% 0.36/0.58  thf('17', plain,
% 0.36/0.58      ((~ (l1_struct_0 @ sk_A)
% 0.36/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.58        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.58            (k2_struct_0 @ sk_B)) = (k2_struct_0 @ sk_A))
% 0.36/0.58        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.36/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.58  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('20', plain,
% 0.36/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('21', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('22', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(redefinition_k8_relset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.58       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.36/0.58  thf('23', plain,
% 0.36/0.58      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.58         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.36/0.58          | ((k8_relset_1 @ X12 @ X13 @ X11 @ X14) = (k10_relat_1 @ X11 @ X14)))),
% 0.36/0.58      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.36/0.58  thf('24', plain,
% 0.36/0.58      (![X0 : $i]:
% 0.36/0.58         ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.36/0.58           X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.58  thf('25', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('26', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('27', plain,
% 0.36/0.58      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.36/0.58        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.36/0.58      inference('demod', [status(thm)],
% 0.36/0.58                ['17', '18', '19', '20', '21', '24', '25', '26'])).
% 0.36/0.58  thf('28', plain,
% 0.36/0.58      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.36/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.58        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['14', '27'])).
% 0.36/0.58  thf('29', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(cc1_relset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.58       ( v1_relat_1 @ C ) ))).
% 0.36/0.58  thf('30', plain,
% 0.36/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.58         ((v1_relat_1 @ X2)
% 0.36/0.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.36/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.58  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.58  thf('32', plain,
% 0.36/0.58      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.36/0.58        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.36/0.58      inference('demod', [status(thm)], ['28', '31'])).
% 0.36/0.58  thf(t55_funct_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.58       ( ( v2_funct_1 @ A ) =>
% 0.36/0.58         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.36/0.58           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.36/0.58  thf('33', plain,
% 0.36/0.58      (![X1 : $i]:
% 0.36/0.58         (~ (v2_funct_1 @ X1)
% 0.36/0.58          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.36/0.58          | ~ (v1_funct_1 @ X1)
% 0.36/0.58          | ~ (v1_relat_1 @ X1))),
% 0.36/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.58  thf('34', plain,
% 0.36/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58          != (k2_struct_0 @ sk_B))
% 0.36/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58            != (k2_struct_0 @ sk_A)))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('35', plain,
% 0.36/0.58      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58          != (k2_struct_0 @ sk_A)))
% 0.36/0.58         <= (~
% 0.36/0.58             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58                = (k2_struct_0 @ sk_A))))),
% 0.36/0.58      inference('split', [status(esa)], ['34'])).
% 0.36/0.58  thf('36', plain,
% 0.36/0.58      (![X18 : $i]:
% 0.36/0.58         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.58  thf('37', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(d4_tops_2, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.58       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.36/0.58         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.36/0.58  thf('38', plain,
% 0.36/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.58         (((k2_relset_1 @ X21 @ X20 @ X22) != (X20))
% 0.36/0.58          | ~ (v2_funct_1 @ X22)
% 0.36/0.58          | ((k2_tops_2 @ X21 @ X20 @ X22) = (k2_funct_1 @ X22))
% 0.36/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.36/0.58          | ~ (v1_funct_2 @ X22 @ X21 @ X20)
% 0.36/0.58          | ~ (v1_funct_1 @ X22))),
% 0.36/0.58      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.36/0.58  thf('39', plain,
% 0.36/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58            = (k2_funct_1 @ sk_C))
% 0.36/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58            != (u1_struct_0 @ sk_B)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.58  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('41', plain,
% 0.36/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('42', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('43', plain,
% 0.36/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58         = (k2_relat_1 @ sk_C))),
% 0.36/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.58  thf('44', plain,
% 0.36/0.58      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58          = (k2_funct_1 @ sk_C))
% 0.36/0.58        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.36/0.58      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.36/0.58  thf('45', plain,
% 0.36/0.58      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.36/0.58        | ~ (l1_struct_0 @ sk_B)
% 0.36/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58            = (k2_funct_1 @ sk_C)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['36', '44'])).
% 0.36/0.58  thf('46', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('48', plain,
% 0.36/0.58      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.36/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58            = (k2_funct_1 @ sk_C)))),
% 0.36/0.58      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.36/0.58  thf('49', plain,
% 0.36/0.58      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58         = (k2_funct_1 @ sk_C))),
% 0.36/0.58      inference('simplify', [status(thm)], ['48'])).
% 0.36/0.58  thf('50', plain,
% 0.36/0.58      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58          (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 0.36/0.58         <= (~
% 0.36/0.58             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58                = (k2_struct_0 @ sk_A))))),
% 0.36/0.58      inference('demod', [status(thm)], ['35', '49'])).
% 0.36/0.58  thf('51', plain,
% 0.36/0.58      (![X1 : $i]:
% 0.36/0.58         (~ (v2_funct_1 @ X1)
% 0.36/0.58          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 0.36/0.58          | ~ (v1_funct_1 @ X1)
% 0.36/0.58          | ~ (v1_relat_1 @ X1))),
% 0.36/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.58  thf('52', plain,
% 0.36/0.58      (![X18 : $i]:
% 0.36/0.58         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.58  thf('53', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(t31_funct_2, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.58       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.36/0.58         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.36/0.58           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.36/0.58           ( m1_subset_1 @
% 0.36/0.58             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.36/0.58  thf('54', plain,
% 0.36/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.58         (~ (v2_funct_1 @ X15)
% 0.36/0.58          | ((k2_relset_1 @ X17 @ X16 @ X15) != (X16))
% 0.36/0.58          | (m1_subset_1 @ (k2_funct_1 @ X15) @ 
% 0.36/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.36/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.36/0.58          | ~ (v1_funct_2 @ X15 @ X17 @ X16)
% 0.36/0.58          | ~ (v1_funct_1 @ X15))),
% 0.36/0.58      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.36/0.58  thf('55', plain,
% 0.36/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.36/0.58        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.58           (k1_zfmisc_1 @ 
% 0.36/0.58            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.36/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58            != (u1_struct_0 @ sk_B))
% 0.36/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.36/0.58  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('57', plain,
% 0.36/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('58', plain,
% 0.36/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58         = (k2_relat_1 @ sk_C))),
% 0.36/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.58  thf('59', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('60', plain,
% 0.36/0.58      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.58         (k1_zfmisc_1 @ 
% 0.36/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.36/0.58        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.36/0.58      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.36/0.58  thf('61', plain,
% 0.36/0.58      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.36/0.58        | ~ (l1_struct_0 @ sk_B)
% 0.36/0.58        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.58           (k1_zfmisc_1 @ 
% 0.36/0.58            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['52', '60'])).
% 0.36/0.58  thf('62', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('63', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('64', plain,
% 0.36/0.58      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.36/0.58        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.58           (k1_zfmisc_1 @ 
% 0.36/0.58            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.58      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.36/0.58  thf('65', plain,
% 0.36/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('simplify', [status(thm)], ['64'])).
% 0.36/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.58    (![A:$i,B:$i,C:$i]:
% 0.36/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.58  thf('66', plain,
% 0.36/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.58         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.36/0.58          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.36/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.58  thf('67', plain,
% 0.36/0.58      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['65', '66'])).
% 0.36/0.58  thf('68', plain,
% 0.36/0.58      (![X18 : $i]:
% 0.36/0.58         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.58  thf('69', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('70', plain,
% 0.36/0.58      (((m1_subset_1 @ sk_C @ 
% 0.36/0.58         (k1_zfmisc_1 @ 
% 0.36/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.36/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['68', '69'])).
% 0.36/0.58  thf('71', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('72', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.36/0.58      inference('demod', [status(thm)], ['70', '71'])).
% 0.36/0.58  thf('73', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('74', plain,
% 0.36/0.58      ((m1_subset_1 @ sk_C @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.36/0.58      inference('demod', [status(thm)], ['72', '73'])).
% 0.36/0.58  thf('75', plain,
% 0.36/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.58         (((k2_relset_1 @ X21 @ X20 @ X22) != (X20))
% 0.36/0.58          | ~ (v2_funct_1 @ X22)
% 0.36/0.58          | ((k2_tops_2 @ X21 @ X20 @ X22) = (k2_funct_1 @ X22))
% 0.36/0.58          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20)))
% 0.36/0.58          | ~ (v1_funct_2 @ X22 @ X21 @ X20)
% 0.36/0.58          | ~ (v1_funct_1 @ X22))),
% 0.36/0.58      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.36/0.58  thf('76', plain,
% 0.36/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.36/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.36/0.58        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.58            = (k2_funct_1 @ sk_C))
% 0.36/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.58        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.58            != (k2_relat_1 @ sk_C)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['74', '75'])).
% 0.36/0.58  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('78', plain,
% 0.36/0.58      (![X18 : $i]:
% 0.36/0.58         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.58  thf('79', plain,
% 0.36/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('80', plain,
% 0.36/0.58      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.36/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['78', '79'])).
% 0.36/0.58  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('82', plain,
% 0.36/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('demod', [status(thm)], ['80', '81'])).
% 0.36/0.58  thf('83', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('84', plain,
% 0.36/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.36/0.58      inference('demod', [status(thm)], ['82', '83'])).
% 0.36/0.58  thf('85', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('86', plain,
% 0.36/0.58      (![X18 : $i]:
% 0.36/0.58         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.58  thf('87', plain,
% 0.36/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58         = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('88', plain,
% 0.36/0.58      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58          = (k2_struct_0 @ sk_B))
% 0.36/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['86', '87'])).
% 0.36/0.58  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('90', plain,
% 0.36/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.36/0.58         = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('demod', [status(thm)], ['88', '89'])).
% 0.36/0.58  thf('91', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('92', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('93', plain,
% 0.36/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.58         = (k2_relat_1 @ sk_C))),
% 0.36/0.58      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.36/0.58  thf('94', plain,
% 0.36/0.58      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.58          = (k2_funct_1 @ sk_C))
% 0.36/0.58        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.36/0.58      inference('demod', [status(thm)], ['76', '77', '84', '85', '93'])).
% 0.36/0.58  thf('95', plain,
% 0.36/0.58      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.36/0.58         = (k2_funct_1 @ sk_C))),
% 0.36/0.58      inference('simplify', [status(thm)], ['94'])).
% 0.36/0.58  thf('96', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('97', plain,
% 0.36/0.58      (![X18 : $i]:
% 0.36/0.58         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.36/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.58  thf('98', plain,
% 0.36/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58          != (k2_struct_0 @ sk_B)))
% 0.36/0.58         <= (~
% 0.36/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58                = (k2_struct_0 @ sk_B))))),
% 0.36/0.58      inference('split', [status(esa)], ['34'])).
% 0.36/0.58  thf('99', plain,
% 0.36/0.58      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58           != (k2_struct_0 @ sk_B))
% 0.36/0.58         | ~ (l1_struct_0 @ sk_B)))
% 0.36/0.58         <= (~
% 0.36/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58                = (k2_struct_0 @ sk_B))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['97', '98'])).
% 0.36/0.58  thf('100', plain, ((l1_struct_0 @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('101', plain,
% 0.36/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58          != (k2_struct_0 @ sk_B)))
% 0.36/0.58         <= (~
% 0.36/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58                = (k2_struct_0 @ sk_B))))),
% 0.36/0.58      inference('demod', [status(thm)], ['99', '100'])).
% 0.36/0.58  thf('102', plain,
% 0.36/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.36/0.58          != (k2_struct_0 @ sk_B)))
% 0.36/0.58         <= (~
% 0.36/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58                = (k2_struct_0 @ sk_B))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['96', '101'])).
% 0.36/0.58  thf('103', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '3'])).
% 0.36/0.58  thf('104', plain,
% 0.36/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.36/0.58          != (k2_relat_1 @ sk_C)))
% 0.36/0.58         <= (~
% 0.36/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58                = (k2_struct_0 @ sk_B))))),
% 0.36/0.58      inference('demod', [status(thm)], ['102', '103'])).
% 0.36/0.58  thf('105', plain,
% 0.36/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.36/0.58         <= (~
% 0.36/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58                = (k2_struct_0 @ sk_B))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['95', '104'])).
% 0.36/0.58  thf('106', plain,
% 0.36/0.58      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.36/0.58         <= (~
% 0.36/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58                = (k2_struct_0 @ sk_B))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['67', '105'])).
% 0.36/0.58  thf('107', plain,
% 0.36/0.58      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.36/0.58         | ~ (v1_relat_1 @ sk_C)
% 0.36/0.58         | ~ (v1_funct_1 @ sk_C)
% 0.36/0.58         | ~ (v2_funct_1 @ sk_C)))
% 0.36/0.58         <= (~
% 0.36/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58                = (k2_struct_0 @ sk_B))))),
% 0.36/0.58      inference('sup-', [status(thm)], ['51', '106'])).
% 0.36/0.58  thf('108', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.58  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('110', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('111', plain,
% 0.36/0.58      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.36/0.58         <= (~
% 0.36/0.58             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58                = (k2_struct_0 @ sk_B))))),
% 0.36/0.58      inference('demod', [status(thm)], ['107', '108', '109', '110'])).
% 0.36/0.58  thf('112', plain,
% 0.36/0.58      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58          = (k2_struct_0 @ sk_B)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['111'])).
% 0.36/0.58  thf('113', plain,
% 0.36/0.58      (~
% 0.36/0.58       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58          = (k2_struct_0 @ sk_A))) | 
% 0.36/0.58       ~
% 0.36/0.58       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58          = (k2_struct_0 @ sk_B)))),
% 0.36/0.58      inference('split', [status(esa)], ['34'])).
% 0.36/0.58  thf('114', plain,
% 0.36/0.58      (~
% 0.36/0.58       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.36/0.58          = (k2_struct_0 @ sk_A)))),
% 0.36/0.58      inference('sat_resolution*', [status(thm)], ['112', '113'])).
% 0.36/0.58  thf('115', plain,
% 0.36/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58         (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.36/0.58      inference('simpl_trail', [status(thm)], ['50', '114'])).
% 0.36/0.58  thf('116', plain,
% 0.36/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.58        (k1_zfmisc_1 @ 
% 0.36/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.36/0.58      inference('simplify', [status(thm)], ['64'])).
% 0.36/0.58  thf('117', plain,
% 0.36/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.36/0.58         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.36/0.58          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.36/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.58  thf('118', plain,
% 0.36/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.58         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['116', '117'])).
% 0.36/0.58  thf('119', plain,
% 0.36/0.58      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))),
% 0.36/0.58      inference('demod', [status(thm)], ['115', '118'])).
% 0.36/0.58  thf('120', plain,
% 0.36/0.58      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.36/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.58      inference('sup-', [status(thm)], ['33', '119'])).
% 0.36/0.58  thf('121', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.58  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('123', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('124', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.36/0.58      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 0.36/0.58  thf('125', plain,
% 0.36/0.58      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.36/0.58        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.36/0.58      inference('sup-', [status(thm)], ['32', '124'])).
% 0.36/0.58  thf('126', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.36/0.58      inference('simplify', [status(thm)], ['125'])).
% 0.36/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.58  thf('127', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.58  thf('128', plain, ($false),
% 0.36/0.58      inference('demod', [status(thm)], ['13', '126', '127'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
