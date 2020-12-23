%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UD6x2cFksr

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:04 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 170 expanded)
%              Number of leaves         :   32 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  942 (2881 expanded)
%              Number of equality atoms :   43 ( 108 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k10_relat_1 @ X13 @ X14 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X13 ) @ X14 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(t137_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k10_relat_1 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X10 @ X11 ) @ ( k10_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k10_relat_1 @ X13 @ X14 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X13 ) @ X14 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k10_relat_1 @ X13 @ X14 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X13 ) @ X14 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(t122_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ! [B: $i,C: $i] :
            ( ( k9_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) )
            = ( k3_xboole_0 @ ( k9_relat_1 @ A @ B ) @ ( k9_relat_1 @ A @ C ) ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( ( k9_relat_1 @ X9 @ ( k3_xboole_0 @ ( sk_B @ X9 ) @ ( sk_C @ X9 ) ) )
       != ( k3_xboole_0 @ ( k9_relat_1 @ X9 @ ( sk_B @ X9 ) ) @ ( k9_relat_1 @ X9 @ ( sk_C @ X9 ) ) ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t122_funct_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k3_xboole_0 @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) )
       != ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k3_xboole_0 @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) )
       != ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) @ ( k10_relat_1 @ X0 @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k3_xboole_0 @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) )
       != ( k3_xboole_0 @ ( k10_relat_1 @ X0 @ ( sk_B @ ( k2_funct_1 @ X0 ) ) ) @ ( k10_relat_1 @ X0 @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k3_xboole_0 @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) )
       != ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k3_xboole_0 @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) )
       != ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) )
       != ( k10_relat_1 @ X0 @ ( k3_xboole_0 @ ( sk_B @ ( k2_funct_1 @ X0 ) ) @ ( sk_C @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('18',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
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

thf('19',plain,(
    ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('25',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

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

thf('37',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('45',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('54',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['37','38','45','46','54'])).

thf('56',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['28','56'])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('60',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('62',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('63',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['58','63','64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UD6x2cFksr
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.05/1.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.29  % Solved by: fo/fo7.sh
% 1.05/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.29  % done 283 iterations in 0.835s
% 1.05/1.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.29  % SZS output start Refutation
% 1.05/1.29  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.05/1.29  thf(sk_C_type, type, sk_C: $i > $i).
% 1.05/1.29  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.05/1.29  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.05/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.29  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.05/1.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.05/1.29  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.05/1.29  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.05/1.29  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.05/1.29  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.05/1.29  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.05/1.29  thf(sk_B_type, type, sk_B: $i > $i).
% 1.05/1.29  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.05/1.29  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.05/1.29  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.05/1.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.05/1.29  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.05/1.29  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.05/1.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.05/1.29  thf(dt_k2_funct_1, axiom,
% 1.05/1.29    (![A:$i]:
% 1.05/1.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.05/1.29       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.05/1.29         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.05/1.29  thf('0', plain,
% 1.05/1.29      (![X8 : $i]:
% 1.05/1.29         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 1.05/1.29          | ~ (v1_funct_1 @ X8)
% 1.05/1.29          | ~ (v1_relat_1 @ X8))),
% 1.05/1.29      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.05/1.29  thf('1', plain,
% 1.05/1.29      (![X8 : $i]:
% 1.05/1.29         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 1.05/1.29          | ~ (v1_funct_1 @ X8)
% 1.05/1.29          | ~ (v1_relat_1 @ X8))),
% 1.05/1.29      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.05/1.29  thf(t155_funct_1, axiom,
% 1.05/1.29    (![A:$i,B:$i]:
% 1.05/1.29     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.05/1.29       ( ( v2_funct_1 @ B ) =>
% 1.05/1.29         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 1.05/1.29  thf('2', plain,
% 1.05/1.29      (![X13 : $i, X14 : $i]:
% 1.05/1.29         (~ (v2_funct_1 @ X13)
% 1.05/1.29          | ((k10_relat_1 @ X13 @ X14)
% 1.05/1.29              = (k9_relat_1 @ (k2_funct_1 @ X13) @ X14))
% 1.05/1.29          | ~ (v1_funct_1 @ X13)
% 1.05/1.29          | ~ (v1_relat_1 @ X13))),
% 1.05/1.29      inference('cnf', [status(esa)], [t155_funct_1])).
% 1.05/1.29  thf(t137_funct_1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.05/1.29       ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 1.05/1.29         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 1.05/1.29  thf('3', plain,
% 1.05/1.29      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.05/1.29         (((k10_relat_1 @ X10 @ (k3_xboole_0 @ X11 @ X12))
% 1.05/1.29            = (k3_xboole_0 @ (k10_relat_1 @ X10 @ X11) @ 
% 1.05/1.29               (k10_relat_1 @ X10 @ X12)))
% 1.05/1.29          | ~ (v1_funct_1 @ X10)
% 1.05/1.29          | ~ (v1_relat_1 @ X10))),
% 1.05/1.29      inference('cnf', [status(esa)], [t137_funct_1])).
% 1.05/1.29  thf('4', plain,
% 1.05/1.29      (![X13 : $i, X14 : $i]:
% 1.05/1.29         (~ (v2_funct_1 @ X13)
% 1.05/1.29          | ((k10_relat_1 @ X13 @ X14)
% 1.05/1.29              = (k9_relat_1 @ (k2_funct_1 @ X13) @ X14))
% 1.05/1.29          | ~ (v1_funct_1 @ X13)
% 1.05/1.29          | ~ (v1_relat_1 @ X13))),
% 1.05/1.29      inference('cnf', [status(esa)], [t155_funct_1])).
% 1.05/1.29  thf('5', plain,
% 1.05/1.29      (![X13 : $i, X14 : $i]:
% 1.05/1.29         (~ (v2_funct_1 @ X13)
% 1.05/1.29          | ((k10_relat_1 @ X13 @ X14)
% 1.05/1.29              = (k9_relat_1 @ (k2_funct_1 @ X13) @ X14))
% 1.05/1.29          | ~ (v1_funct_1 @ X13)
% 1.05/1.29          | ~ (v1_relat_1 @ X13))),
% 1.05/1.29      inference('cnf', [status(esa)], [t155_funct_1])).
% 1.05/1.29  thf(t122_funct_1, axiom,
% 1.05/1.29    (![A:$i]:
% 1.05/1.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.05/1.29       ( ( ![B:$i,C:$i]:
% 1.05/1.29           ( ( k9_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 1.05/1.29             ( k3_xboole_0 @ ( k9_relat_1 @ A @ B ) @ ( k9_relat_1 @ A @ C ) ) ) ) =>
% 1.05/1.29         ( v2_funct_1 @ A ) ) ))).
% 1.05/1.29  thf('6', plain,
% 1.05/1.29      (![X9 : $i]:
% 1.05/1.29         (((k9_relat_1 @ X9 @ (k3_xboole_0 @ (sk_B @ X9) @ (sk_C @ X9)))
% 1.05/1.29            != (k3_xboole_0 @ (k9_relat_1 @ X9 @ (sk_B @ X9)) @ 
% 1.05/1.29                (k9_relat_1 @ X9 @ (sk_C @ X9))))
% 1.05/1.29          | (v2_funct_1 @ X9)
% 1.05/1.29          | ~ (v1_funct_1 @ X9)
% 1.05/1.29          | ~ (v1_relat_1 @ X9))),
% 1.05/1.29      inference('cnf', [status(esa)], [t122_funct_1])).
% 1.05/1.29  thf('7', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.05/1.29            (k3_xboole_0 @ (sk_B @ (k2_funct_1 @ X0)) @ 
% 1.05/1.29             (sk_C @ (k2_funct_1 @ X0))))
% 1.05/1.29            != (k3_xboole_0 @ 
% 1.05/1.29                (k10_relat_1 @ X0 @ (sk_B @ (k2_funct_1 @ X0))) @ 
% 1.05/1.29                (k9_relat_1 @ (k2_funct_1 @ X0) @ (sk_C @ (k2_funct_1 @ X0)))))
% 1.05/1.29          | ~ (v1_relat_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v2_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['5', '6'])).
% 1.05/1.29  thf('8', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.05/1.29            (k3_xboole_0 @ (sk_B @ (k2_funct_1 @ X0)) @ 
% 1.05/1.29             (sk_C @ (k2_funct_1 @ X0))))
% 1.05/1.29            != (k3_xboole_0 @ 
% 1.05/1.29                (k10_relat_1 @ X0 @ (sk_B @ (k2_funct_1 @ X0))) @ 
% 1.05/1.29                (k10_relat_1 @ X0 @ (sk_C @ (k2_funct_1 @ X0)))))
% 1.05/1.29          | ~ (v1_relat_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v2_funct_1 @ X0)
% 1.05/1.29          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v2_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_relat_1 @ X0))),
% 1.05/1.29      inference('sup-', [status(thm)], ['4', '7'])).
% 1.05/1.29  thf('9', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v2_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_relat_1 @ X0)
% 1.05/1.29          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.05/1.29              (k3_xboole_0 @ (sk_B @ (k2_funct_1 @ X0)) @ 
% 1.05/1.29               (sk_C @ (k2_funct_1 @ X0))))
% 1.05/1.29              != (k3_xboole_0 @ 
% 1.05/1.29                  (k10_relat_1 @ X0 @ (sk_B @ (k2_funct_1 @ X0))) @ 
% 1.05/1.29                  (k10_relat_1 @ X0 @ (sk_C @ (k2_funct_1 @ X0))))))),
% 1.05/1.29      inference('simplify', [status(thm)], ['8'])).
% 1.05/1.29  thf('10', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.05/1.29            (k3_xboole_0 @ (sk_B @ (k2_funct_1 @ X0)) @ 
% 1.05/1.29             (sk_C @ (k2_funct_1 @ X0))))
% 1.05/1.29            != (k10_relat_1 @ X0 @ 
% 1.05/1.29                (k3_xboole_0 @ (sk_B @ (k2_funct_1 @ X0)) @ 
% 1.05/1.29                 (sk_C @ (k2_funct_1 @ X0)))))
% 1.05/1.29          | ~ (v1_relat_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_relat_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v2_funct_1 @ X0)
% 1.05/1.29          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['3', '9'])).
% 1.05/1.29  thf('11', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v2_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_relat_1 @ X0)
% 1.05/1.29          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.05/1.29              (k3_xboole_0 @ (sk_B @ (k2_funct_1 @ X0)) @ 
% 1.05/1.29               (sk_C @ (k2_funct_1 @ X0))))
% 1.05/1.29              != (k10_relat_1 @ X0 @ 
% 1.05/1.29                  (k3_xboole_0 @ (sk_B @ (k2_funct_1 @ X0)) @ 
% 1.05/1.29                   (sk_C @ (k2_funct_1 @ X0))))))),
% 1.05/1.29      inference('simplify', [status(thm)], ['10'])).
% 1.05/1.29  thf('12', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (((k10_relat_1 @ X0 @ 
% 1.05/1.29            (k3_xboole_0 @ (sk_B @ (k2_funct_1 @ X0)) @ 
% 1.05/1.29             (sk_C @ (k2_funct_1 @ X0))))
% 1.05/1.29            != (k10_relat_1 @ X0 @ 
% 1.05/1.29                (k3_xboole_0 @ (sk_B @ (k2_funct_1 @ X0)) @ 
% 1.05/1.29                 (sk_C @ (k2_funct_1 @ X0)))))
% 1.05/1.29          | ~ (v1_relat_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v2_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_relat_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v2_funct_1 @ X0)
% 1.05/1.29          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['2', '11'])).
% 1.05/1.29  thf('13', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v2_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_relat_1 @ X0))),
% 1.05/1.29      inference('simplify', [status(thm)], ['12'])).
% 1.05/1.29  thf('14', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (~ (v1_relat_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_relat_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v2_funct_1 @ X0)
% 1.05/1.29          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['1', '13'])).
% 1.05/1.29  thf('15', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v2_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_relat_1 @ X0))),
% 1.05/1.29      inference('simplify', [status(thm)], ['14'])).
% 1.05/1.29  thf('16', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (~ (v1_relat_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_relat_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v2_funct_1 @ X0)
% 1.05/1.29          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['0', '15'])).
% 1.05/1.29  thf('17', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 1.05/1.29          | ~ (v2_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_relat_1 @ X0))),
% 1.05/1.29      inference('simplify', [status(thm)], ['16'])).
% 1.05/1.29  thf(d3_struct_0, axiom,
% 1.05/1.29    (![A:$i]:
% 1.05/1.29     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.05/1.29  thf('18', plain,
% 1.05/1.29      (![X18 : $i]:
% 1.05/1.29         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 1.05/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.05/1.29  thf(t63_tops_2, conjecture,
% 1.05/1.29    (![A:$i]:
% 1.05/1.29     ( ( l1_struct_0 @ A ) =>
% 1.05/1.29       ( ![B:$i]:
% 1.05/1.29         ( ( l1_struct_0 @ B ) =>
% 1.05/1.29           ( ![C:$i]:
% 1.05/1.29             ( ( ( v1_funct_1 @ C ) & 
% 1.05/1.29                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.05/1.29                 ( m1_subset_1 @
% 1.05/1.29                   C @ 
% 1.05/1.29                   ( k1_zfmisc_1 @
% 1.05/1.29                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.05/1.29               ( ( ( ( k2_relset_1 @
% 1.05/1.29                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.05/1.29                     ( k2_struct_0 @ B ) ) & 
% 1.05/1.29                   ( v2_funct_1 @ C ) ) =>
% 1.05/1.29                 ( v2_funct_1 @
% 1.05/1.29                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 1.05/1.29  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.29    (~( ![A:$i]:
% 1.05/1.29        ( ( l1_struct_0 @ A ) =>
% 1.05/1.29          ( ![B:$i]:
% 1.05/1.29            ( ( l1_struct_0 @ B ) =>
% 1.05/1.29              ( ![C:$i]:
% 1.05/1.29                ( ( ( v1_funct_1 @ C ) & 
% 1.05/1.29                    ( v1_funct_2 @
% 1.05/1.29                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.05/1.29                    ( m1_subset_1 @
% 1.05/1.29                      C @ 
% 1.05/1.29                      ( k1_zfmisc_1 @
% 1.05/1.29                        ( k2_zfmisc_1 @
% 1.05/1.29                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.05/1.29                  ( ( ( ( k2_relset_1 @
% 1.05/1.29                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.05/1.29                        ( k2_struct_0 @ B ) ) & 
% 1.05/1.29                      ( v2_funct_1 @ C ) ) =>
% 1.05/1.29                    ( v2_funct_1 @
% 1.05/1.29                      ( k2_tops_2 @
% 1.05/1.29                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ) )),
% 1.05/1.29    inference('cnf.neg', [status(esa)], [t63_tops_2])).
% 1.05/1.29  thf('19', plain,
% 1.05/1.29      (~ (v2_funct_1 @ 
% 1.05/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('20', plain,
% 1.05/1.29      ((~ (v2_funct_1 @ 
% 1.05/1.29           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C_1))
% 1.05/1.29        | ~ (l1_struct_0 @ sk_B_1))),
% 1.05/1.29      inference('sup-', [status(thm)], ['18', '19'])).
% 1.05/1.29  thf('21', plain, ((l1_struct_0 @ sk_B_1)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('22', plain,
% 1.05/1.29      (~ (v2_funct_1 @ 
% 1.05/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C_1))),
% 1.05/1.29      inference('demod', [status(thm)], ['20', '21'])).
% 1.05/1.29  thf('23', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C_1 @ 
% 1.05/1.29        (k1_zfmisc_1 @ 
% 1.05/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(redefinition_k2_relset_1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.29       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.05/1.29  thf('24', plain,
% 1.05/1.29      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.05/1.29         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.05/1.29          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.05/1.29  thf('25', plain,
% 1.05/1.29      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.05/1.29         = (k2_relat_1 @ sk_C_1))),
% 1.05/1.29      inference('sup-', [status(thm)], ['23', '24'])).
% 1.05/1.29  thf('26', plain,
% 1.05/1.29      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.05/1.29         = (k2_struct_0 @ sk_B_1))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('27', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.05/1.29      inference('sup+', [status(thm)], ['25', '26'])).
% 1.05/1.29  thf('28', plain,
% 1.05/1.29      (~ (v2_funct_1 @ 
% 1.05/1.29          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ sk_C_1))),
% 1.05/1.29      inference('demod', [status(thm)], ['22', '27'])).
% 1.05/1.29  thf('29', plain,
% 1.05/1.29      (![X18 : $i]:
% 1.05/1.29         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 1.05/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.05/1.29  thf('30', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C_1 @ 
% 1.05/1.29        (k1_zfmisc_1 @ 
% 1.05/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('31', plain,
% 1.05/1.29      (((m1_subset_1 @ sk_C_1 @ 
% 1.05/1.29         (k1_zfmisc_1 @ 
% 1.05/1.29          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))
% 1.05/1.29        | ~ (l1_struct_0 @ sk_B_1))),
% 1.05/1.29      inference('sup+', [status(thm)], ['29', '30'])).
% 1.05/1.29  thf('32', plain, ((l1_struct_0 @ sk_B_1)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('33', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C_1 @ 
% 1.05/1.29        (k1_zfmisc_1 @ 
% 1.05/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 1.05/1.29      inference('demod', [status(thm)], ['31', '32'])).
% 1.05/1.29  thf('34', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.05/1.29      inference('sup+', [status(thm)], ['25', '26'])).
% 1.05/1.29  thf('35', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C_1 @ 
% 1.05/1.29        (k1_zfmisc_1 @ 
% 1.05/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))))),
% 1.05/1.29      inference('demod', [status(thm)], ['33', '34'])).
% 1.05/1.29  thf(d4_tops_2, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.29       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.05/1.29         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.05/1.29  thf('36', plain,
% 1.05/1.29      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.05/1.29         (((k2_relset_1 @ X20 @ X19 @ X21) != (X19))
% 1.05/1.29          | ~ (v2_funct_1 @ X21)
% 1.05/1.29          | ((k2_tops_2 @ X20 @ X19 @ X21) = (k2_funct_1 @ X21))
% 1.05/1.29          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 1.05/1.29          | ~ (v1_funct_2 @ X21 @ X20 @ X19)
% 1.05/1.29          | ~ (v1_funct_1 @ X21))),
% 1.05/1.29      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.05/1.29  thf('37', plain,
% 1.05/1.29      ((~ (v1_funct_1 @ sk_C_1)
% 1.05/1.29        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))
% 1.05/1.29        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 1.05/1.29            = (k2_funct_1 @ sk_C_1))
% 1.05/1.29        | ~ (v2_funct_1 @ sk_C_1)
% 1.05/1.29        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 1.05/1.29            != (k2_relat_1 @ sk_C_1)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['35', '36'])).
% 1.05/1.29  thf('38', plain, ((v1_funct_1 @ sk_C_1)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('39', plain,
% 1.05/1.29      (![X18 : $i]:
% 1.05/1.29         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 1.05/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.05/1.29  thf('40', plain,
% 1.05/1.29      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('41', plain,
% 1.05/1.29      (((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))
% 1.05/1.29        | ~ (l1_struct_0 @ sk_B_1))),
% 1.05/1.29      inference('sup+', [status(thm)], ['39', '40'])).
% 1.05/1.29  thf('42', plain, ((l1_struct_0 @ sk_B_1)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('43', plain,
% 1.05/1.29      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))),
% 1.05/1.29      inference('demod', [status(thm)], ['41', '42'])).
% 1.05/1.29  thf('44', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.05/1.29      inference('sup+', [status(thm)], ['25', '26'])).
% 1.05/1.29  thf('45', plain,
% 1.05/1.29      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))),
% 1.05/1.29      inference('demod', [status(thm)], ['43', '44'])).
% 1.05/1.29  thf('46', plain, ((v2_funct_1 @ sk_C_1)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('47', plain,
% 1.05/1.29      (![X18 : $i]:
% 1.05/1.29         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 1.05/1.29      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.05/1.29  thf('48', plain,
% 1.05/1.29      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 1.05/1.29         = (k2_struct_0 @ sk_B_1))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('49', plain,
% 1.05/1.29      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C_1)
% 1.05/1.29          = (k2_struct_0 @ sk_B_1))
% 1.05/1.29        | ~ (l1_struct_0 @ sk_B_1))),
% 1.05/1.29      inference('sup+', [status(thm)], ['47', '48'])).
% 1.05/1.29  thf('50', plain, ((l1_struct_0 @ sk_B_1)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('51', plain,
% 1.05/1.29      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C_1)
% 1.05/1.29         = (k2_struct_0 @ sk_B_1))),
% 1.05/1.29      inference('demod', [status(thm)], ['49', '50'])).
% 1.05/1.29  thf('52', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.05/1.29      inference('sup+', [status(thm)], ['25', '26'])).
% 1.05/1.29  thf('53', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 1.05/1.29      inference('sup+', [status(thm)], ['25', '26'])).
% 1.05/1.29  thf('54', plain,
% 1.05/1.29      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 1.05/1.29         = (k2_relat_1 @ sk_C_1))),
% 1.05/1.29      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.05/1.29  thf('55', plain,
% 1.05/1.29      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 1.05/1.29          = (k2_funct_1 @ sk_C_1))
% 1.05/1.29        | ((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1)))),
% 1.05/1.29      inference('demod', [status(thm)], ['37', '38', '45', '46', '54'])).
% 1.05/1.29  thf('56', plain,
% 1.05/1.29      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 1.05/1.29         = (k2_funct_1 @ sk_C_1))),
% 1.05/1.29      inference('simplify', [status(thm)], ['55'])).
% 1.05/1.29  thf('57', plain, (~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 1.05/1.29      inference('demod', [status(thm)], ['28', '56'])).
% 1.05/1.29  thf('58', plain,
% 1.05/1.29      ((~ (v1_relat_1 @ sk_C_1)
% 1.05/1.29        | ~ (v1_funct_1 @ sk_C_1)
% 1.05/1.29        | ~ (v2_funct_1 @ sk_C_1))),
% 1.05/1.29      inference('sup-', [status(thm)], ['17', '57'])).
% 1.05/1.29  thf('59', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C_1 @ 
% 1.05/1.29        (k1_zfmisc_1 @ 
% 1.05/1.29         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(cc2_relat_1, axiom,
% 1.05/1.29    (![A:$i]:
% 1.05/1.29     ( ( v1_relat_1 @ A ) =>
% 1.05/1.29       ( ![B:$i]:
% 1.05/1.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.05/1.29  thf('60', plain,
% 1.05/1.29      (![X4 : $i, X5 : $i]:
% 1.05/1.29         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 1.05/1.29          | (v1_relat_1 @ X4)
% 1.05/1.29          | ~ (v1_relat_1 @ X5))),
% 1.05/1.29      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.05/1.29  thf('61', plain,
% 1.05/1.29      ((~ (v1_relat_1 @ 
% 1.05/1.29           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))
% 1.05/1.29        | (v1_relat_1 @ sk_C_1))),
% 1.05/1.29      inference('sup-', [status(thm)], ['59', '60'])).
% 1.05/1.29  thf(fc6_relat_1, axiom,
% 1.05/1.29    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.05/1.29  thf('62', plain,
% 1.05/1.29      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 1.05/1.29      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.05/1.29  thf('63', plain, ((v1_relat_1 @ sk_C_1)),
% 1.05/1.29      inference('demod', [status(thm)], ['61', '62'])).
% 1.05/1.29  thf('64', plain, ((v1_funct_1 @ sk_C_1)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('65', plain, ((v2_funct_1 @ sk_C_1)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('66', plain, ($false),
% 1.05/1.29      inference('demod', [status(thm)], ['58', '63', '64', '65'])).
% 1.05/1.29  
% 1.05/1.29  % SZS output end Refutation
% 1.05/1.29  
% 1.05/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
