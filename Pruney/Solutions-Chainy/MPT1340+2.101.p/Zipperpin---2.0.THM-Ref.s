%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jLjDbsrGns

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:25 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  264 (1250 expanded)
%              Number of leaves         :   37 ( 379 expanded)
%              Depth                    :   21
%              Number of atoms          : 2552 (30559 expanded)
%              Number of equality atoms :  138 ( 971 expanded)
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

thf('18',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

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

thf('25',plain,(
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

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('43',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27','34','35','43'])).

thf('45',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['17','45'])).

thf('47',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('51',plain,(
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

thf('52',plain,(
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

thf('53',plain,
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
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['53','54','55','56','57','58','59','60'])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
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

thf('66',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('71',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('74',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,(
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

thf('82',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('87',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('89',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['80','88'])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('91',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('95',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['79','95'])).

thf('97',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['50','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('100',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('101',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','102','103','104'])).

thf('106',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['49','105'])).

thf('107',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('108',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['107','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('119',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['121','126'])).

thf('128',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('131',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('133',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('134',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['132','137'])).

thf('139',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('143',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['119','120','131','143','144'])).

thf('146',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
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

thf('148',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('150',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('151',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('154',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('155',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['151','152','153','154','155'])).

thf('157',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('159',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X18 ) @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('160',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('163',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('164',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['160','161','162','163','164'])).

thf('166',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('168',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['156'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('169',plain,(
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

thf('170',plain,(
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

thf('171',plain,(
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
    inference('sup-',[status(thm)],['169','170'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('172',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('173',plain,(
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
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['168','174'])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('177',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['175','176','177','178'])).

thf('180',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('181',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relset_1 @ X20 @ X19 @ X18 )
       != X19 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X18 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('182',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('185',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('186',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['182','183','184','185','186'])).

thf('188',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('190',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('192',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['179','192'])).

thf('194',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['167','193'])).

thf('195',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('196',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['194','195','196','197'])).

thf('199',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('201',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('202',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','157','166','199','202'])).

thf('204',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['79','95'])).

thf('205',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','102','103','104'])).

thf('208',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['106','208'])).

thf('210',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','209'])).

thf('211',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('213',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_funct_2 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['214','215','216'])).

thf('218',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['211','217'])).

thf('219',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['218','219','220'])).

thf('222',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('223',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    $false ),
    inference(demod,[status(thm)],['210','221','222','223','224'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jLjDbsrGns
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:21:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.59/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.76  % Solved by: fo/fo7.sh
% 0.59/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.76  % done 563 iterations in 0.290s
% 0.59/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.76  % SZS output start Refutation
% 0.59/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.76  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.59/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.76  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.59/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.76  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.59/0.76  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.59/0.76  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.59/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.76  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.59/0.76  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.59/0.76  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.76  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.59/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.76  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.59/0.76  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.59/0.76  thf(t65_funct_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.76       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.59/0.76  thf('0', plain,
% 0.59/0.76      (![X10 : $i]:
% 0.59/0.76         (~ (v2_funct_1 @ X10)
% 0.59/0.76          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.59/0.76          | ~ (v1_funct_1 @ X10)
% 0.59/0.76          | ~ (v1_relat_1 @ X10))),
% 0.59/0.76      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.59/0.76  thf(d3_struct_0, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.59/0.76  thf('1', plain,
% 0.59/0.76      (![X21 : $i]:
% 0.59/0.76         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.76  thf('2', plain,
% 0.59/0.76      (![X21 : $i]:
% 0.59/0.76         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.76  thf('3', plain,
% 0.59/0.76      (![X21 : $i]:
% 0.59/0.76         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.76  thf(t64_tops_2, conjecture,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( l1_struct_0 @ A ) =>
% 0.59/0.76       ( ![B:$i]:
% 0.59/0.76         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.59/0.76           ( ![C:$i]:
% 0.59/0.76             ( ( ( v1_funct_1 @ C ) & 
% 0.59/0.76                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.76                 ( m1_subset_1 @
% 0.59/0.76                   C @ 
% 0.59/0.76                   ( k1_zfmisc_1 @
% 0.59/0.76                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.76               ( ( ( ( k2_relset_1 @
% 0.59/0.76                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.59/0.76                     ( k2_struct_0 @ B ) ) & 
% 0.59/0.76                   ( v2_funct_1 @ C ) ) =>
% 0.59/0.76                 ( r2_funct_2 @
% 0.59/0.76                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.59/0.76                   ( k2_tops_2 @
% 0.59/0.76                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.59/0.76                     ( k2_tops_2 @
% 0.59/0.76                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.59/0.76                   C ) ) ) ) ) ) ))).
% 0.59/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.76    (~( ![A:$i]:
% 0.59/0.76        ( ( l1_struct_0 @ A ) =>
% 0.59/0.76          ( ![B:$i]:
% 0.59/0.76            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.59/0.76              ( ![C:$i]:
% 0.59/0.76                ( ( ( v1_funct_1 @ C ) & 
% 0.59/0.76                    ( v1_funct_2 @
% 0.59/0.76                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.76                    ( m1_subset_1 @
% 0.59/0.76                      C @ 
% 0.59/0.76                      ( k1_zfmisc_1 @
% 0.59/0.76                        ( k2_zfmisc_1 @
% 0.59/0.76                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.76                  ( ( ( ( k2_relset_1 @
% 0.59/0.76                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.59/0.76                        ( k2_struct_0 @ B ) ) & 
% 0.59/0.76                      ( v2_funct_1 @ C ) ) =>
% 0.59/0.76                    ( r2_funct_2 @
% 0.59/0.76                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.59/0.76                      ( k2_tops_2 @
% 0.59/0.76                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.59/0.76                        ( k2_tops_2 @
% 0.59/0.76                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.59/0.76                      C ) ) ) ) ) ) ) )),
% 0.59/0.76    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.59/0.76  thf('4', plain,
% 0.59/0.76      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.76          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.76           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.59/0.76          sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('5', plain,
% 0.59/0.76      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.76           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.76            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.59/0.76           sk_C)
% 0.59/0.76        | ~ (l1_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.76  thf('6', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('7', plain,
% 0.59/0.76      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.76          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.76           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.59/0.76          sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['5', '6'])).
% 0.59/0.76  thf('8', plain,
% 0.59/0.76      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.76           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.76            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.59/0.76           sk_C)
% 0.59/0.76        | ~ (l1_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup-', [status(thm)], ['2', '7'])).
% 0.59/0.76  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('10', plain,
% 0.59/0.76      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.76          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.76           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.59/0.76          sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['8', '9'])).
% 0.59/0.76  thf('11', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(redefinition_k2_relset_1, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i]:
% 0.59/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.76       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.59/0.76  thf('12', plain,
% 0.59/0.76      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.59/0.76         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.59/0.76          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.59/0.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.59/0.76  thf('13', plain,
% 0.59/0.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76         = (k2_relat_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.76  thf('14', plain,
% 0.59/0.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76         = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('15', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.76  thf('16', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.76  thf('17', plain,
% 0.59/0.76      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.76          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.76           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.59/0.76          sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['10', '15', '16'])).
% 0.59/0.76  thf('18', plain,
% 0.59/0.76      (![X21 : $i]:
% 0.59/0.76         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.76  thf('19', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('20', plain,
% 0.59/0.76      (((m1_subset_1 @ sk_C @ 
% 0.59/0.76         (k1_zfmisc_1 @ 
% 0.59/0.76          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.59/0.76        | ~ (l1_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['18', '19'])).
% 0.59/0.76  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('22', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.59/0.76      inference('demod', [status(thm)], ['20', '21'])).
% 0.59/0.76  thf('23', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.76  thf('24', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.59/0.76      inference('demod', [status(thm)], ['22', '23'])).
% 0.59/0.76  thf(d4_tops_2, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i]:
% 0.59/0.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.76       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.59/0.76         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.59/0.76  thf('25', plain,
% 0.59/0.76      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.76         (((k2_relset_1 @ X23 @ X22 @ X24) != (X22))
% 0.59/0.76          | ~ (v2_funct_1 @ X24)
% 0.59/0.76          | ((k2_tops_2 @ X23 @ X22 @ X24) = (k2_funct_1 @ X24))
% 0.59/0.76          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.59/0.76          | ~ (v1_funct_2 @ X24 @ X23 @ X22)
% 0.59/0.76          | ~ (v1_funct_1 @ X24))),
% 0.59/0.76      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.59/0.76  thf('26', plain,
% 0.59/0.76      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.59/0.76        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.76            = (k2_funct_1 @ sk_C))
% 0.59/0.76        | ~ (v2_funct_1 @ sk_C)
% 0.59/0.76        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.76            != (k2_relat_1 @ sk_C)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['24', '25'])).
% 0.59/0.76  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('28', plain,
% 0.59/0.76      (![X21 : $i]:
% 0.59/0.76         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.76  thf('29', plain,
% 0.59/0.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('30', plain,
% 0.59/0.76      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.59/0.76        | ~ (l1_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['28', '29'])).
% 0.59/0.76  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('32', plain,
% 0.59/0.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('demod', [status(thm)], ['30', '31'])).
% 0.59/0.76  thf('33', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.76  thf('34', plain,
% 0.59/0.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['32', '33'])).
% 0.59/0.76  thf('35', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('36', plain,
% 0.59/0.76      (![X21 : $i]:
% 0.59/0.76         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.76  thf('37', plain,
% 0.59/0.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76         = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('38', plain,
% 0.59/0.76      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76          = (k2_struct_0 @ sk_B))
% 0.59/0.76        | ~ (l1_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['36', '37'])).
% 0.59/0.76  thf('39', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('40', plain,
% 0.59/0.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76         = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('demod', [status(thm)], ['38', '39'])).
% 0.59/0.76  thf('41', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.76  thf('42', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.76  thf('43', plain,
% 0.59/0.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.76         = (k2_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.59/0.76  thf('44', plain,
% 0.59/0.76      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.76          = (k2_funct_1 @ sk_C))
% 0.59/0.76        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.59/0.76      inference('demod', [status(thm)], ['26', '27', '34', '35', '43'])).
% 0.59/0.76  thf('45', plain,
% 0.59/0.76      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.76         = (k2_funct_1 @ sk_C))),
% 0.59/0.76      inference('simplify', [status(thm)], ['44'])).
% 0.59/0.76  thf('46', plain,
% 0.59/0.76      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.76          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.76           (k2_funct_1 @ sk_C)) @ 
% 0.59/0.76          sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['17', '45'])).
% 0.59/0.76  thf('47', plain,
% 0.59/0.76      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.76           (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.76            (k2_funct_1 @ sk_C)) @ 
% 0.59/0.76           sk_C)
% 0.59/0.76        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.76      inference('sup-', [status(thm)], ['1', '46'])).
% 0.59/0.76  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('49', plain,
% 0.59/0.76      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.76          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.76           (k2_funct_1 @ sk_C)) @ 
% 0.59/0.76          sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['47', '48'])).
% 0.59/0.76  thf(t55_funct_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.76       ( ( v2_funct_1 @ A ) =>
% 0.59/0.76         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.59/0.76           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.59/0.76  thf('50', plain,
% 0.59/0.76      (![X8 : $i]:
% 0.59/0.76         (~ (v2_funct_1 @ X8)
% 0.59/0.76          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.59/0.76          | ~ (v1_funct_1 @ X8)
% 0.59/0.76          | ~ (v1_relat_1 @ X8))),
% 0.59/0.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.59/0.76  thf('51', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(t62_tops_2, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( l1_struct_0 @ A ) =>
% 0.59/0.76       ( ![B:$i]:
% 0.59/0.76         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.59/0.76           ( ![C:$i]:
% 0.59/0.76             ( ( ( v1_funct_1 @ C ) & 
% 0.59/0.76                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.76                 ( m1_subset_1 @
% 0.59/0.76                   C @ 
% 0.59/0.76                   ( k1_zfmisc_1 @
% 0.59/0.76                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.76               ( ( ( ( k2_relset_1 @
% 0.59/0.76                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.59/0.76                     ( k2_struct_0 @ B ) ) & 
% 0.59/0.76                   ( v2_funct_1 @ C ) ) =>
% 0.59/0.76                 ( ( ( k1_relset_1 @
% 0.59/0.76                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.59/0.76                       ( k2_tops_2 @
% 0.59/0.76                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.59/0.76                     ( k2_struct_0 @ B ) ) & 
% 0.59/0.76                   ( ( k2_relset_1 @
% 0.59/0.76                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.59/0.76                       ( k2_tops_2 @
% 0.59/0.76                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.59/0.76                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.59/0.76  thf('52', plain,
% 0.59/0.76      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.59/0.76         ((v2_struct_0 @ X25)
% 0.59/0.76          | ~ (l1_struct_0 @ X25)
% 0.59/0.76          | ((k2_relset_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25) @ X27)
% 0.59/0.76              != (k2_struct_0 @ X25))
% 0.59/0.76          | ~ (v2_funct_1 @ X27)
% 0.59/0.76          | ((k2_relset_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26) @ 
% 0.59/0.76              (k2_tops_2 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25) @ X27))
% 0.59/0.76              = (k2_struct_0 @ X26))
% 0.59/0.76          | ~ (m1_subset_1 @ X27 @ 
% 0.59/0.76               (k1_zfmisc_1 @ 
% 0.59/0.76                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.59/0.76          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.59/0.76          | ~ (v1_funct_1 @ X27)
% 0.59/0.76          | ~ (l1_struct_0 @ X26))),
% 0.59/0.76      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.59/0.76  thf('53', plain,
% 0.59/0.76      ((~ (l1_struct_0 @ sk_A)
% 0.59/0.76        | ~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.59/0.76        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.76            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.76            = (k2_struct_0 @ sk_A))
% 0.59/0.76        | ~ (v2_funct_1 @ sk_C)
% 0.59/0.76        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76            != (k2_struct_0 @ sk_B))
% 0.59/0.76        | ~ (l1_struct_0 @ sk_B)
% 0.59/0.76        | (v2_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup-', [status(thm)], ['51', '52'])).
% 0.59/0.76  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('56', plain,
% 0.59/0.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('57', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('58', plain,
% 0.59/0.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76         = (k2_relat_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.76  thf('59', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.76  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('61', plain,
% 0.59/0.76      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.76          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.76          = (k2_struct_0 @ sk_A))
% 0.59/0.76        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.59/0.76        | (v2_struct_0 @ sk_B))),
% 0.59/0.76      inference('demod', [status(thm)],
% 0.59/0.76                ['53', '54', '55', '56', '57', '58', '59', '60'])).
% 0.59/0.76  thf('62', plain,
% 0.59/0.76      (((v2_struct_0 @ sk_B)
% 0.59/0.76        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.76            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.76            = (k2_struct_0 @ sk_A)))),
% 0.59/0.76      inference('simplify', [status(thm)], ['61'])).
% 0.59/0.76  thf('63', plain,
% 0.59/0.76      (![X21 : $i]:
% 0.59/0.76         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.76  thf('64', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('65', plain,
% 0.59/0.76      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.76         (((k2_relset_1 @ X23 @ X22 @ X24) != (X22))
% 0.59/0.76          | ~ (v2_funct_1 @ X24)
% 0.59/0.76          | ((k2_tops_2 @ X23 @ X22 @ X24) = (k2_funct_1 @ X24))
% 0.59/0.76          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.59/0.76          | ~ (v1_funct_2 @ X24 @ X23 @ X22)
% 0.59/0.76          | ~ (v1_funct_1 @ X24))),
% 0.59/0.76      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.59/0.76  thf('66', plain,
% 0.59/0.76      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.59/0.76        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76            = (k2_funct_1 @ sk_C))
% 0.59/0.76        | ~ (v2_funct_1 @ sk_C)
% 0.59/0.76        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76            != (u1_struct_0 @ sk_B)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['64', '65'])).
% 0.59/0.76  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('68', plain,
% 0.59/0.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('69', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('70', plain,
% 0.59/0.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76         = (k2_relat_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.76  thf('71', plain,
% 0.59/0.76      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76          = (k2_funct_1 @ sk_C))
% 0.59/0.76        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.59/0.76      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 0.59/0.76  thf('72', plain,
% 0.59/0.76      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.59/0.76        | ~ (l1_struct_0 @ sk_B)
% 0.59/0.76        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76            = (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['63', '71'])).
% 0.59/0.76  thf('73', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.76  thf('74', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('75', plain,
% 0.59/0.76      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.59/0.76        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76            = (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.59/0.76  thf('76', plain,
% 0.59/0.76      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76         = (k2_funct_1 @ sk_C))),
% 0.59/0.76      inference('simplify', [status(thm)], ['75'])).
% 0.59/0.76  thf('77', plain,
% 0.59/0.76      (((v2_struct_0 @ sk_B)
% 0.59/0.76        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.76            (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.59/0.76      inference('demod', [status(thm)], ['62', '76'])).
% 0.59/0.76  thf('78', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('79', plain,
% 0.59/0.76      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.76         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.59/0.76      inference('clc', [status(thm)], ['77', '78'])).
% 0.59/0.76  thf('80', plain,
% 0.59/0.76      (![X21 : $i]:
% 0.59/0.76         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.76  thf('81', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(t31_funct_2, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i]:
% 0.59/0.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.76       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.59/0.76         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.59/0.76           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.59/0.76           ( m1_subset_1 @
% 0.59/0.76             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.59/0.76  thf('82', plain,
% 0.59/0.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.76         (~ (v2_funct_1 @ X18)
% 0.59/0.76          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 0.59/0.76          | (m1_subset_1 @ (k2_funct_1 @ X18) @ 
% 0.59/0.76             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.59/0.76          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.59/0.76          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 0.59/0.76          | ~ (v1_funct_1 @ X18))),
% 0.59/0.76      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.59/0.76  thf('83', plain,
% 0.59/0.76      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.59/0.76        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76           (k1_zfmisc_1 @ 
% 0.59/0.76            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.59/0.76        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76            != (u1_struct_0 @ sk_B))
% 0.59/0.76        | ~ (v2_funct_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['81', '82'])).
% 0.59/0.76  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('85', plain,
% 0.59/0.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('86', plain,
% 0.59/0.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76         = (k2_relat_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.76  thf('87', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('88', plain,
% 0.59/0.76      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76         (k1_zfmisc_1 @ 
% 0.59/0.76          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.59/0.76        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.59/0.76      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 0.59/0.76  thf('89', plain,
% 0.59/0.76      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.59/0.76        | ~ (l1_struct_0 @ sk_B)
% 0.59/0.76        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76           (k1_zfmisc_1 @ 
% 0.59/0.76            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.59/0.76      inference('sup-', [status(thm)], ['80', '88'])).
% 0.59/0.76  thf('90', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.76  thf('91', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('92', plain,
% 0.59/0.76      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.59/0.76        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76           (k1_zfmisc_1 @ 
% 0.59/0.76            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.59/0.76      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.59/0.76  thf('93', plain,
% 0.59/0.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.59/0.76      inference('simplify', [status(thm)], ['92'])).
% 0.59/0.76  thf('94', plain,
% 0.59/0.76      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.59/0.76         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.59/0.76          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.59/0.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.59/0.76  thf('95', plain,
% 0.59/0.76      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.76         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['93', '94'])).
% 0.59/0.76  thf('96', plain,
% 0.59/0.76      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('sup+', [status(thm)], ['79', '95'])).
% 0.59/0.76  thf('97', plain,
% 0.59/0.76      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 0.59/0.76        | ~ (v1_relat_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v2_funct_1 @ sk_C))),
% 0.59/0.76      inference('sup+', [status(thm)], ['50', '96'])).
% 0.59/0.76  thf('98', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(cc2_relat_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( v1_relat_1 @ A ) =>
% 0.59/0.76       ( ![B:$i]:
% 0.59/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.59/0.76  thf('99', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.59/0.76          | (v1_relat_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ X1))),
% 0.59/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.59/0.76  thf('100', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ 
% 0.59/0.76           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.59/0.76        | (v1_relat_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['98', '99'])).
% 0.59/0.76  thf(fc6_relat_1, axiom,
% 0.59/0.76    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.59/0.76  thf('101', plain,
% 0.59/0.76      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.59/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.59/0.76  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['100', '101'])).
% 0.59/0.76  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('104', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('105', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['97', '102', '103', '104'])).
% 0.59/0.76  thf('106', plain,
% 0.59/0.76      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.76          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.59/0.76           (k2_funct_1 @ sk_C)) @ 
% 0.59/0.76          sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['49', '105'])).
% 0.59/0.76  thf('107', plain,
% 0.59/0.76      (![X21 : $i]:
% 0.59/0.76         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.76  thf('108', plain,
% 0.59/0.76      (![X21 : $i]:
% 0.59/0.76         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.76  thf('109', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('110', plain,
% 0.59/0.76      (((m1_subset_1 @ sk_C @ 
% 0.59/0.76         (k1_zfmisc_1 @ 
% 0.59/0.76          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.59/0.76        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.76      inference('sup+', [status(thm)], ['108', '109'])).
% 0.59/0.76  thf('111', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('112', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.76      inference('demod', [status(thm)], ['110', '111'])).
% 0.59/0.76  thf('113', plain,
% 0.59/0.76      (((m1_subset_1 @ sk_C @ 
% 0.59/0.76         (k1_zfmisc_1 @ 
% 0.59/0.76          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.59/0.76        | ~ (l1_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['107', '112'])).
% 0.59/0.76  thf('114', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('115', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.59/0.76      inference('demod', [status(thm)], ['113', '114'])).
% 0.59/0.76  thf('116', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.76  thf('117', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.59/0.76      inference('demod', [status(thm)], ['115', '116'])).
% 0.59/0.76  thf('118', plain,
% 0.59/0.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.76         (~ (v2_funct_1 @ X18)
% 0.59/0.76          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 0.59/0.76          | (m1_subset_1 @ (k2_funct_1 @ X18) @ 
% 0.59/0.76             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.59/0.76          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.59/0.76          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 0.59/0.76          | ~ (v1_funct_1 @ X18))),
% 0.59/0.76      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.59/0.76  thf('119', plain,
% 0.59/0.76      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.59/0.76        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76           (k1_zfmisc_1 @ 
% 0.59/0.76            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.59/0.76        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.76            != (k2_relat_1 @ sk_C))
% 0.59/0.76        | ~ (v2_funct_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['117', '118'])).
% 0.59/0.76  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('121', plain,
% 0.59/0.76      (![X21 : $i]:
% 0.59/0.76         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.76  thf('122', plain,
% 0.59/0.76      (![X21 : $i]:
% 0.59/0.76         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.76  thf('123', plain,
% 0.59/0.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('124', plain,
% 0.59/0.76      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.59/0.76        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.76      inference('sup+', [status(thm)], ['122', '123'])).
% 0.59/0.76  thf('125', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('126', plain,
% 0.59/0.76      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.76      inference('demod', [status(thm)], ['124', '125'])).
% 0.59/0.76  thf('127', plain,
% 0.59/0.76      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.59/0.76        | ~ (l1_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['121', '126'])).
% 0.59/0.76  thf('128', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('129', plain,
% 0.59/0.76      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('demod', [status(thm)], ['127', '128'])).
% 0.59/0.76  thf('130', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.76  thf('131', plain,
% 0.59/0.76      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['129', '130'])).
% 0.59/0.76  thf('132', plain,
% 0.59/0.76      (![X21 : $i]:
% 0.59/0.76         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.76  thf('133', plain,
% 0.59/0.76      (![X21 : $i]:
% 0.59/0.76         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.59/0.76      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.76  thf('134', plain,
% 0.59/0.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76         = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('135', plain,
% 0.59/0.76      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76          = (k2_struct_0 @ sk_B))
% 0.59/0.76        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.76      inference('sup+', [status(thm)], ['133', '134'])).
% 0.59/0.76  thf('136', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('137', plain,
% 0.59/0.76      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76         = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('demod', [status(thm)], ['135', '136'])).
% 0.59/0.76  thf('138', plain,
% 0.59/0.76      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76          = (k2_struct_0 @ sk_B))
% 0.59/0.76        | ~ (l1_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['132', '137'])).
% 0.59/0.76  thf('139', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('140', plain,
% 0.59/0.76      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.59/0.76         = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('demod', [status(thm)], ['138', '139'])).
% 0.59/0.76  thf('141', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.76  thf('142', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.76      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.76  thf('143', plain,
% 0.59/0.76      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.76         = (k2_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.59/0.76  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('145', plain,
% 0.59/0.76      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76         (k1_zfmisc_1 @ 
% 0.59/0.76          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.59/0.76        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.59/0.76      inference('demod', [status(thm)], ['119', '120', '131', '143', '144'])).
% 0.59/0.76  thf('146', plain,
% 0.59/0.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.59/0.76      inference('simplify', [status(thm)], ['145'])).
% 0.59/0.76  thf('147', plain,
% 0.59/0.76      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.76         (((k2_relset_1 @ X23 @ X22 @ X24) != (X22))
% 0.59/0.76          | ~ (v2_funct_1 @ X24)
% 0.59/0.76          | ((k2_tops_2 @ X23 @ X22 @ X24) = (k2_funct_1 @ X24))
% 0.59/0.76          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.59/0.76          | ~ (v1_funct_2 @ X24 @ X23 @ X22)
% 0.59/0.76          | ~ (v1_funct_1 @ X24))),
% 0.59/0.76      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.59/0.76  thf('148', plain,
% 0.59/0.76      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.76        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.59/0.76             (k2_struct_0 @ sk_A))
% 0.59/0.76        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.76            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.59/0.76        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.76        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.76            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['146', '147'])).
% 0.59/0.76  thf('149', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.59/0.76      inference('demod', [status(thm)], ['22', '23'])).
% 0.59/0.76  thf('150', plain,
% 0.59/0.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.76         (~ (v2_funct_1 @ X18)
% 0.59/0.76          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 0.59/0.76          | (v1_funct_1 @ (k2_funct_1 @ X18))
% 0.59/0.76          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.59/0.76          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 0.59/0.76          | ~ (v1_funct_1 @ X18))),
% 0.59/0.76      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.59/0.76  thf('151', plain,
% 0.59/0.76      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.59/0.76        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.76        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.76            != (k2_relat_1 @ sk_C))
% 0.59/0.76        | ~ (v2_funct_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['149', '150'])).
% 0.59/0.76  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('153', plain,
% 0.59/0.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['32', '33'])).
% 0.59/0.76  thf('154', plain,
% 0.59/0.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.76         = (k2_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.59/0.76  thf('155', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('156', plain,
% 0.59/0.76      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.76        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.59/0.76      inference('demod', [status(thm)], ['151', '152', '153', '154', '155'])).
% 0.59/0.76  thf('157', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.59/0.76      inference('simplify', [status(thm)], ['156'])).
% 0.59/0.76  thf('158', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.59/0.76      inference('demod', [status(thm)], ['115', '116'])).
% 0.59/0.76  thf('159', plain,
% 0.59/0.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.76         (~ (v2_funct_1 @ X18)
% 0.59/0.76          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 0.59/0.76          | (v1_funct_2 @ (k2_funct_1 @ X18) @ X19 @ X20)
% 0.59/0.76          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.59/0.76          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 0.59/0.76          | ~ (v1_funct_1 @ X18))),
% 0.59/0.76      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.59/0.76  thf('160', plain,
% 0.59/0.76      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.59/0.76        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.59/0.76           (k2_struct_0 @ sk_A))
% 0.59/0.76        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.76            != (k2_relat_1 @ sk_C))
% 0.59/0.76        | ~ (v2_funct_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['158', '159'])).
% 0.59/0.76  thf('161', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('162', plain,
% 0.59/0.76      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['129', '130'])).
% 0.59/0.76  thf('163', plain,
% 0.59/0.76      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.76         = (k2_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['140', '141', '142'])).
% 0.59/0.76  thf('164', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('165', plain,
% 0.59/0.76      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.59/0.76         (k2_struct_0 @ sk_A))
% 0.59/0.76        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.59/0.76      inference('demod', [status(thm)], ['160', '161', '162', '163', '164'])).
% 0.59/0.76  thf('166', plain,
% 0.59/0.76      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.59/0.76        (k2_struct_0 @ sk_A))),
% 0.59/0.76      inference('simplify', [status(thm)], ['165'])).
% 0.59/0.76  thf('167', plain,
% 0.59/0.76      (![X8 : $i]:
% 0.59/0.76         (~ (v2_funct_1 @ X8)
% 0.59/0.76          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 0.59/0.76          | ~ (v1_funct_1 @ X8)
% 0.59/0.76          | ~ (v1_relat_1 @ X8))),
% 0.59/0.76      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.59/0.76  thf('168', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.59/0.76      inference('simplify', [status(thm)], ['156'])).
% 0.59/0.76  thf(t61_funct_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.76       ( ( v2_funct_1 @ A ) =>
% 0.59/0.76         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.59/0.76             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.59/0.76           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.59/0.76             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.59/0.76  thf('169', plain,
% 0.59/0.76      (![X9 : $i]:
% 0.59/0.76         (~ (v2_funct_1 @ X9)
% 0.59/0.76          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 0.59/0.76              = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 0.59/0.76          | ~ (v1_funct_1 @ X9)
% 0.59/0.76          | ~ (v1_relat_1 @ X9))),
% 0.59/0.76      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.59/0.76  thf(t48_funct_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.76       ( ![B:$i]:
% 0.59/0.76         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.76           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.59/0.76               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.59/0.76             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.59/0.76  thf('170', plain,
% 0.59/0.76      (![X6 : $i, X7 : $i]:
% 0.59/0.76         (~ (v1_relat_1 @ X6)
% 0.59/0.76          | ~ (v1_funct_1 @ X6)
% 0.59/0.76          | (v2_funct_1 @ X7)
% 0.59/0.76          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 0.59/0.76          | ~ (v2_funct_1 @ (k5_relat_1 @ X6 @ X7))
% 0.59/0.76          | ~ (v1_funct_1 @ X7)
% 0.59/0.76          | ~ (v1_relat_1 @ X7))),
% 0.59/0.76      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.59/0.76  thf('171', plain,
% 0.59/0.76      (![X0 : $i]:
% 0.59/0.76         (~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.59/0.76          | ~ (v1_relat_1 @ X0)
% 0.59/0.76          | ~ (v1_funct_1 @ X0)
% 0.59/0.76          | ~ (v2_funct_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.76          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.59/0.76          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.76          | ~ (v1_funct_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ X0))),
% 0.59/0.76      inference('sup-', [status(thm)], ['169', '170'])).
% 0.59/0.76  thf(fc4_funct_1, axiom,
% 0.59/0.76    (![A:$i]:
% 0.59/0.76     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.59/0.76       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.59/0.76  thf('172', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 0.59/0.76      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.59/0.76  thf('173', plain,
% 0.59/0.76      (![X0 : $i]:
% 0.59/0.76         (~ (v1_relat_1 @ X0)
% 0.59/0.76          | ~ (v1_funct_1 @ X0)
% 0.59/0.76          | ~ (v2_funct_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.76          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.59/0.76          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.76          | ~ (v1_funct_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ X0))),
% 0.59/0.76      inference('demod', [status(thm)], ['171', '172'])).
% 0.59/0.76  thf('174', plain,
% 0.59/0.76      (![X0 : $i]:
% 0.59/0.76         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.76          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.59/0.76          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.59/0.76          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.59/0.76          | ~ (v2_funct_1 @ X0)
% 0.59/0.76          | ~ (v1_funct_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ X0))),
% 0.59/0.76      inference('simplify', [status(thm)], ['173'])).
% 0.59/0.76  thf('175', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v2_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.76        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.59/0.76        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['168', '174'])).
% 0.59/0.76  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['100', '101'])).
% 0.59/0.76  thf('177', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('178', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('179', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.76        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.59/0.76        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('demod', [status(thm)], ['175', '176', '177', '178'])).
% 0.59/0.76  thf('180', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.59/0.76      inference('demod', [status(thm)], ['22', '23'])).
% 0.59/0.76  thf('181', plain,
% 0.59/0.76      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.76         (~ (v2_funct_1 @ X18)
% 0.59/0.76          | ((k2_relset_1 @ X20 @ X19 @ X18) != (X19))
% 0.59/0.76          | (m1_subset_1 @ (k2_funct_1 @ X18) @ 
% 0.59/0.76             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.59/0.76          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.59/0.76          | ~ (v1_funct_2 @ X18 @ X20 @ X19)
% 0.59/0.76          | ~ (v1_funct_1 @ X18))),
% 0.59/0.76      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.59/0.76  thf('182', plain,
% 0.59/0.76      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.59/0.76        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76           (k1_zfmisc_1 @ 
% 0.59/0.76            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.59/0.76        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.76            != (k2_relat_1 @ sk_C))
% 0.59/0.76        | ~ (v2_funct_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['180', '181'])).
% 0.59/0.76  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('184', plain,
% 0.59/0.76      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['32', '33'])).
% 0.59/0.76  thf('185', plain,
% 0.59/0.76      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.76         = (k2_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.59/0.76  thf('186', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('187', plain,
% 0.59/0.76      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76         (k1_zfmisc_1 @ 
% 0.59/0.76          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.59/0.76        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.59/0.76      inference('demod', [status(thm)], ['182', '183', '184', '185', '186'])).
% 0.59/0.76  thf('188', plain,
% 0.59/0.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.59/0.76      inference('simplify', [status(thm)], ['187'])).
% 0.59/0.76  thf('189', plain,
% 0.59/0.76      (![X0 : $i, X1 : $i]:
% 0.59/0.76         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.59/0.76          | (v1_relat_1 @ X0)
% 0.59/0.76          | ~ (v1_relat_1 @ X1))),
% 0.59/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.59/0.76  thf('190', plain,
% 0.59/0.76      ((~ (v1_relat_1 @ 
% 0.59/0.76           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))
% 0.59/0.76        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['188', '189'])).
% 0.59/0.76  thf('191', plain,
% 0.59/0.76      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.59/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.59/0.76  thf('192', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['190', '191'])).
% 0.59/0.76  thf('193', plain,
% 0.59/0.76      ((((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.59/0.76        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('demod', [status(thm)], ['179', '192'])).
% 0.59/0.76  thf('194', plain,
% 0.59/0.76      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.59/0.76        | ~ (v1_relat_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v2_funct_1 @ sk_C)
% 0.59/0.76        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['167', '193'])).
% 0.59/0.76  thf('195', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['100', '101'])).
% 0.59/0.76  thf('196', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('197', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('198', plain,
% 0.59/0.76      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.59/0.76        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('demod', [status(thm)], ['194', '195', '196', '197'])).
% 0.59/0.76  thf('199', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.59/0.76      inference('simplify', [status(thm)], ['198'])).
% 0.59/0.76  thf('200', plain,
% 0.59/0.76      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.59/0.76      inference('simplify', [status(thm)], ['145'])).
% 0.59/0.76  thf('201', plain,
% 0.59/0.76      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.59/0.76         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 0.59/0.76          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.59/0.76      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.59/0.76  thf('202', plain,
% 0.59/0.76      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.76         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('sup-', [status(thm)], ['200', '201'])).
% 0.59/0.76  thf('203', plain,
% 0.59/0.76      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.76          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.59/0.76        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.59/0.76      inference('demod', [status(thm)], ['148', '157', '166', '199', '202'])).
% 0.59/0.76  thf('204', plain,
% 0.59/0.76      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('sup+', [status(thm)], ['79', '95'])).
% 0.59/0.76  thf('205', plain,
% 0.59/0.76      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.76          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.59/0.76        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.59/0.76      inference('demod', [status(thm)], ['203', '204'])).
% 0.59/0.76  thf('206', plain,
% 0.59/0.76      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.76         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('simplify', [status(thm)], ['205'])).
% 0.59/0.76  thf('207', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.59/0.76      inference('demod', [status(thm)], ['97', '102', '103', '104'])).
% 0.59/0.76  thf('208', plain,
% 0.59/0.76      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.59/0.76         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.76      inference('demod', [status(thm)], ['206', '207'])).
% 0.59/0.76  thf('209', plain,
% 0.59/0.76      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.76          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.59/0.76      inference('demod', [status(thm)], ['106', '208'])).
% 0.59/0.76  thf('210', plain,
% 0.59/0.76      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.59/0.76           sk_C)
% 0.59/0.76        | ~ (v1_relat_1 @ sk_C)
% 0.59/0.76        | ~ (v1_funct_1 @ sk_C)
% 0.59/0.76        | ~ (v2_funct_1 @ sk_C))),
% 0.59/0.76      inference('sup-', [status(thm)], ['0', '209'])).
% 0.59/0.76  thf('211', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf('212', plain,
% 0.59/0.76      ((m1_subset_1 @ sk_C @ 
% 0.59/0.76        (k1_zfmisc_1 @ 
% 0.59/0.76         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.76  thf(reflexivity_r2_funct_2, axiom,
% 0.59/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.76     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.76         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.76         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.59/0.76         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.76       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.59/0.76  thf('213', plain,
% 0.59/0.76      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.76         ((r2_funct_2 @ X14 @ X15 @ X16 @ X16)
% 0.59/0.76          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.59/0.76          | ~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.59/0.76          | ~ (v1_funct_1 @ X16)
% 0.59/0.76          | ~ (v1_funct_1 @ X17)
% 0.59/0.76          | ~ (v1_funct_2 @ X17 @ X14 @ X15)
% 0.59/0.76          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.59/0.76      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.59/0.76  thf('214', plain,
% 0.59/0.76      (![X0 : $i]:
% 0.59/0.76         (~ (m1_subset_1 @ X0 @ 
% 0.59/0.76             (k1_zfmisc_1 @ 
% 0.59/0.76              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.59/0.76          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.59/0.76          | ~ (v1_funct_1 @ X0)
% 0.59/0.76          | ~ (v1_funct_1 @ sk_C)
% 0.59/0.77          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.59/0.77          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.59/0.77             sk_C))),
% 0.59/0.77      inference('sup-', [status(thm)], ['212', '213'])).
% 0.59/0.77  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('216', plain,
% 0.59/0.77      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('217', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X0 @ 
% 0.59/0.77             (k1_zfmisc_1 @ 
% 0.59/0.77              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.59/0.77          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.59/0.77             sk_C))),
% 0.59/0.77      inference('demod', [status(thm)], ['214', '215', '216'])).
% 0.59/0.77  thf('218', plain,
% 0.59/0.77      (((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.59/0.77        | ~ (v1_funct_1 @ sk_C)
% 0.59/0.77        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['211', '217'])).
% 0.59/0.77  thf('219', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('220', plain,
% 0.59/0.77      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('221', plain,
% 0.59/0.77      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.59/0.77      inference('demod', [status(thm)], ['218', '219', '220'])).
% 0.59/0.77  thf('222', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.77      inference('demod', [status(thm)], ['100', '101'])).
% 0.59/0.77  thf('223', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('224', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('225', plain, ($false),
% 0.59/0.77      inference('demod', [status(thm)], ['210', '221', '222', '223', '224'])).
% 0.59/0.77  
% 0.59/0.77  % SZS output end Refutation
% 0.59/0.77  
% 0.59/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
