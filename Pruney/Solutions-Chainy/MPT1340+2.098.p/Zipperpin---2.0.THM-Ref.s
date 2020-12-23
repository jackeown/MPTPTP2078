%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QdarjEs3Km

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:24 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  291 (2785 expanded)
%              Number of leaves         :   37 ( 830 expanded)
%              Depth                    :   20
%              Number of atoms          : 2923 (70024 expanded)
%              Number of equality atoms :  168 (2250 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','19'])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('22',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

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

thf('29',plain,(
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

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('47',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','31','38','39','47'])).

thf('49',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['20','21','49','50'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('53',plain,(
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

thf('54',plain,(
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

thf('55',plain,
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
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
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

thf('62',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('67',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64','65','66'])).

thf('68',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('70',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('75',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['73','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('82',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['48'])).

thf('85',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('87',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('91',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56','57','58','72','87','88','89','90','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['52','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('100',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','101','102','103'])).

thf('105',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','101','102','103'])).

thf('106',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['51','104','105'])).

thf('107',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('108',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
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
    inference('sup+',[status(thm)],['16','17'])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X22 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('119',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('122',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
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
    inference('sup+',[status(thm)],['16','17'])).

thf('131',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['119','120','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('134',plain,(
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

thf('135',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('138',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('140',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('141',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['139','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('150',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['135','136','137','138','150'])).

thf('152',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['132','152'])).

thf('154',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','101','102','103'])).

thf('155',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
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

thf('157',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

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

thf('159',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relset_1 @ X17 @ X16 @ X15 )
       != X16 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('160',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('163',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('164',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['160','161','162','163','164'])).

thf('166',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('168',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relset_1 @ X17 @ X16 @ X15 )
       != X16 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X15 ) @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('169',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('172',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['169','170','171','172','173'])).

thf('175',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','101','102','103'])).

thf('177',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('179',plain,(
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

thf('180',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( l1_struct_0 @ X28 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) @ X30 )
       != ( k2_struct_0 @ X28 ) )
      | ~ ( v2_funct_1 @ X30 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t63_tops_2])).

thf('181',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['71'])).

thf('186',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('188',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('189',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['181','182','183','184','185','186','187','188','189'])).

thf('191',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('193',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k5_relat_1 @ X5 @ ( k2_funct_1 @ X5 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('194',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k2_funct_1 @ X7 ) )
      | ( ( k5_relat_1 @ X6 @ X7 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['192','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['191','198'])).

thf('200',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['99','100'])).

thf('201',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('204',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relset_1 @ X17 @ X16 @ X15 )
       != X16 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('205',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('208',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('209',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['205','206','207','208','209'])).

thf('211',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('213',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('215',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['165'])).

thf('217',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','215','216'])).

thf('218',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['178','217'])).

thf('219',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['99','100'])).

thf('220',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['218','219','220','221'])).

thf('223',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('225',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('226',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_relset_1 @ X17 @ X16 @ X15 )
       != X16 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X15 @ X17 @ X16 )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('227',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('230',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('231',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['227','228','229','230','231'])).

thf('233',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('235',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('237',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','101','102','103'])).

thf('239',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','101','102','103'])).

thf('240',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['237','238','239'])).

thf('241',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['157','166','177','223','224','240'])).

thf('242',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

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

thf('244',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( r2_funct_2 @ X12 @ X13 @ X11 @ X14 )
      | ( X11 != X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('245',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_funct_2 @ X12 @ X13 @ X14 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['243','245'])).

thf('247',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('248',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['246','247','248'])).

thf('250',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','101','102','103'])).

thf('251',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,(
    $false ),
    inference(demod,[status(thm)],['106','242','251'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QdarjEs3Km
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 352 iterations in 0.180s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.68  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.45/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.68  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.68  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.45/0.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.68  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.68  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.68  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.45/0.68  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.45/0.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.68  thf(d3_struct_0, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.68  thf('0', plain,
% 0.45/0.68      (![X18 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('1', plain,
% 0.45/0.68      (![X18 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      (![X18 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      (![X18 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf(t64_tops_2, conjecture,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_struct_0 @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.68                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.68                 ( m1_subset_1 @
% 0.45/0.68                   C @ 
% 0.45/0.68                   ( k1_zfmisc_1 @
% 0.45/0.68                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.68               ( ( ( ( k2_relset_1 @
% 0.45/0.68                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.68                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.68                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.68                 ( r2_funct_2 @
% 0.45/0.68                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.68                   ( k2_tops_2 @
% 0.45/0.68                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.68                     ( k2_tops_2 @
% 0.45/0.68                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.68                   C ) ) ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i]:
% 0.45/0.68        ( ( l1_struct_0 @ A ) =>
% 0.45/0.68          ( ![B:$i]:
% 0.45/0.68            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.68              ( ![C:$i]:
% 0.45/0.68                ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.68                    ( v1_funct_2 @
% 0.45/0.68                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.68                    ( m1_subset_1 @
% 0.45/0.68                      C @ 
% 0.45/0.68                      ( k1_zfmisc_1 @
% 0.45/0.68                        ( k2_zfmisc_1 @
% 0.45/0.68                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.68                  ( ( ( ( k2_relset_1 @
% 0.45/0.68                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.68                        ( k2_struct_0 @ B ) ) & 
% 0.45/0.68                      ( v2_funct_1 @ C ) ) =>
% 0.45/0.68                    ( r2_funct_2 @
% 0.45/0.68                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.68                      ( k2_tops_2 @
% 0.45/0.68                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.68                        ( k2_tops_2 @
% 0.45/0.68                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.68                      C ) ) ) ) ) ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.45/0.68  thf('4', plain,
% 0.45/0.68      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.68          sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('5', plain,
% 0.45/0.68      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.68           sk_C)
% 0.45/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.68  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.68          sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['5', '6'])).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.68           sk_C)
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup-', [status(thm)], ['2', '7'])).
% 0.45/0.68  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('10', plain,
% 0.45/0.68      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.68          sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.68            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.68           sk_C)
% 0.45/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['1', '10'])).
% 0.45/0.68  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('13', plain,
% 0.45/0.68      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.68           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.68          sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['11', '12'])).
% 0.45/0.68  thf('14', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.68  thf('15', plain,
% 0.45/0.68      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.45/0.68          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.68  thf('16', plain,
% 0.45/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.68  thf('17', plain,
% 0.45/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('18', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('19', plain,
% 0.45/0.68      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.68           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.68          sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['13', '18'])).
% 0.45/0.68  thf('20', plain,
% 0.45/0.68      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68           (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.68            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.68           sk_C)
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup-', [status(thm)], ['0', '19'])).
% 0.45/0.68  thf('21', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('22', plain,
% 0.45/0.68      (![X18 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('23', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('24', plain,
% 0.45/0.68      (((m1_subset_1 @ sk_C @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['22', '23'])).
% 0.45/0.68  thf('25', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('26', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.68  thf('27', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('28', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.68  thf(d4_tops_2, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.68       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.45/0.68         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.45/0.68  thf('29', plain,
% 0.45/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X20 @ X19 @ X21) != (X19))
% 0.45/0.68          | ~ (v2_funct_1 @ X21)
% 0.45/0.68          | ((k2_tops_2 @ X20 @ X19 @ X21) = (k2_funct_1 @ X21))
% 0.45/0.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.45/0.68          | ~ (v1_funct_2 @ X21 @ X20 @ X19)
% 0.45/0.68          | ~ (v1_funct_1 @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.68  thf('30', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.68        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68            = (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68            != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.68  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('32', plain,
% 0.45/0.68      (![X18 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('34', plain,
% 0.45/0.68      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['32', '33'])).
% 0.45/0.68  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('36', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['34', '35'])).
% 0.45/0.68  thf('37', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('38', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.68  thf('39', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('40', plain,
% 0.45/0.68      (![X18 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('41', plain,
% 0.45/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('42', plain,
% 0.45/0.68      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68          = (k2_struct_0 @ sk_B))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['40', '41'])).
% 0.45/0.68  thf('43', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('44', plain,
% 0.45/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['42', '43'])).
% 0.45/0.68  thf('45', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('46', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('47', plain,
% 0.45/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.45/0.68  thf('48', plain,
% 0.45/0.68      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68          = (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['30', '31', '38', '39', '47'])).
% 0.45/0.68  thf('49', plain,
% 0.45/0.68      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68         = (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['48'])).
% 0.45/0.68  thf('50', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('51', plain,
% 0.45/0.68      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.68           (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68          sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['20', '21', '49', '50'])).
% 0.45/0.68  thf(t55_funct_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.68       ( ( v2_funct_1 @ A ) =>
% 0.45/0.68         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.45/0.68           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.68  thf('52', plain,
% 0.45/0.68      (![X4 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X4)
% 0.45/0.68          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.45/0.68          | ~ (v1_funct_1 @ X4)
% 0.45/0.68          | ~ (v1_relat_1 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.68  thf('53', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(t62_tops_2, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_struct_0 @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.68                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.68                 ( m1_subset_1 @
% 0.45/0.68                   C @ 
% 0.45/0.68                   ( k1_zfmisc_1 @
% 0.45/0.68                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.68               ( ( ( ( k2_relset_1 @
% 0.45/0.68                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.68                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.68                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.68                 ( ( ( k1_relset_1 @
% 0.45/0.68                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.68                       ( k2_tops_2 @
% 0.45/0.68                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.45/0.68                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.68                   ( ( k2_relset_1 @
% 0.45/0.68                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.68                       ( k2_tops_2 @
% 0.45/0.68                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.45/0.68                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf('54', plain,
% 0.45/0.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.68         ((v2_struct_0 @ X25)
% 0.45/0.68          | ~ (l1_struct_0 @ X25)
% 0.45/0.68          | ((k2_relset_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25) @ X27)
% 0.45/0.68              != (k2_struct_0 @ X25))
% 0.45/0.68          | ~ (v2_funct_1 @ X27)
% 0.45/0.68          | ((k2_relset_1 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26) @ 
% 0.45/0.68              (k2_tops_2 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25) @ X27))
% 0.45/0.68              = (k2_struct_0 @ X26))
% 0.45/0.68          | ~ (m1_subset_1 @ X27 @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))))
% 0.45/0.68          | ~ (v1_funct_2 @ X27 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.45/0.68          | ~ (v1_funct_1 @ X27)
% 0.45/0.68          | ~ (l1_struct_0 @ X26))),
% 0.45/0.68      inference('cnf', [status(esa)], [t62_tops_2])).
% 0.45/0.68  thf('55', plain,
% 0.45/0.68      ((~ (l1_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.68            = (k2_struct_0 @ sk_A))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            != (k2_struct_0 @ sk_B))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.68        | (v2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.45/0.68  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('58', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('59', plain,
% 0.45/0.68      (![X18 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('60', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('61', plain,
% 0.45/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X20 @ X19 @ X21) != (X19))
% 0.45/0.68          | ~ (v2_funct_1 @ X21)
% 0.45/0.68          | ((k2_tops_2 @ X20 @ X19 @ X21) = (k2_funct_1 @ X21))
% 0.45/0.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.45/0.68          | ~ (v1_funct_2 @ X21 @ X20 @ X19)
% 0.45/0.68          | ~ (v1_funct_1 @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.68  thf('62', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            = (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            != (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.45/0.68  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('64', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('65', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('66', plain,
% 0.45/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.68  thf('67', plain,
% 0.45/0.68      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68          = (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['62', '63', '64', '65', '66'])).
% 0.45/0.68  thf('68', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B)
% 0.45/0.68        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            = (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['59', '67'])).
% 0.45/0.68  thf('69', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('71', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.45/0.68        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            = (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.45/0.68  thf('72', plain,
% 0.45/0.68      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['71'])).
% 0.45/0.68  thf('73', plain,
% 0.45/0.68      (![X18 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('74', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(dt_k2_tops_2, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.68       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 0.45/0.68         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 0.45/0.68         ( m1_subset_1 @
% 0.45/0.68           ( k2_tops_2 @ A @ B @ C ) @ 
% 0.45/0.68           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 0.45/0.68  thf('75', plain,
% 0.45/0.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (k2_tops_2 @ X22 @ X23 @ X24) @ 
% 0.45/0.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.68          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.45/0.68          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.45/0.68          | ~ (v1_funct_1 @ X24))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.45/0.68  thf('76', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | (m1_subset_1 @ 
% 0.45/0.68           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.68           (k1_zfmisc_1 @ 
% 0.45/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.68  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('78', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('79', plain,
% 0.45/0.68      ((m1_subset_1 @ 
% 0.45/0.68        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.45/0.68  thf('80', plain,
% 0.45/0.68      (((m1_subset_1 @ 
% 0.45/0.68         (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C) @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['73', '79'])).
% 0.45/0.68  thf('81', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('82', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('83', plain,
% 0.45/0.68      ((m1_subset_1 @ 
% 0.45/0.68        (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.45/0.68  thf('84', plain,
% 0.45/0.68      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68         = (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['48'])).
% 0.45/0.68  thf('85', plain,
% 0.45/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('demod', [status(thm)], ['83', '84'])).
% 0.45/0.68  thf('86', plain,
% 0.45/0.68      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.45/0.68          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.68  thf('87', plain,
% 0.45/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.68         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['85', '86'])).
% 0.45/0.68  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('89', plain,
% 0.45/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.68  thf('90', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('91', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('92', plain,
% 0.45/0.68      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.45/0.68        | (v2_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)],
% 0.45/0.68                ['55', '56', '57', '58', '72', '87', '88', '89', '90', '91'])).
% 0.45/0.68  thf('93', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_B)
% 0.45/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['92'])).
% 0.45/0.68  thf('94', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('95', plain,
% 0.45/0.68      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('clc', [status(thm)], ['93', '94'])).
% 0.45/0.68  thf('96', plain,
% 0.45/0.68      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.45/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.68      inference('sup+', [status(thm)], ['52', '95'])).
% 0.45/0.68  thf('97', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(cc2_relat_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( v1_relat_1 @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.68  thf('98', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.68          | (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.68  thf('99', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ 
% 0.45/0.68           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.45/0.68        | (v1_relat_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['97', '98'])).
% 0.45/0.68  thf(fc6_relat_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.68  thf('100', plain,
% 0.45/0.68      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.68  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['99', '100'])).
% 0.45/0.68  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('103', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('104', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['96', '101', '102', '103'])).
% 0.45/0.68  thf('105', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['96', '101', '102', '103'])).
% 0.45/0.68  thf('106', plain,
% 0.45/0.68      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.68          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68           (k2_funct_1 @ sk_C)) @ 
% 0.45/0.68          sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['51', '104', '105'])).
% 0.45/0.68  thf('107', plain,
% 0.45/0.68      (![X18 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('108', plain,
% 0.45/0.68      (![X18 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('109', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('110', plain,
% 0.45/0.68      (((m1_subset_1 @ sk_C @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup+', [status(thm)], ['108', '109'])).
% 0.45/0.68  thf('111', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('112', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['110', '111'])).
% 0.45/0.68  thf('113', plain,
% 0.45/0.68      (((m1_subset_1 @ sk_C @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['107', '112'])).
% 0.45/0.68  thf('114', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('115', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['113', '114'])).
% 0.45/0.68  thf('116', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('117', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['115', '116'])).
% 0.45/0.68  thf('118', plain,
% 0.45/0.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (k2_tops_2 @ X22 @ X23 @ X24) @ 
% 0.45/0.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.45/0.68          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.45/0.68          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.45/0.68          | ~ (v1_funct_1 @ X24))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 0.45/0.68  thf('119', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.68        | (m1_subset_1 @ 
% 0.45/0.68           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.45/0.68           (k1_zfmisc_1 @ 
% 0.45/0.68            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['117', '118'])).
% 0.45/0.68  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('121', plain,
% 0.45/0.68      (![X18 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('122', plain,
% 0.45/0.68      (![X18 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('123', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('124', plain,
% 0.45/0.68      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup+', [status(thm)], ['122', '123'])).
% 0.45/0.68  thf('125', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('126', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['124', '125'])).
% 0.45/0.68  thf('127', plain,
% 0.45/0.68      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['121', '126'])).
% 0.45/0.68  thf('128', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('129', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['127', '128'])).
% 0.45/0.68  thf('130', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('131', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['129', '130'])).
% 0.45/0.68  thf('132', plain,
% 0.45/0.68      ((m1_subset_1 @ 
% 0.45/0.68        (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.45/0.68      inference('demod', [status(thm)], ['119', '120', '131'])).
% 0.45/0.68  thf('133', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['115', '116'])).
% 0.45/0.68  thf('134', plain,
% 0.45/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X20 @ X19 @ X21) != (X19))
% 0.45/0.68          | ~ (v2_funct_1 @ X21)
% 0.45/0.68          | ((k2_tops_2 @ X20 @ X19 @ X21) = (k2_funct_1 @ X21))
% 0.45/0.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.45/0.68          | ~ (v1_funct_2 @ X21 @ X20 @ X19)
% 0.45/0.68          | ~ (v1_funct_1 @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.68  thf('135', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.68        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68            = (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68            != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['133', '134'])).
% 0.45/0.68  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('137', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['129', '130'])).
% 0.45/0.68  thf('138', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('139', plain,
% 0.45/0.68      (![X18 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('140', plain,
% 0.45/0.68      (![X18 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('141', plain,
% 0.45/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('142', plain,
% 0.45/0.68      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68          = (k2_struct_0 @ sk_B))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup+', [status(thm)], ['140', '141'])).
% 0.45/0.68  thf('143', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('144', plain,
% 0.45/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['142', '143'])).
% 0.45/0.68  thf('145', plain,
% 0.45/0.68      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68          = (k2_struct_0 @ sk_B))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['139', '144'])).
% 0.45/0.68  thf('146', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('147', plain,
% 0.45/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['145', '146'])).
% 0.45/0.68  thf('148', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('149', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('150', plain,
% 0.45/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.45/0.68  thf('151', plain,
% 0.45/0.68      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68          = (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['135', '136', '137', '138', '150'])).
% 0.45/0.68  thf('152', plain,
% 0.45/0.68      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68         = (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['151'])).
% 0.45/0.68  thf('153', plain,
% 0.45/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.45/0.68      inference('demod', [status(thm)], ['132', '152'])).
% 0.45/0.68  thf('154', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['96', '101', '102', '103'])).
% 0.45/0.68  thf('155', plain,
% 0.45/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['153', '154'])).
% 0.45/0.68  thf('156', plain,
% 0.45/0.68      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X20 @ X19 @ X21) != (X19))
% 0.45/0.68          | ~ (v2_funct_1 @ X21)
% 0.45/0.68          | ((k2_tops_2 @ X20 @ X19 @ X21) = (k2_funct_1 @ X21))
% 0.45/0.68          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19)))
% 0.45/0.68          | ~ (v1_funct_2 @ X21 @ X20 @ X19)
% 0.45/0.68          | ~ (v1_funct_1 @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.68  thf('157', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.68             (k1_relat_1 @ sk_C))
% 0.45/0.68        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['155', '156'])).
% 0.45/0.68  thf('158', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.68  thf(t31_funct_2, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.68       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.68         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.68           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.68           ( m1_subset_1 @
% 0.45/0.68             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.45/0.68  thf('159', plain,
% 0.45/0.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X15)
% 0.45/0.68          | ((k2_relset_1 @ X17 @ X16 @ X15) != (X16))
% 0.45/0.68          | (v1_funct_1 @ (k2_funct_1 @ X15))
% 0.45/0.68          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.45/0.68          | ~ (v1_funct_2 @ X15 @ X17 @ X16)
% 0.45/0.68          | ~ (v1_funct_1 @ X15))),
% 0.45/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.68  thf('160', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.68        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68            != (k2_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['158', '159'])).
% 0.45/0.68  thf('161', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('162', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.68  thf('163', plain,
% 0.45/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.45/0.68  thf('164', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('165', plain,
% 0.45/0.68      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['160', '161', '162', '163', '164'])).
% 0.45/0.68  thf('166', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['165'])).
% 0.45/0.68  thf('167', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['115', '116'])).
% 0.45/0.68  thf('168', plain,
% 0.45/0.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X15)
% 0.45/0.68          | ((k2_relset_1 @ X17 @ X16 @ X15) != (X16))
% 0.45/0.68          | (v1_funct_2 @ (k2_funct_1 @ X15) @ X16 @ X17)
% 0.45/0.68          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.45/0.68          | ~ (v1_funct_2 @ X15 @ X17 @ X16)
% 0.45/0.68          | ~ (v1_funct_1 @ X15))),
% 0.45/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.68  thf('169', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.68        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.68           (k2_struct_0 @ sk_A))
% 0.45/0.68        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68            != (k2_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['167', '168'])).
% 0.45/0.68  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('171', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['129', '130'])).
% 0.45/0.68  thf('172', plain,
% 0.45/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.45/0.68  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('174', plain,
% 0.45/0.68      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.68         (k2_struct_0 @ sk_A))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['169', '170', '171', '172', '173'])).
% 0.45/0.68  thf('175', plain,
% 0.45/0.68      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.68        (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('simplify', [status(thm)], ['174'])).
% 0.45/0.68  thf('176', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['96', '101', '102', '103'])).
% 0.45/0.68  thf('177', plain,
% 0.45/0.68      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.45/0.68        (k1_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['175', '176'])).
% 0.45/0.68  thf('178', plain,
% 0.45/0.68      (![X4 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X4)
% 0.45/0.68          | ((k2_relat_1 @ X4) = (k1_relat_1 @ (k2_funct_1 @ X4)))
% 0.45/0.68          | ~ (v1_funct_1 @ X4)
% 0.45/0.68          | ~ (v1_relat_1 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.68  thf('179', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(t63_tops_2, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_struct_0 @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( l1_struct_0 @ B ) =>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.68                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.68                 ( m1_subset_1 @
% 0.45/0.68                   C @ 
% 0.45/0.68                   ( k1_zfmisc_1 @
% 0.45/0.68                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.68               ( ( ( ( k2_relset_1 @
% 0.45/0.68                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.68                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.68                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.68                 ( v2_funct_1 @
% 0.45/0.68                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf('180', plain,
% 0.45/0.68      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.68         (~ (l1_struct_0 @ X28)
% 0.45/0.68          | ((k2_relset_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28) @ X30)
% 0.45/0.68              != (k2_struct_0 @ X28))
% 0.45/0.68          | ~ (v2_funct_1 @ X30)
% 0.45/0.68          | (v2_funct_1 @ 
% 0.45/0.68             (k2_tops_2 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28) @ X30))
% 0.45/0.68          | ~ (m1_subset_1 @ X30 @ 
% 0.45/0.68               (k1_zfmisc_1 @ 
% 0.45/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 0.45/0.68          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.45/0.68          | ~ (v1_funct_1 @ X30)
% 0.45/0.68          | ~ (l1_struct_0 @ X29))),
% 0.45/0.68      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.45/0.68  thf('181', plain,
% 0.45/0.68      ((~ (l1_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | (v2_funct_1 @ 
% 0.45/0.68           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68            != (k2_struct_0 @ sk_B))
% 0.45/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup-', [status(thm)], ['179', '180'])).
% 0.45/0.68  thf('182', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('184', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('185', plain,
% 0.45/0.68      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['71'])).
% 0.45/0.68  thf('186', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('187', plain,
% 0.45/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.68  thf('188', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.45/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('189', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('190', plain,
% 0.45/0.68      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)],
% 0.45/0.68                ['181', '182', '183', '184', '185', '186', '187', '188', '189'])).
% 0.45/0.68  thf('191', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['190'])).
% 0.45/0.68  thf('192', plain,
% 0.45/0.68      (![X4 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X4)
% 0.45/0.68          | ((k1_relat_1 @ X4) = (k2_relat_1 @ (k2_funct_1 @ X4)))
% 0.45/0.68          | ~ (v1_funct_1 @ X4)
% 0.45/0.68          | ~ (v1_relat_1 @ X4))),
% 0.45/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.68  thf(t61_funct_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.68       ( ( v2_funct_1 @ A ) =>
% 0.45/0.68         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.45/0.68             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.45/0.68           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.45/0.68             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.45/0.68  thf('193', plain,
% 0.45/0.68      (![X5 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X5)
% 0.45/0.68          | ((k5_relat_1 @ X5 @ (k2_funct_1 @ X5))
% 0.45/0.68              = (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.45/0.68          | ~ (v1_funct_1 @ X5)
% 0.45/0.68          | ~ (v1_relat_1 @ X5))),
% 0.45/0.68      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.45/0.68  thf(t64_funct_1, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.68           ( ( ( v2_funct_1 @ A ) & 
% 0.45/0.68               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.45/0.68               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.45/0.68             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.68  thf('194', plain,
% 0.45/0.68      (![X6 : $i, X7 : $i]:
% 0.45/0.68         (~ (v1_relat_1 @ X6)
% 0.45/0.68          | ~ (v1_funct_1 @ X6)
% 0.45/0.68          | ((X6) = (k2_funct_1 @ X7))
% 0.45/0.68          | ((k5_relat_1 @ X6 @ X7) != (k6_relat_1 @ (k2_relat_1 @ X7)))
% 0.45/0.68          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 0.45/0.68          | ~ (v2_funct_1 @ X7)
% 0.45/0.68          | ~ (v1_funct_1 @ X7)
% 0.45/0.68          | ~ (v1_relat_1 @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.45/0.68  thf('195', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.45/0.68            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['193', '194'])).
% 0.45/0.68  thf('196', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.45/0.68              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['195'])).
% 0.45/0.68  thf('197', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((k6_relat_1 @ (k1_relat_1 @ X0)) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['192', '196'])).
% 0.45/0.68  thf('198', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.68          | ~ (v2_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_funct_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X0))),
% 0.45/0.68      inference('simplify', [status(thm)], ['197'])).
% 0.45/0.68  thf('199', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['191', '198'])).
% 0.45/0.68  thf('200', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['99', '100'])).
% 0.45/0.68  thf('201', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('202', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('203', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.68  thf('204', plain,
% 0.45/0.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X15)
% 0.45/0.68          | ((k2_relset_1 @ X17 @ X16 @ X15) != (X16))
% 0.45/0.68          | (m1_subset_1 @ (k2_funct_1 @ X15) @ 
% 0.45/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.45/0.68          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.45/0.68          | ~ (v1_funct_2 @ X15 @ X17 @ X16)
% 0.45/0.68          | ~ (v1_funct_1 @ X15))),
% 0.45/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.68  thf('205', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.68        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68           (k1_zfmisc_1 @ 
% 0.45/0.68            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.45/0.68        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68            != (k2_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['203', '204'])).
% 0.45/0.68  thf('206', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('207', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.68  thf('208', plain,
% 0.45/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.45/0.68  thf('209', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('210', plain,
% 0.45/0.68      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['205', '206', '207', '208', '209'])).
% 0.45/0.68  thf('211', plain,
% 0.45/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['210'])).
% 0.45/0.68  thf('212', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.68          | (v1_relat_1 @ X0)
% 0.45/0.68          | ~ (v1_relat_1 @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.68  thf('213', plain,
% 0.45/0.68      ((~ (v1_relat_1 @ 
% 0.45/0.68           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A)))
% 0.45/0.68        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['211', '212'])).
% 0.45/0.68  thf('214', plain,
% 0.45/0.68      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.68  thf('215', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['213', '214'])).
% 0.45/0.68  thf('216', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['165'])).
% 0.45/0.68  thf('217', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.68        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)],
% 0.45/0.68                ['199', '200', '201', '202', '215', '216'])).
% 0.45/0.68  thf('218', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.68        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['178', '217'])).
% 0.45/0.68  thf('219', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['99', '100'])).
% 0.45/0.68  thf('220', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('221', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('222', plain,
% 0.45/0.68      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.45/0.68        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['218', '219', '220', '221'])).
% 0.45/0.68  thf('223', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['222'])).
% 0.45/0.68  thf('224', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['190'])).
% 0.45/0.68  thf('225', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.45/0.68      inference('demod', [status(thm)], ['115', '116'])).
% 0.45/0.68  thf('226', plain,
% 0.45/0.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.68         (~ (v2_funct_1 @ X15)
% 0.45/0.68          | ((k2_relset_1 @ X17 @ X16 @ X15) != (X16))
% 0.45/0.68          | (m1_subset_1 @ (k2_funct_1 @ X15) @ 
% 0.45/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.45/0.68          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X16)))
% 0.45/0.68          | ~ (v1_funct_2 @ X15 @ X17 @ X16)
% 0.45/0.68          | ~ (v1_funct_1 @ X15))),
% 0.45/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.68  thf('227', plain,
% 0.45/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.45/0.68        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68           (k1_zfmisc_1 @ 
% 0.45/0.68            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.45/0.68        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68            != (k2_relat_1 @ sk_C))
% 0.45/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['225', '226'])).
% 0.45/0.68  thf('228', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('229', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['129', '130'])).
% 0.45/0.68  thf('230', plain,
% 0.45/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.45/0.68         = (k2_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.45/0.68  thf('231', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('232', plain,
% 0.45/0.68      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68         (k1_zfmisc_1 @ 
% 0.45/0.68          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.45/0.68        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)], ['227', '228', '229', '230', '231'])).
% 0.45/0.68  thf('233', plain,
% 0.45/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['232'])).
% 0.45/0.68  thf('234', plain,
% 0.45/0.68      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.68         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.45/0.68          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.68  thf('235', plain,
% 0.45/0.68      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.68         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['233', '234'])).
% 0.45/0.68  thf('236', plain,
% 0.45/0.68      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('clc', [status(thm)], ['93', '94'])).
% 0.45/0.68  thf('237', plain,
% 0.45/0.68      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.68         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['235', '236'])).
% 0.45/0.68  thf('238', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['96', '101', '102', '103'])).
% 0.45/0.68  thf('239', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['96', '101', '102', '103'])).
% 0.45/0.68  thf('240', plain,
% 0.45/0.68      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.45/0.68      inference('demod', [status(thm)], ['237', '238', '239'])).
% 0.45/0.68  thf('241', plain,
% 0.45/0.68      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.45/0.68        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.45/0.68      inference('demod', [status(thm)],
% 0.45/0.68                ['157', '166', '177', '223', '224', '240'])).
% 0.45/0.68  thf('242', plain,
% 0.45/0.68      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.45/0.68         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.45/0.68      inference('simplify', [status(thm)], ['241'])).
% 0.45/0.68  thf('243', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_C @ 
% 0.45/0.68        (k1_zfmisc_1 @ 
% 0.45/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['110', '111'])).
% 0.45/0.68  thf(redefinition_r2_funct_2, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.68         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.68       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.45/0.68  thf('244', plain,
% 0.45/0.68      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.45/0.68          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 0.45/0.68          | ~ (v1_funct_1 @ X11)
% 0.45/0.68          | ~ (v1_funct_1 @ X14)
% 0.45/0.68          | ~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.45/0.68          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.45/0.68          | (r2_funct_2 @ X12 @ X13 @ X11 @ X14)
% 0.45/0.68          | ((X11) != (X14)))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.45/0.68  thf('245', plain,
% 0.45/0.68      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.68         ((r2_funct_2 @ X12 @ X13 @ X14 @ X14)
% 0.45/0.68          | ~ (v1_funct_1 @ X14)
% 0.45/0.68          | ~ (v1_funct_2 @ X14 @ X12 @ X13)
% 0.45/0.68          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['244'])).
% 0.45/0.68  thf('246', plain,
% 0.45/0.68      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.68        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.68           sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['243', '245'])).
% 0.45/0.68  thf('247', plain,
% 0.45/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.68      inference('demod', [status(thm)], ['124', '125'])).
% 0.45/0.68  thf('248', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('249', plain,
% 0.45/0.68      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['246', '247', '248'])).
% 0.45/0.68  thf('250', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['96', '101', '102', '103'])).
% 0.45/0.68  thf('251', plain,
% 0.45/0.68      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.45/0.68      inference('demod', [status(thm)], ['249', '250'])).
% 0.45/0.68  thf('252', plain, ($false),
% 0.45/0.68      inference('demod', [status(thm)], ['106', '242', '251'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
