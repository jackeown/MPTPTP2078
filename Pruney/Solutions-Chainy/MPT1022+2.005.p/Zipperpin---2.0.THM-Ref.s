%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b9xJPAkpUu

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 205 expanded)
%              Number of leaves         :   38 (  77 expanded)
%              Depth                    :   13
%              Number of atoms          :  950 (3806 expanded)
%              Number of equality atoms :   66 ( 206 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t92_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ A )
        & ( v3_funct_2 @ C @ A @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r1_tarski @ B @ A )
       => ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) )
            = B )
          & ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) )
            = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ A )
          & ( v3_funct_2 @ C @ A @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r1_tarski @ B @ A )
         => ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) )
              = B )
            & ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) )
              = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t92_funct_2])).

thf('0',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k8_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k10_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k7_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k9_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X34 @ X35 )
        = X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['10','11','12','15'])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k9_relat_1 @ X3 @ ( k10_relat_1 @ X3 @ X2 ) )
        = ( k3_xboole_0 @ X2 @ ( k9_relat_1 @ X3 @ ( k1_relat_1 @ X3 ) ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = ( k3_xboole_0 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','21','22'])).

thf('24',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['1','4','7','23'])).

thf('25',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['10','11','12','15'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X4 @ ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ( ( k10_relat_1 @ X5 @ ( k9_relat_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('32',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X31 )
      | ( v2_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('33',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','36'])).

thf('38',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['25','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('41',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( sk_B != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,(
    ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    ( k3_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['24','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('50',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k7_relset_1 @ X26 @ X27 @ X28 @ X26 )
        = ( k2_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('51',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('54',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('55',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X31 )
      | ( v2_funct_2 @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('58',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['58','59','60'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('62',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v2_funct_2 @ X33 @ X32 )
      | ( ( k2_relat_1 @ X33 )
        = X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('66',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('67',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['63','64','67'])).

thf('69',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['55','68'])).

thf('70',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['51','52','69'])).

thf('71',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('73',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['48','70','73'])).

thf('75',plain,(
    $false ),
    inference(simplify,[status(thm)],['74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b9xJPAkpUu
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 51 iterations in 0.028s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.53  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(t92_funct_2, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.21/0.53         ( v3_funct_2 @ C @ A @ A ) & 
% 0.21/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.53       ( ( r1_tarski @ B @ A ) =>
% 0.21/0.53         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.21/0.53             ( B ) ) & 
% 0.21/0.53           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.21/0.53             ( B ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.21/0.53            ( v3_funct_2 @ C @ A @ A ) & 
% 0.21/0.53            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.53          ( ( r1_tarski @ B @ A ) =>
% 0.21/0.53            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.21/0.53                ( B ) ) & 
% 0.21/0.53              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.21/0.53                ( B ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.21/0.53          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B))
% 0.21/0.53        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.21/0.53            (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.21/0.53          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.21/0.53         <= (~
% 0.21/0.53             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.21/0.53                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k8_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.21/0.53          | ((k8_relset_1 @ X23 @ X24 @ X22 @ X25) = (k10_relat_1 @ X22 @ X25)))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.21/0.53          | ((k7_relset_1 @ X19 @ X20 @ X18 @ X21) = (k9_relat_1 @ X18 @ X21)))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t67_funct_2, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.53       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X34 : $i, X35 : $i]:
% 0.21/0.53         (((k1_relset_1 @ X34 @ X34 @ X35) = (X34))
% 0.21/0.53          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 0.21/0.53          | ~ (v1_funct_2 @ X35 @ X34 @ X34)
% 0.21/0.53          | ~ (v1_funct_1 @ X35))),
% 0.21/0.53      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.53        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.21/0.53        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('12', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.53         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.21/0.53          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['10', '11', '12', '15'])).
% 0.21/0.53  thf(t148_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.21/0.53         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i]:
% 0.21/0.53         (((k9_relat_1 @ X3 @ (k10_relat_1 @ X3 @ X2))
% 0.21/0.53            = (k3_xboole_0 @ X2 @ (k9_relat_1 @ X3 @ (k1_relat_1 @ X3))))
% 0.21/0.53          | ~ (v1_funct_1 @ X3)
% 0.21/0.53          | ~ (v1_relat_1 @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0))
% 0.21/0.53            = (k3_xboole_0 @ X0 @ (k9_relat_1 @ sk_C @ sk_A)))
% 0.21/0.53          | ~ (v1_relat_1 @ sk_C)
% 0.21/0.53          | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.53      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc1_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( v1_relat_1 @ C ) ))).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.53         ((v1_relat_1 @ X6)
% 0.21/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.53  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0))
% 0.21/0.53           = (k3_xboole_0 @ X0 @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['18', '21', '22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      ((((k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)) != (sk_B)))
% 0.21/0.53         <= (~
% 0.21/0.53             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.21/0.53                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.21/0.53      inference('demod', [status(thm)], ['1', '4', '7', '23'])).
% 0.21/0.53  thf('25', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('26', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['10', '11', '12', '15'])).
% 0.21/0.53  thf(t164_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.21/0.53         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X4 @ (k1_relat_1 @ X5))
% 0.21/0.53          | ~ (v2_funct_1 @ X5)
% 0.21/0.53          | ((k10_relat_1 @ X5 @ (k9_relat_1 @ X5 @ X4)) = (X4))
% 0.21/0.53          | ~ (v1_funct_1 @ X5)
% 0.21/0.53          | ~ (v1_relat_1 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X0 @ sk_A)
% 0.21/0.53          | ~ (v1_relat_1 @ sk_C)
% 0.21/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.53          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 0.21/0.53          | ~ (v2_funct_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc2_funct_2, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.53         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.53         (~ (v1_funct_1 @ X29)
% 0.21/0.53          | ~ (v3_funct_2 @ X29 @ X30 @ X31)
% 0.21/0.53          | (v2_funct_1 @ X29)
% 0.21/0.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (((v2_funct_1 @ sk_C)
% 0.21/0.53        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.53  thf('34', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('36', plain, ((v2_funct_1 @ sk_C)),
% 0.21/0.53      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X0 @ sk_A)
% 0.21/0.53          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['28', '29', '30', '36'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['25', '37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.21/0.53          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.21/0.53         <= (~
% 0.21/0.53             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.21/0.53                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.21/0.53          != (sk_B)))
% 0.21/0.53         <= (~
% 0.21/0.53             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.21/0.53                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.21/0.53         <= (~
% 0.21/0.53             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.21/0.53                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['39', '42'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      ((((sk_B) != (sk_B)))
% 0.21/0.53         <= (~
% 0.21/0.53             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.21/0.53                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['38', '43'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.21/0.53          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (~
% 0.21/0.53       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.21/0.53          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))) | 
% 0.21/0.53       ~
% 0.21/0.53       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.21/0.53          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['0'])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (~
% 0.21/0.53       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.21/0.53          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (((k3_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)) != (sk_B))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['24', '47'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t38_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.21/0.53         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.53         (((k7_relset_1 @ X26 @ X27 @ X28 @ X26)
% 0.21/0.53            = (k2_relset_1 @ X26 @ X27 @ X28))
% 0.21/0.53          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.21/0.53      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_A)
% 0.21/0.53         = (k2_relset_1 @ sk_A @ sk_A @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.53         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.21/0.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.53         (~ (v1_funct_1 @ X29)
% 0.21/0.53          | ~ (v3_funct_2 @ X29 @ X30 @ X31)
% 0.21/0.53          | (v2_funct_2 @ X29 @ X31)
% 0.21/0.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (((v2_funct_2 @ sk_C @ sk_A)
% 0.21/0.53        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.53  thf('59', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('61', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.21/0.53  thf(d3_funct_2, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.21/0.53       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      (![X32 : $i, X33 : $i]:
% 0.21/0.53         (~ (v2_funct_2 @ X33 @ X32)
% 0.21/0.53          | ((k2_relat_1 @ X33) = (X32))
% 0.21/0.53          | ~ (v5_relat_1 @ X33 @ X32)
% 0.21/0.53          | ~ (v1_relat_1 @ X33))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.21/0.53  thf('63', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.53        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.21/0.53        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.53  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc2_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.53         ((v5_relat_1 @ X9 @ X11)
% 0.21/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.53  thf('67', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.53  thf('68', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['63', '64', '67'])).
% 0.21/0.53  thf('69', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['55', '68'])).
% 0.21/0.53  thf('70', plain, (((k9_relat_1 @ sk_C @ sk_A) = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['51', '52', '69'])).
% 0.21/0.53  thf('71', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t28_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.53  thf('73', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.53  thf('74', plain, (((sk_B) != (sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['48', '70', '73'])).
% 0.21/0.53  thf('75', plain, ($false), inference('simplify', [status(thm)], ['74'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
