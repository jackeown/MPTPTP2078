%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.POotl0H7Ku

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 267 expanded)
%              Number of leaves         :   39 (  95 expanded)
%              Depth                    :   18
%              Number of atoms          : 1156 (4650 expanded)
%              Number of equality atoms :   81 ( 248 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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

thf('0',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X35 @ X36 )
        = X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X35 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('8',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ( ( k10_relat_1 @ X12 @ ( k9_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X32 )
      | ( v2_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('18',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['11','14','15','21'])).

thf('23',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('25',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k8_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k10_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k7_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k9_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('35',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['30'])).

thf('36',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X32 )
      | ( v2_funct_2 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('40',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['40','41','42'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('44',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v2_funct_2 @ X34 @ X33 )
      | ( ( k2_relat_1 @ X34 )
        = X33 )
      | ~ ( v5_relat_1 @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['45','46','49'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['51'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('53',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ( ( k7_relat_1 @ X7 @ X8 )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('56',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('57',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ( ( k10_relat_1 @ X12 @ ( k9_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['50','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('65',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k10_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('69',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('70',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k9_relat_1 @ X10 @ ( k10_relat_1 @ X10 @ X9 ) )
        = ( k3_xboole_0 @ X9 @ ( k9_relat_1 @ X10 @ ( k1_relat_1 @ X10 ) ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
      = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['67','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['45','46','49'])).

thf('77',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['51'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('78',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['75','76','79','80','81'])).

thf('83',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k9_relat_1 @ X10 @ ( k10_relat_1 @ X10 @ X9 ) )
        = ( k3_xboole_0 @ X9 @ ( k9_relat_1 @ X10 @ ( k1_relat_1 @ X10 ) ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = ( k3_xboole_0 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
      = ( k3_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('90',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_B != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['36','37','87','90'])).

thf('92',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['30'])).

thf('94',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('95',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['33','94'])).

thf('96',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.POotl0H7Ku
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 126 iterations in 0.086s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.55  thf(t92_funct_2, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.55         ( v3_funct_2 @ C @ A @ A ) & 
% 0.20/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.55       ( ( r1_tarski @ B @ A ) =>
% 0.20/0.55         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.20/0.55             ( B ) ) & 
% 0.20/0.55           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.20/0.55             ( B ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.55            ( v3_funct_2 @ C @ A @ A ) & 
% 0.20/0.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.55          ( ( r1_tarski @ B @ A ) =>
% 0.20/0.55            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.20/0.55                ( B ) ) & 
% 0.20/0.55              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.20/0.55                ( B ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.20/0.55  thf('0', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t67_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.55       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X35 : $i, X36 : $i]:
% 0.20/0.55         (((k1_relset_1 @ X35 @ X35 @ X36) = (X35))
% 0.20/0.55          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 0.20/0.55          | ~ (v1_funct_2 @ X36 @ X35 @ X35)
% 0.20/0.55          | ~ (v1_funct_1 @ X36))),
% 0.20/0.55      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.20/0.55        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.55  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.55         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.20/0.55          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.55  thf('8', plain, (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.55  thf('9', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.20/0.55  thf(t164_funct_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.55       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.20/0.55         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X11 : $i, X12 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X11 @ (k1_relat_1 @ X12))
% 0.20/0.55          | ~ (v2_funct_1 @ X12)
% 0.20/0.55          | ((k10_relat_1 @ X12 @ (k9_relat_1 @ X12 @ X11)) = (X11))
% 0.20/0.55          | ~ (v1_funct_1 @ X12)
% 0.20/0.55          | ~ (v1_relat_1 @ X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X0 @ sk_A)
% 0.20/0.55          | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.55          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 0.20/0.55          | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc1_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( v1_relat_1 @ C ) ))).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.55         ((v1_relat_1 @ X13)
% 0.20/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.55  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc2_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.20/0.55         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ X30)
% 0.20/0.55          | ~ (v3_funct_2 @ X30 @ X31 @ X32)
% 0.20/0.55          | (v2_funct_1 @ X30)
% 0.20/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (((v2_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.55  thf('19', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('21', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X0 @ sk_A)
% 0.20/0.55          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['11', '14', '15', '21'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '22'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k8_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.20/0.55          | ((k8_relset_1 @ X27 @ X28 @ X26 @ X29) = (k10_relat_1 @ X26 @ X29)))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.20/0.55          | ((k7_relset_1 @ X23 @ X24 @ X22 @ X25) = (k9_relat_1 @ X22 @ X25)))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.55          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B))
% 0.20/0.55        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.55            (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.55          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.55                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.20/0.55      inference('split', [status(esa)], ['30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.20/0.55          != (sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.55                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['29', '31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.55                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '32'])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.55          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.55                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.20/0.55      inference('split', [status(esa)], ['30'])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_B))
% 0.20/0.55          != (sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.55                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ X30)
% 0.20/0.55          | ~ (v3_funct_2 @ X30 @ X31 @ X32)
% 0.20/0.55          | (v2_funct_2 @ X30 @ X32)
% 0.20/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      (((v2_funct_2 @ sk_C @ sk_A)
% 0.20/0.55        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.55  thf('41', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('43', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.20/0.55      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.20/0.55  thf(d3_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.20/0.55       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      (![X33 : $i, X34 : $i]:
% 0.20/0.55         (~ (v2_funct_2 @ X34 @ X33)
% 0.20/0.55          | ((k2_relat_1 @ X34) = (X33))
% 0.20/0.55          | ~ (v5_relat_1 @ X34 @ X33)
% 0.20/0.55          | ~ (v1_relat_1 @ X34))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.20/0.55        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.55  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc2_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.55         ((v5_relat_1 @ X16 @ X18)
% 0.20/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.55  thf('49', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.20/0.55      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.55  thf('50', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['45', '46', '49'])).
% 0.20/0.55  thf(d10_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.55  thf('52', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.55      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.55  thf(t97_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.20/0.55         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         (~ (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.20/0.55          | ((k7_relat_1 @ X7 @ X8) = (X7))
% 0.20/0.55          | ~ (v1_relat_1 @ X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.55  thf(t148_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]:
% 0.20/0.55         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.20/0.55          | ~ (v1_relat_1 @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.55  thf('56', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.55      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      (![X11 : $i, X12 : $i]:
% 0.20/0.55         (~ (r1_tarski @ X11 @ (k1_relat_1 @ X12))
% 0.20/0.55          | ~ (v2_funct_1 @ X12)
% 0.20/0.55          | ((k10_relat_1 @ X12 @ (k9_relat_1 @ X12 @ X11)) = (X11))
% 0.20/0.55          | ~ (v1_funct_1 @ X12)
% 0.20/0.55          | ~ (v1_relat_1 @ X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.20/0.55              = (k1_relat_1 @ X0))
% 0.20/0.55          | ~ (v2_funct_1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k10_relat_1 @ X0 @ 
% 0.20/0.55            (k2_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 0.20/0.55            = (k1_relat_1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['55', '58'])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k10_relat_1 @ X0 @ 
% 0.20/0.55              (k2_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))
% 0.20/0.55              = (k1_relat_1 @ X0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['54', '60'])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v2_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['61'])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      ((((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))
% 0.20/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.55      inference('sup+', [status(thm)], ['50', '62'])).
% 0.20/0.55  thf('64', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('65', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.55      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.55  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('67', plain, (((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]:
% 0.20/0.55         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 0.20/0.55          | ~ (v1_relat_1 @ X5))),
% 0.20/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.55  thf(t148_funct_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.55       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.20/0.55         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i]:
% 0.20/0.55         (((k9_relat_1 @ X10 @ (k10_relat_1 @ X10 @ X9))
% 0.20/0.55            = (k3_xboole_0 @ X9 @ (k9_relat_1 @ X10 @ (k1_relat_1 @ X10))))
% 0.20/0.55          | ~ (v1_funct_1 @ X10)
% 0.20/0.55          | ~ (v1_relat_1 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.20/0.55            = (k3_xboole_0 @ X1 @ 
% 0.20/0.55               (k2_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)))))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['69', '70'])).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.20/0.55              = (k3_xboole_0 @ X1 @ 
% 0.20/0.55                 (k2_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['71'])).
% 0.20/0.55  thf('73', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.20/0.55            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ~ (v1_funct_1 @ X0))),
% 0.20/0.55      inference('sup+', [status(thm)], ['68', '72'])).
% 0.20/0.55  thf('74', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ X0)
% 0.20/0.55          | ~ (v1_relat_1 @ X0)
% 0.20/0.55          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.20/0.55              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['73'])).
% 0.20/0.55  thf('75', plain,
% 0.20/0.55      ((((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.20/0.55          = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)))
% 0.20/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.55      inference('sup+', [status(thm)], ['67', '74'])).
% 0.20/0.55  thf('76', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['45', '46', '49'])).
% 0.20/0.55  thf('77', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.55      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.55  thf(t28_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.55  thf('79', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.55  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('82', plain, (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['75', '76', '79', '80', '81'])).
% 0.20/0.55  thf('83', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i]:
% 0.20/0.55         (((k9_relat_1 @ X10 @ (k10_relat_1 @ X10 @ X9))
% 0.20/0.55            = (k3_xboole_0 @ X9 @ (k9_relat_1 @ X10 @ (k1_relat_1 @ X10))))
% 0.20/0.55          | ~ (v1_funct_1 @ X10)
% 0.20/0.55          | ~ (v1_relat_1 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.20/0.55  thf('84', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0))
% 0.20/0.55            = (k3_xboole_0 @ X0 @ sk_A))
% 0.20/0.55          | ~ (v1_relat_1 @ sk_C)
% 0.20/0.55          | ~ (v1_funct_1 @ sk_C))),
% 0.20/0.55      inference('sup+', [status(thm)], ['82', '83'])).
% 0.20/0.55  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('87', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0))
% 0.20/0.55           = (k3_xboole_0 @ X0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.20/0.55  thf('88', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('89', plain,
% 0.20/0.55      (![X3 : $i, X4 : $i]:
% 0.20/0.55         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.55  thf('90', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['88', '89'])).
% 0.20/0.55  thf('91', plain,
% 0.20/0.55      ((((sk_B) != (sk_B)))
% 0.20/0.55         <= (~
% 0.20/0.55             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.55                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.20/0.55      inference('demod', [status(thm)], ['36', '37', '87', '90'])).
% 0.20/0.55  thf('92', plain,
% 0.20/0.55      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.55          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['91'])).
% 0.20/0.55  thf('93', plain,
% 0.20/0.55      (~
% 0.20/0.55       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.55          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))) | 
% 0.20/0.55       ~
% 0.20/0.55       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.55          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.20/0.55      inference('split', [status(esa)], ['30'])).
% 0.20/0.55  thf('94', plain,
% 0.20/0.55      (~
% 0.20/0.55       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.20/0.55          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 0.20/0.55  thf('95', plain,
% 0.20/0.55      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['33', '94'])).
% 0.20/0.55  thf('96', plain, ($false),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['23', '95'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
