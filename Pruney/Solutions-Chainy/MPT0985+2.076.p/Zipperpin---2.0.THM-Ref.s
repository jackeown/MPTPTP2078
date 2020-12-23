%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q8qeJmw15L

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:37 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  268 (6237 expanded)
%              Number of leaves         :   47 (1904 expanded)
%              Depth                    :   48
%              Number of atoms          : 1983 (95593 expanded)
%              Number of equality atoms :  108 (3664 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k10_relat_1 @ X21 @ X22 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X21 ) @ X22 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('3',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('5',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t31_funct_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X35 @ X33 )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('12',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['20','23','24','25'])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['4','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['8','9'])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39','40'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X16: $i] :
      ( ( ( k9_relat_1 @ X16 @ ( k1_relat_1 @ X16 ) )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('43',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['3','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['2','47'])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X17: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k2_relat_1 @ X17 ) )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('51',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('53',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','53','54','55','56'])).

thf('58',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('59',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('60',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('62',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['60','62'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X44: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X44 ) @ ( k2_relat_1 @ X44 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['60','62'])).

thf('67',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X1 )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39','40'])).

thf('72',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ( zip_tseitin_0 @ sk_B @ X1 )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( zip_tseitin_0 @ sk_B @ X0 )
        | ( zip_tseitin_0 @ sk_B @ X1 )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X0 )
        | ( zip_tseitin_0 @ sk_B @ X1 )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(condensation,[status(thm)],['76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('80',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('84',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('88',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('90',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('91',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['85','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('95',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('96',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['67'])).

thf('97',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['67'])).

thf('102',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('103',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('104',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('106',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('108',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('109',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','53','54','55','56'])).

thf('110',plain,(
    ! [X44: $i] :
      ( ( v1_funct_2 @ X44 @ ( k1_relat_1 @ X44 ) @ ( k2_relat_1 @ X44 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('111',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39','40'])).

thf('113',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['107','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['106','121'])).

thf('123',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['67'])).

thf('124',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['101','124'])).

thf('126',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('127',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('128',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('129',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('131',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) @ sk_C )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['126','131'])).

thf('133',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('134',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['133'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('135',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('136',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('137',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['133'])).

thf('138',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['132','134','135','136','137'])).

thf('139',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['125','138'])).

thf('140',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('141',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('142',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['132','134','135','136','137'])).

thf('143',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39','40'])).

thf('144',plain,
    ( ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('146',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X44: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X44 ) @ ( k2_relat_1 @ X44 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('148',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ) @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
        = ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['146','151'])).

thf('153',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('154',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('155',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('156',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('157',plain,
    ( ( ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['152','153','154','155','156'])).

thf('158',plain,
    ( ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['141','157'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('159',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('160',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('161',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('163',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_funct_1 @ B ) ) ) )).

thf('164',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc3_funct_1])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['162','165'])).

thf('167',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['158','161','168'])).

thf('170',plain,
    ( ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['140','169'])).

thf('171',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['159','160'])).

thf('172',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['166','167'])).

thf('173',plain,
    ( ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('175',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('178',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('179',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['159','160'])).

thf('183',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('185',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['183','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['176','187'])).

thf('189',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('193',plain,(
    ! [X36: $i] :
      ( zip_tseitin_0 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['192'])).

thf('194',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('195',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['193','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['191','197'])).

thf('199',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['139','173','198'])).

thf('200',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['67'])).

thf('201',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['100','199','200'])).

thf('202',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['93','201'])).

thf('203',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','202'])).

thf('204',plain,(
    ! [X44: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X44 ) @ ( k2_relat_1 @ X44 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('205',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','39','40'])).

thf('207',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['67'])).

thf('209',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['100','199','200'])).

thf('210',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['208','209'])).

thf('211',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['207','210'])).

thf('212',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','211'])).

thf('213',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('214',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['212','213','214'])).

thf('216',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','215'])).

thf('217',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('218',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    $false ),
    inference(demod,[status(thm)],['216','217','218'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.q8qeJmw15L
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.60/1.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.60/1.78  % Solved by: fo/fo7.sh
% 1.60/1.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.60/1.78  % done 2210 iterations in 1.330s
% 1.60/1.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.60/1.78  % SZS output start Refutation
% 1.60/1.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.60/1.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.60/1.78  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.60/1.78  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.60/1.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.60/1.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.60/1.78  thf(sk_B_type, type, sk_B: $i).
% 1.60/1.78  thf(sk_A_type, type, sk_A: $i).
% 1.60/1.78  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.60/1.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.60/1.78  thf(sk_C_type, type, sk_C: $i).
% 1.60/1.78  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.60/1.78  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.60/1.78  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.60/1.78  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.60/1.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.60/1.78  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.60/1.78  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.60/1.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.60/1.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.60/1.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.60/1.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.60/1.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.60/1.78  thf(dt_k2_funct_1, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.60/1.78       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.60/1.78         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.60/1.78  thf('0', plain,
% 1.60/1.78      (![X20 : $i]:
% 1.60/1.78         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 1.60/1.78          | ~ (v1_funct_1 @ X20)
% 1.60/1.78          | ~ (v1_relat_1 @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf('1', plain,
% 1.60/1.78      (![X20 : $i]:
% 1.60/1.78         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 1.60/1.78          | ~ (v1_funct_1 @ X20)
% 1.60/1.78          | ~ (v1_relat_1 @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf(t155_funct_1, axiom,
% 1.60/1.78    (![A:$i,B:$i]:
% 1.60/1.78     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.60/1.78       ( ( v2_funct_1 @ B ) =>
% 1.60/1.78         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 1.60/1.78  thf('2', plain,
% 1.60/1.78      (![X21 : $i, X22 : $i]:
% 1.60/1.78         (~ (v2_funct_1 @ X21)
% 1.60/1.78          | ((k10_relat_1 @ X21 @ X22)
% 1.60/1.78              = (k9_relat_1 @ (k2_funct_1 @ X21) @ X22))
% 1.60/1.78          | ~ (v1_funct_1 @ X21)
% 1.60/1.78          | ~ (v1_relat_1 @ X21))),
% 1.60/1.78      inference('cnf', [status(esa)], [t155_funct_1])).
% 1.60/1.78  thf('3', plain,
% 1.60/1.78      (![X20 : $i]:
% 1.60/1.78         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 1.60/1.78          | ~ (v1_funct_1 @ X20)
% 1.60/1.78          | ~ (v1_relat_1 @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf(t55_funct_1, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.60/1.78       ( ( v2_funct_1 @ A ) =>
% 1.60/1.78         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.60/1.78           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.60/1.78  thf('4', plain,
% 1.60/1.78      (![X23 : $i]:
% 1.60/1.78         (~ (v2_funct_1 @ X23)
% 1.60/1.78          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 1.60/1.78          | ~ (v1_funct_1 @ X23)
% 1.60/1.78          | ~ (v1_relat_1 @ X23))),
% 1.60/1.78      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.60/1.78  thf('5', plain,
% 1.60/1.78      (![X20 : $i]:
% 1.60/1.78         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 1.60/1.78          | ~ (v1_funct_1 @ X20)
% 1.60/1.78          | ~ (v1_relat_1 @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf(t31_funct_2, conjecture,
% 1.60/1.78    (![A:$i,B:$i,C:$i]:
% 1.60/1.78     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.60/1.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.78       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.60/1.78         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.60/1.78           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.60/1.78           ( m1_subset_1 @
% 1.60/1.78             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.60/1.78  thf(zf_stmt_0, negated_conjecture,
% 1.60/1.78    (~( ![A:$i,B:$i,C:$i]:
% 1.60/1.78        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.60/1.78            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.78          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.60/1.78            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.60/1.78              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.60/1.78              ( m1_subset_1 @
% 1.60/1.78                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 1.60/1.78    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 1.60/1.78  thf('6', plain,
% 1.60/1.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf(redefinition_k2_relset_1, axiom,
% 1.60/1.78    (![A:$i,B:$i,C:$i]:
% 1.60/1.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.78       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.60/1.78  thf('7', plain,
% 1.60/1.78      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.60/1.78         (((k2_relset_1 @ X34 @ X35 @ X33) = (k2_relat_1 @ X33))
% 1.60/1.78          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.60/1.78      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.60/1.78  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.60/1.78      inference('sup-', [status(thm)], ['6', '7'])).
% 1.60/1.78  thf('9', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('10', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.60/1.78      inference('sup+', [status(thm)], ['8', '9'])).
% 1.60/1.78  thf('11', plain,
% 1.60/1.78      (![X20 : $i]:
% 1.60/1.78         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 1.60/1.78          | ~ (v1_funct_1 @ X20)
% 1.60/1.78          | ~ (v1_relat_1 @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf('12', plain,
% 1.60/1.78      (![X23 : $i]:
% 1.60/1.78         (~ (v2_funct_1 @ X23)
% 1.60/1.78          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 1.60/1.78          | ~ (v1_funct_1 @ X23)
% 1.60/1.78          | ~ (v1_relat_1 @ X23))),
% 1.60/1.78      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.60/1.78  thf(d10_xboole_0, axiom,
% 1.60/1.78    (![A:$i,B:$i]:
% 1.60/1.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.60/1.78  thf('13', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.60/1.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.60/1.78  thf('14', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.60/1.78      inference('simplify', [status(thm)], ['13'])).
% 1.60/1.78  thf(d18_relat_1, axiom,
% 1.60/1.78    (![A:$i,B:$i]:
% 1.60/1.78     ( ( v1_relat_1 @ B ) =>
% 1.60/1.78       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.60/1.78  thf('15', plain,
% 1.60/1.78      (![X14 : $i, X15 : $i]:
% 1.60/1.78         (~ (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.60/1.78          | (v4_relat_1 @ X14 @ X15)
% 1.60/1.78          | ~ (v1_relat_1 @ X14))),
% 1.60/1.78      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.60/1.78  thf('16', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['14', '15'])).
% 1.60/1.78  thf('17', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.60/1.78          | ~ (v1_relat_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ X0)
% 1.60/1.78          | ~ (v2_funct_1 @ X0)
% 1.60/1.78          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.60/1.78      inference('sup+', [status(thm)], ['12', '16'])).
% 1.60/1.78  thf('18', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (v1_relat_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ X0)
% 1.60/1.78          | ~ (v2_funct_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ X0)
% 1.60/1.78          | ~ (v1_relat_1 @ X0)
% 1.60/1.78          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['11', '17'])).
% 1.60/1.78  thf('19', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.60/1.78          | ~ (v2_funct_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ X0)
% 1.60/1.78          | ~ (v1_relat_1 @ X0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['18'])).
% 1.60/1.78  thf('20', plain,
% 1.60/1.78      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.60/1.78        | ~ (v1_relat_1 @ sk_C)
% 1.60/1.78        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.78        | ~ (v2_funct_1 @ sk_C))),
% 1.60/1.78      inference('sup+', [status(thm)], ['10', '19'])).
% 1.60/1.78  thf('21', plain,
% 1.60/1.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf(cc1_relset_1, axiom,
% 1.60/1.78    (![A:$i,B:$i,C:$i]:
% 1.60/1.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.78       ( v1_relat_1 @ C ) ))).
% 1.60/1.78  thf('22', plain,
% 1.60/1.78      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.60/1.78         ((v1_relat_1 @ X24)
% 1.60/1.78          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.60/1.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.60/1.78  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.78  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('25', plain, ((v2_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('26', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.60/1.78      inference('demod', [status(thm)], ['20', '23', '24', '25'])).
% 1.60/1.78  thf('27', plain,
% 1.60/1.78      (![X14 : $i, X15 : $i]:
% 1.60/1.78         (~ (v4_relat_1 @ X14 @ X15)
% 1.60/1.78          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.60/1.78          | ~ (v1_relat_1 @ X14))),
% 1.60/1.78      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.60/1.78  thf('28', plain,
% 1.60/1.78      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.78        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.60/1.78      inference('sup-', [status(thm)], ['26', '27'])).
% 1.60/1.78  thf('29', plain,
% 1.60/1.78      ((~ (v1_relat_1 @ sk_C)
% 1.60/1.78        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.78        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.60/1.78      inference('sup-', [status(thm)], ['5', '28'])).
% 1.60/1.78  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.78  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('32', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.60/1.78      inference('demod', [status(thm)], ['29', '30', '31'])).
% 1.60/1.78  thf('33', plain,
% 1.60/1.78      (![X0 : $i, X2 : $i]:
% 1.60/1.78         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.60/1.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.60/1.78  thf('34', plain,
% 1.60/1.78      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.60/1.78        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['32', '33'])).
% 1.60/1.78  thf('35', plain,
% 1.60/1.78      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.60/1.78        | ~ (v1_relat_1 @ sk_C)
% 1.60/1.78        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.78        | ~ (v2_funct_1 @ sk_C)
% 1.60/1.78        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['4', '34'])).
% 1.60/1.78  thf('36', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.60/1.78      inference('sup+', [status(thm)], ['8', '9'])).
% 1.60/1.78  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.60/1.78      inference('simplify', [status(thm)], ['13'])).
% 1.60/1.78  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.78  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('40', plain, ((v2_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('41', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['35', '36', '37', '38', '39', '40'])).
% 1.60/1.78  thf(t146_relat_1, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( v1_relat_1 @ A ) =>
% 1.60/1.78       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.60/1.78  thf('42', plain,
% 1.60/1.78      (![X16 : $i]:
% 1.60/1.78         (((k9_relat_1 @ X16 @ (k1_relat_1 @ X16)) = (k2_relat_1 @ X16))
% 1.60/1.78          | ~ (v1_relat_1 @ X16))),
% 1.60/1.78      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.60/1.78  thf('43', plain,
% 1.60/1.78      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.60/1.78          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.60/1.78        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('sup+', [status(thm)], ['41', '42'])).
% 1.60/1.78  thf('44', plain,
% 1.60/1.78      ((~ (v1_relat_1 @ sk_C)
% 1.60/1.78        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.78        | ((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.60/1.78            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['3', '43'])).
% 1.60/1.78  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.78  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('47', plain,
% 1.60/1.78      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.60/1.78         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.60/1.78  thf('48', plain,
% 1.60/1.78      ((((k10_relat_1 @ sk_C @ sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.60/1.78        | ~ (v1_relat_1 @ sk_C)
% 1.60/1.78        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.78        | ~ (v2_funct_1 @ sk_C))),
% 1.60/1.78      inference('sup+', [status(thm)], ['2', '47'])).
% 1.60/1.78  thf('49', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.60/1.78      inference('sup+', [status(thm)], ['8', '9'])).
% 1.60/1.78  thf(t169_relat_1, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( v1_relat_1 @ A ) =>
% 1.60/1.78       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.60/1.78  thf('50', plain,
% 1.60/1.78      (![X17 : $i]:
% 1.60/1.78         (((k10_relat_1 @ X17 @ (k2_relat_1 @ X17)) = (k1_relat_1 @ X17))
% 1.60/1.78          | ~ (v1_relat_1 @ X17))),
% 1.60/1.78      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.60/1.78  thf('51', plain,
% 1.60/1.78      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 1.60/1.78        | ~ (v1_relat_1 @ sk_C))),
% 1.60/1.78      inference('sup+', [status(thm)], ['49', '50'])).
% 1.60/1.78  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.78  thf('53', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 1.60/1.78      inference('demod', [status(thm)], ['51', '52'])).
% 1.60/1.78  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.78  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('56', plain, ((v2_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('57', plain,
% 1.60/1.78      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['48', '53', '54', '55', '56'])).
% 1.60/1.78  thf('58', plain,
% 1.60/1.78      (![X20 : $i]:
% 1.60/1.78         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 1.60/1.78          | ~ (v1_funct_1 @ X20)
% 1.60/1.78          | ~ (v1_relat_1 @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf('59', plain,
% 1.60/1.78      (![X20 : $i]:
% 1.60/1.78         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 1.60/1.78          | ~ (v1_funct_1 @ X20)
% 1.60/1.78          | ~ (v1_relat_1 @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf(d1_funct_2, axiom,
% 1.60/1.78    (![A:$i,B:$i,C:$i]:
% 1.60/1.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.78       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.60/1.78           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.60/1.78             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.60/1.78         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.60/1.78           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.60/1.78             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.60/1.78  thf(zf_stmt_1, axiom,
% 1.60/1.78    (![B:$i,A:$i]:
% 1.60/1.78     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.60/1.78       ( zip_tseitin_0 @ B @ A ) ))).
% 1.60/1.78  thf('60', plain,
% 1.60/1.78      (![X36 : $i, X37 : $i]:
% 1.60/1.78         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.60/1.78  thf(t113_zfmisc_1, axiom,
% 1.60/1.78    (![A:$i,B:$i]:
% 1.60/1.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.60/1.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.60/1.78  thf('61', plain,
% 1.60/1.78      (![X5 : $i, X6 : $i]:
% 1.60/1.78         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 1.60/1.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.60/1.78  thf('62', plain,
% 1.60/1.78      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['61'])).
% 1.60/1.78  thf('63', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.78         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.60/1.78      inference('sup+', [status(thm)], ['60', '62'])).
% 1.60/1.78  thf(t3_funct_2, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.60/1.78       ( ( v1_funct_1 @ A ) & 
% 1.60/1.78         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.60/1.78         ( m1_subset_1 @
% 1.60/1.78           A @ 
% 1.60/1.78           ( k1_zfmisc_1 @
% 1.60/1.78             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.60/1.78  thf('64', plain,
% 1.60/1.78      (![X44 : $i]:
% 1.60/1.78         ((m1_subset_1 @ X44 @ 
% 1.60/1.78           (k1_zfmisc_1 @ 
% 1.60/1.78            (k2_zfmisc_1 @ (k1_relat_1 @ X44) @ (k2_relat_1 @ X44))))
% 1.60/1.78          | ~ (v1_funct_1 @ X44)
% 1.60/1.78          | ~ (v1_relat_1 @ X44))),
% 1.60/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.60/1.78  thf('65', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.60/1.78          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 1.60/1.78          | ~ (v1_relat_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ X0))),
% 1.60/1.78      inference('sup+', [status(thm)], ['63', '64'])).
% 1.60/1.78  thf('66', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.78         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.60/1.78      inference('sup+', [status(thm)], ['60', '62'])).
% 1.60/1.78  thf('67', plain,
% 1.60/1.78      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.78        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.60/1.78        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('68', plain,
% 1.60/1.78      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('split', [status(esa)], ['67'])).
% 1.60/1.78  thf('69', plain,
% 1.60/1.78      ((![X0 : $i]:
% 1.60/1.78          (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.60/1.78           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['66', '68'])).
% 1.60/1.78  thf('70', plain,
% 1.60/1.78      ((![X0 : $i, X1 : $i]:
% 1.60/1.78          (~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.78           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.78           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X1)
% 1.60/1.78           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['65', '69'])).
% 1.60/1.78  thf('71', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['35', '36', '37', '38', '39', '40'])).
% 1.60/1.78  thf('72', plain,
% 1.60/1.78      ((![X0 : $i, X1 : $i]:
% 1.60/1.78          (~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.78           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.78           | (zip_tseitin_0 @ sk_B @ X1)
% 1.60/1.78           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('demod', [status(thm)], ['70', '71'])).
% 1.60/1.78  thf('73', plain,
% 1.60/1.78      ((![X0 : $i, X1 : $i]:
% 1.60/1.78          (~ (v1_relat_1 @ sk_C)
% 1.60/1.78           | ~ (v1_funct_1 @ sk_C)
% 1.60/1.78           | (zip_tseitin_0 @ sk_B @ X0)
% 1.60/1.78           | (zip_tseitin_0 @ sk_B @ X1)
% 1.60/1.78           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['59', '72'])).
% 1.60/1.78  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.78  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('76', plain,
% 1.60/1.78      ((![X0 : $i, X1 : $i]:
% 1.60/1.78          ((zip_tseitin_0 @ sk_B @ X0)
% 1.60/1.78           | (zip_tseitin_0 @ sk_B @ X1)
% 1.60/1.78           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('demod', [status(thm)], ['73', '74', '75'])).
% 1.60/1.78  thf('77', plain,
% 1.60/1.78      ((![X0 : $i]:
% 1.60/1.78          (~ (v1_relat_1 @ (k2_funct_1 @ sk_C)) | (zip_tseitin_0 @ sk_B @ X0)))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('condensation', [status(thm)], ['76'])).
% 1.60/1.78  thf('78', plain,
% 1.60/1.78      ((![X0 : $i]:
% 1.60/1.78          (~ (v1_relat_1 @ sk_C)
% 1.60/1.78           | ~ (v1_funct_1 @ sk_C)
% 1.60/1.78           | (zip_tseitin_0 @ sk_B @ X0)))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['58', '77'])).
% 1.60/1.78  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.78  thf('80', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('81', plain,
% 1.60/1.78      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('demod', [status(thm)], ['78', '79', '80'])).
% 1.60/1.78  thf('82', plain,
% 1.60/1.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.60/1.78  thf(zf_stmt_3, axiom,
% 1.60/1.78    (![C:$i,B:$i,A:$i]:
% 1.60/1.78     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.60/1.78       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.60/1.78  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.60/1.78  thf(zf_stmt_5, axiom,
% 1.60/1.78    (![A:$i,B:$i,C:$i]:
% 1.60/1.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.78       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.60/1.78         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.60/1.78           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.60/1.78             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.60/1.78  thf('83', plain,
% 1.60/1.78      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.60/1.78         (~ (zip_tseitin_0 @ X41 @ X42)
% 1.60/1.78          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 1.60/1.78          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.60/1.78  thf('84', plain,
% 1.60/1.78      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.60/1.78      inference('sup-', [status(thm)], ['82', '83'])).
% 1.60/1.78  thf('85', plain,
% 1.60/1.78      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['81', '84'])).
% 1.60/1.78  thf('86', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('87', plain,
% 1.60/1.78      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.60/1.78         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 1.60/1.78          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 1.60/1.78          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.60/1.78  thf('88', plain,
% 1.60/1.78      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 1.60/1.78        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['86', '87'])).
% 1.60/1.78  thf('89', plain,
% 1.60/1.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf(redefinition_k1_relset_1, axiom,
% 1.60/1.78    (![A:$i,B:$i,C:$i]:
% 1.60/1.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.78       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.60/1.78  thf('90', plain,
% 1.60/1.78      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.60/1.78         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 1.60/1.78          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.60/1.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.60/1.78  thf('91', plain,
% 1.60/1.78      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.60/1.78      inference('sup-', [status(thm)], ['89', '90'])).
% 1.60/1.78  thf('92', plain,
% 1.60/1.78      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['88', '91'])).
% 1.60/1.78  thf('93', plain,
% 1.60/1.78      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['85', '92'])).
% 1.60/1.78  thf('94', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.78  thf('95', plain,
% 1.60/1.78      (![X20 : $i]:
% 1.60/1.78         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 1.60/1.78          | ~ (v1_funct_1 @ X20)
% 1.60/1.78          | ~ (v1_relat_1 @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf('96', plain,
% 1.60/1.78      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 1.60/1.78         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.60/1.78      inference('split', [status(esa)], ['67'])).
% 1.60/1.78  thf('97', plain,
% 1.60/1.78      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 1.60/1.78         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['95', '96'])).
% 1.60/1.78  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('99', plain,
% 1.60/1.78      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 1.60/1.78      inference('demod', [status(thm)], ['97', '98'])).
% 1.60/1.78  thf('100', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['94', '99'])).
% 1.60/1.78  thf('101', plain,
% 1.60/1.78      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('split', [status(esa)], ['67'])).
% 1.60/1.78  thf('102', plain,
% 1.60/1.78      (![X36 : $i, X37 : $i]:
% 1.60/1.78         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.60/1.78  thf('103', plain,
% 1.60/1.78      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.60/1.78      inference('sup-', [status(thm)], ['82', '83'])).
% 1.60/1.78  thf('104', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 1.60/1.78      inference('sup-', [status(thm)], ['102', '103'])).
% 1.60/1.78  thf('105', plain,
% 1.60/1.78      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['88', '91'])).
% 1.60/1.78  thf('106', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['104', '105'])).
% 1.60/1.78  thf('107', plain,
% 1.60/1.78      (![X20 : $i]:
% 1.60/1.78         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 1.60/1.78          | ~ (v1_funct_1 @ X20)
% 1.60/1.78          | ~ (v1_relat_1 @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf('108', plain,
% 1.60/1.78      (![X20 : $i]:
% 1.60/1.78         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 1.60/1.78          | ~ (v1_funct_1 @ X20)
% 1.60/1.78          | ~ (v1_relat_1 @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf('109', plain,
% 1.60/1.78      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['48', '53', '54', '55', '56'])).
% 1.60/1.78  thf('110', plain,
% 1.60/1.78      (![X44 : $i]:
% 1.60/1.78         ((v1_funct_2 @ X44 @ (k1_relat_1 @ X44) @ (k2_relat_1 @ X44))
% 1.60/1.78          | ~ (v1_funct_1 @ X44)
% 1.60/1.78          | ~ (v1_relat_1 @ X44))),
% 1.60/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.60/1.78  thf('111', plain,
% 1.60/1.78      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C))
% 1.60/1.78        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.78        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('sup+', [status(thm)], ['109', '110'])).
% 1.60/1.78  thf('112', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['35', '36', '37', '38', '39', '40'])).
% 1.60/1.78  thf('113', plain,
% 1.60/1.78      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 1.60/1.78        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.78        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['111', '112'])).
% 1.60/1.78  thf('114', plain,
% 1.60/1.78      ((~ (v1_relat_1 @ sk_C)
% 1.60/1.78        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.78        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.78        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['108', '113'])).
% 1.60/1.78  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.78  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('117', plain,
% 1.60/1.78      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.78        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['114', '115', '116'])).
% 1.60/1.78  thf('118', plain,
% 1.60/1.78      ((~ (v1_relat_1 @ sk_C)
% 1.60/1.78        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.78        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['107', '117'])).
% 1.60/1.78  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.78  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('121', plain,
% 1.60/1.78      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 1.60/1.78      inference('demod', [status(thm)], ['118', '119', '120'])).
% 1.60/1.78  thf('122', plain,
% 1.60/1.78      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 1.60/1.78        | ((sk_B) = (k1_xboole_0)))),
% 1.60/1.78      inference('sup+', [status(thm)], ['106', '121'])).
% 1.60/1.78  thf('123', plain,
% 1.60/1.78      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('split', [status(esa)], ['67'])).
% 1.60/1.78  thf('124', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0)))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['122', '123'])).
% 1.60/1.78  thf('125', plain,
% 1.60/1.78      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('demod', [status(thm)], ['101', '124'])).
% 1.60/1.78  thf('126', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0)))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['122', '123'])).
% 1.60/1.78  thf('127', plain,
% 1.60/1.78      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf(t3_subset, axiom,
% 1.60/1.78    (![A:$i,B:$i]:
% 1.60/1.78     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.60/1.78  thf('128', plain,
% 1.60/1.78      (![X8 : $i, X9 : $i]:
% 1.60/1.78         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.60/1.78      inference('cnf', [status(esa)], [t3_subset])).
% 1.60/1.78  thf('129', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 1.60/1.78      inference('sup-', [status(thm)], ['127', '128'])).
% 1.60/1.78  thf('130', plain,
% 1.60/1.78      (![X0 : $i, X2 : $i]:
% 1.60/1.78         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.60/1.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.60/1.78  thf('131', plain,
% 1.60/1.78      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 1.60/1.78        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['129', '130'])).
% 1.60/1.78  thf('132', plain,
% 1.60/1.78      (((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0) @ sk_C)
% 1.60/1.78         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C))))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['126', '131'])).
% 1.60/1.78  thf('133', plain,
% 1.60/1.78      (![X5 : $i, X6 : $i]:
% 1.60/1.78         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 1.60/1.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.60/1.78  thf('134', plain,
% 1.60/1.78      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['133'])).
% 1.60/1.78  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.60/1.78  thf('135', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.60/1.78  thf('136', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0)))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['122', '123'])).
% 1.60/1.78  thf('137', plain,
% 1.60/1.78      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['133'])).
% 1.60/1.78  thf('138', plain,
% 1.60/1.78      ((((k1_xboole_0) = (sk_C)))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('demod', [status(thm)], ['132', '134', '135', '136', '137'])).
% 1.60/1.78  thf('139', plain,
% 1.60/1.78      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('demod', [status(thm)], ['125', '138'])).
% 1.60/1.78  thf('140', plain,
% 1.60/1.78      (![X20 : $i]:
% 1.60/1.78         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 1.60/1.78          | ~ (v1_funct_1 @ X20)
% 1.60/1.78          | ~ (v1_relat_1 @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf('141', plain,
% 1.60/1.78      (![X20 : $i]:
% 1.60/1.78         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 1.60/1.78          | ~ (v1_funct_1 @ X20)
% 1.60/1.78          | ~ (v1_relat_1 @ X20))),
% 1.60/1.78      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.78  thf('142', plain,
% 1.60/1.78      ((((k1_xboole_0) = (sk_C)))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('demod', [status(thm)], ['132', '134', '135', '136', '137'])).
% 1.60/1.78  thf('143', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['35', '36', '37', '38', '39', '40'])).
% 1.60/1.78  thf('144', plain,
% 1.60/1.78      ((((sk_B) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('sup+', [status(thm)], ['142', '143'])).
% 1.60/1.78  thf('145', plain,
% 1.60/1.78      ((((sk_B) = (k1_xboole_0)))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['122', '123'])).
% 1.60/1.78  thf('146', plain,
% 1.60/1.78      ((((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('demod', [status(thm)], ['144', '145'])).
% 1.60/1.78  thf('147', plain,
% 1.60/1.78      (![X44 : $i]:
% 1.60/1.78         ((m1_subset_1 @ X44 @ 
% 1.60/1.78           (k1_zfmisc_1 @ 
% 1.60/1.78            (k2_zfmisc_1 @ (k1_relat_1 @ X44) @ (k2_relat_1 @ X44))))
% 1.60/1.78          | ~ (v1_funct_1 @ X44)
% 1.60/1.78          | ~ (v1_relat_1 @ X44))),
% 1.60/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.60/1.78  thf('148', plain,
% 1.60/1.78      (![X8 : $i, X9 : $i]:
% 1.60/1.78         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 1.60/1.78      inference('cnf', [status(esa)], [t3_subset])).
% 1.60/1.78  thf('149', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (v1_relat_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ X0)
% 1.60/1.78          | (r1_tarski @ X0 @ 
% 1.60/1.78             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 1.60/1.78      inference('sup-', [status(thm)], ['147', '148'])).
% 1.60/1.78  thf('150', plain,
% 1.60/1.78      (![X0 : $i, X2 : $i]:
% 1.60/1.78         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.60/1.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.60/1.78  thf('151', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (v1_funct_1 @ X0)
% 1.60/1.78          | ~ (v1_relat_1 @ X0)
% 1.60/1.78          | ~ (r1_tarski @ 
% 1.60/1.78               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 1.60/1.78          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['149', '150'])).
% 1.60/1.78  thf('152', plain,
% 1.60/1.78      (((~ (r1_tarski @ 
% 1.60/1.78            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 1.60/1.78             (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0))) @ 
% 1.60/1.78            (k2_funct_1 @ k1_xboole_0))
% 1.60/1.78         | ((k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0)) @ 
% 1.60/1.78             (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0)))
% 1.60/1.78             = (k2_funct_1 @ k1_xboole_0))
% 1.60/1.78         | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))
% 1.60/1.78         | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['146', '151'])).
% 1.60/1.78  thf('153', plain,
% 1.60/1.78      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['61'])).
% 1.60/1.78  thf('154', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.60/1.78  thf('155', plain,
% 1.60/1.78      ((((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('demod', [status(thm)], ['144', '145'])).
% 1.60/1.78  thf('156', plain,
% 1.60/1.78      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['61'])).
% 1.60/1.78  thf('157', plain,
% 1.60/1.78      (((((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))
% 1.60/1.78         | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))
% 1.60/1.78         | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('demod', [status(thm)], ['152', '153', '154', '155', '156'])).
% 1.60/1.78  thf('158', plain,
% 1.60/1.78      (((~ (v1_relat_1 @ k1_xboole_0)
% 1.60/1.78         | ~ (v1_funct_1 @ k1_xboole_0)
% 1.60/1.78         | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))
% 1.60/1.78         | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['141', '157'])).
% 1.60/1.78  thf(t4_subset_1, axiom,
% 1.60/1.78    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.60/1.78  thf('159', plain,
% 1.60/1.78      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.60/1.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.60/1.78  thf('160', plain,
% 1.60/1.78      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.60/1.78         ((v1_relat_1 @ X24)
% 1.60/1.78          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.60/1.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.60/1.78  thf('161', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.60/1.78      inference('sup-', [status(thm)], ['159', '160'])).
% 1.60/1.78  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.78  thf('163', plain,
% 1.60/1.78      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.60/1.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.60/1.78  thf(cc3_funct_1, axiom,
% 1.60/1.78    (![A:$i]:
% 1.60/1.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.60/1.78       ( ![B:$i]:
% 1.60/1.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_funct_1 @ B ) ) ) ))).
% 1.60/1.78  thf('164', plain,
% 1.60/1.78      (![X18 : $i, X19 : $i]:
% 1.60/1.78         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 1.60/1.78          | (v1_funct_1 @ X18)
% 1.60/1.78          | ~ (v1_funct_1 @ X19)
% 1.60/1.78          | ~ (v1_relat_1 @ X19))),
% 1.60/1.78      inference('cnf', [status(esa)], [cc3_funct_1])).
% 1.60/1.78  thf('165', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (v1_relat_1 @ X0)
% 1.60/1.78          | ~ (v1_funct_1 @ X0)
% 1.60/1.78          | (v1_funct_1 @ k1_xboole_0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['163', '164'])).
% 1.60/1.78  thf('166', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_funct_1 @ sk_C))),
% 1.60/1.78      inference('sup-', [status(thm)], ['162', '165'])).
% 1.60/1.78  thf('167', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('168', plain, ((v1_funct_1 @ k1_xboole_0)),
% 1.60/1.78      inference('demod', [status(thm)], ['166', '167'])).
% 1.60/1.78  thf('169', plain,
% 1.60/1.78      (((~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))
% 1.60/1.78         | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('demod', [status(thm)], ['158', '161', '168'])).
% 1.60/1.78  thf('170', plain,
% 1.60/1.78      (((~ (v1_relat_1 @ k1_xboole_0)
% 1.60/1.78         | ~ (v1_funct_1 @ k1_xboole_0)
% 1.60/1.78         | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['140', '169'])).
% 1.60/1.78  thf('171', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.60/1.78      inference('sup-', [status(thm)], ['159', '160'])).
% 1.60/1.78  thf('172', plain, ((v1_funct_1 @ k1_xboole_0)),
% 1.60/1.78      inference('demod', [status(thm)], ['166', '167'])).
% 1.60/1.78  thf('173', plain,
% 1.60/1.78      ((((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0)))
% 1.60/1.78         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 1.60/1.78      inference('demod', [status(thm)], ['170', '171', '172'])).
% 1.60/1.78  thf('174', plain,
% 1.60/1.78      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.60/1.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.60/1.78  thf('175', plain,
% 1.60/1.78      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.60/1.78         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 1.60/1.78          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 1.60/1.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.60/1.78  thf('176', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['174', '175'])).
% 1.60/1.78  thf('177', plain,
% 1.60/1.78      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.60/1.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.60/1.78  thf(cc2_relset_1, axiom,
% 1.60/1.78    (![A:$i,B:$i,C:$i]:
% 1.60/1.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.78       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.60/1.78  thf('178', plain,
% 1.60/1.78      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.60/1.78         ((v4_relat_1 @ X27 @ X28)
% 1.60/1.78          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.60/1.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.60/1.78  thf('179', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 1.60/1.78      inference('sup-', [status(thm)], ['177', '178'])).
% 1.60/1.78  thf('180', plain,
% 1.60/1.78      (![X14 : $i, X15 : $i]:
% 1.60/1.78         (~ (v4_relat_1 @ X14 @ X15)
% 1.60/1.78          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.60/1.78          | ~ (v1_relat_1 @ X14))),
% 1.60/1.78      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.60/1.78  thf('181', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         (~ (v1_relat_1 @ k1_xboole_0)
% 1.60/1.78          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['179', '180'])).
% 1.60/1.78  thf('182', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.60/1.78      inference('sup-', [status(thm)], ['159', '160'])).
% 1.60/1.78  thf('183', plain,
% 1.60/1.78      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 1.60/1.78      inference('demod', [status(thm)], ['181', '182'])).
% 1.60/1.78  thf('184', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.60/1.78      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.60/1.78  thf('185', plain,
% 1.60/1.78      (![X0 : $i, X2 : $i]:
% 1.60/1.78         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.60/1.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.60/1.78  thf('186', plain,
% 1.60/1.78      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['184', '185'])).
% 1.60/1.78  thf('187', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['183', '186'])).
% 1.60/1.78  thf('188', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.60/1.78      inference('demod', [status(thm)], ['176', '187'])).
% 1.60/1.78  thf('189', plain,
% 1.60/1.78      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.60/1.78         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 1.60/1.78          | (v1_funct_2 @ X40 @ X38 @ X39)
% 1.60/1.78          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.60/1.78  thf('190', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         (((X1) != (k1_xboole_0))
% 1.60/1.78          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.60/1.78          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.60/1.78      inference('sup-', [status(thm)], ['188', '189'])).
% 1.60/1.78  thf('191', plain,
% 1.60/1.78      (![X0 : $i]:
% 1.60/1.78         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.60/1.78          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.60/1.78      inference('simplify', [status(thm)], ['190'])).
% 1.60/1.78  thf('192', plain,
% 1.60/1.78      (![X36 : $i, X37 : $i]:
% 1.60/1.78         ((zip_tseitin_0 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.60/1.78  thf('193', plain, (![X36 : $i]: (zip_tseitin_0 @ X36 @ k1_xboole_0)),
% 1.60/1.78      inference('simplify', [status(thm)], ['192'])).
% 1.60/1.78  thf('194', plain,
% 1.60/1.78      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 1.60/1.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.60/1.78  thf('195', plain,
% 1.60/1.78      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.60/1.78         (~ (zip_tseitin_0 @ X41 @ X42)
% 1.60/1.78          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 1.60/1.78          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.60/1.78  thf('196', plain,
% 1.60/1.78      (![X0 : $i, X1 : $i]:
% 1.60/1.78         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.60/1.78      inference('sup-', [status(thm)], ['194', '195'])).
% 1.60/1.78  thf('197', plain,
% 1.60/1.78      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.60/1.78      inference('sup-', [status(thm)], ['193', '196'])).
% 1.60/1.78  thf('198', plain,
% 1.60/1.78      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.60/1.78      inference('demod', [status(thm)], ['191', '197'])).
% 1.60/1.78  thf('199', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 1.60/1.78      inference('demod', [status(thm)], ['139', '173', '198'])).
% 1.60/1.78  thf('200', plain,
% 1.60/1.78      (~
% 1.60/1.78       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 1.60/1.78       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 1.60/1.78       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('split', [status(esa)], ['67'])).
% 1.60/1.78  thf('201', plain,
% 1.60/1.78      (~
% 1.60/1.78       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.60/1.78      inference('sat_resolution*', [status(thm)], ['100', '199', '200'])).
% 1.60/1.78  thf('202', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.60/1.78      inference('simpl_trail', [status(thm)], ['93', '201'])).
% 1.60/1.78  thf('203', plain, (((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['57', '202'])).
% 1.60/1.78  thf('204', plain,
% 1.60/1.78      (![X44 : $i]:
% 1.60/1.78         ((m1_subset_1 @ X44 @ 
% 1.60/1.78           (k1_zfmisc_1 @ 
% 1.60/1.78            (k2_zfmisc_1 @ (k1_relat_1 @ X44) @ (k2_relat_1 @ X44))))
% 1.60/1.78          | ~ (v1_funct_1 @ X44)
% 1.60/1.78          | ~ (v1_relat_1 @ X44))),
% 1.60/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.60/1.78  thf('205', plain,
% 1.60/1.78      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78         (k1_zfmisc_1 @ 
% 1.60/1.78          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 1.60/1.78        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.78        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('sup+', [status(thm)], ['203', '204'])).
% 1.60/1.78  thf('206', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['35', '36', '37', '38', '39', '40'])).
% 1.60/1.78  thf('207', plain,
% 1.60/1.78      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.60/1.78        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.78        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('demod', [status(thm)], ['205', '206'])).
% 1.60/1.78  thf('208', plain,
% 1.60/1.78      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 1.60/1.78         <= (~
% 1.60/1.78             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 1.60/1.78      inference('split', [status(esa)], ['67'])).
% 1.60/1.78  thf('209', plain,
% 1.60/1.78      (~
% 1.60/1.78       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 1.60/1.78      inference('sat_resolution*', [status(thm)], ['100', '199', '200'])).
% 1.60/1.78  thf('210', plain,
% 1.60/1.78      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.60/1.78      inference('simpl_trail', [status(thm)], ['208', '209'])).
% 1.60/1.78  thf('211', plain,
% 1.60/1.78      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.78        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('clc', [status(thm)], ['207', '210'])).
% 1.60/1.78  thf('212', plain,
% 1.60/1.78      ((~ (v1_relat_1 @ sk_C)
% 1.60/1.78        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.78        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.78      inference('sup-', [status(thm)], ['1', '211'])).
% 1.60/1.78  thf('213', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.78  thf('214', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('215', plain, (~ (v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.60/1.78      inference('demod', [status(thm)], ['212', '213', '214'])).
% 1.60/1.78  thf('216', plain, ((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C))),
% 1.60/1.78      inference('sup-', [status(thm)], ['0', '215'])).
% 1.60/1.78  thf('217', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.78  thf('218', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.78  thf('219', plain, ($false),
% 1.60/1.78      inference('demod', [status(thm)], ['216', '217', '218'])).
% 1.60/1.78  
% 1.60/1.78  % SZS output end Refutation
% 1.60/1.78  
% 1.60/1.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
