%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eEgP7FmTXu

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:26 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 646 expanded)
%              Number of leaves         :   41 ( 213 expanded)
%              Depth                    :   18
%              Number of atoms          : 1644 (11208 expanded)
%              Number of equality atoms :   90 ( 477 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

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

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X36 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) )
      | ~ ( v3_funct_2 @ X37 @ X36 @ X36 )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X36 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v4_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['11','16'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k7_relat_1 @ X12 @ X13 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) )
    | ( ( k7_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A )
      = ( k2_funct_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('21',plain,
    ( ( k7_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A )
    = ( k2_funct_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('23',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('25',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v3_funct_2 @ X31 @ X32 @ X33 )
      | ( v2_funct_2 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('26',plain,
    ( ( v2_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X36: $i,X37: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X36 @ X37 ) @ X36 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) )
      | ~ ( v3_funct_2 @ X37 @ X36 @ X36 )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X36 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X36: $i,X37: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) )
      | ~ ( v3_funct_2 @ X37 @ X36 @ X36 )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X36 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('36',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    v2_funct_2 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['26','33','40'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('42',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v2_funct_2 @ X35 @ X34 )
      | ( ( k2_relat_1 @ X35 )
        = X34 )
      | ~ ( v5_relat_1 @ X35 @ X34 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) )
    | ~ ( v5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('45',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('46',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('47',plain,(
    v5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['43','44','47'])).

thf('49',plain,(
    v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('50',plain,
    ( sk_A
    = ( k9_relat_1 @ ( k2_funct_2 @ sk_A @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('52',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_funct_2 @ X39 @ X38 )
        = ( k2_funct_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v3_funct_2 @ X38 @ X39 @ X39 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X39 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('53',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_funct_2 @ sk_A @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,
    ( sk_A
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['50','57'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k7_relat_1 @ X12 @ X13 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['62','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v3_funct_2 @ X31 @ X32 @ X33 )
      | ( v2_funct_2 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('75',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( v2_funct_2 @ X35 @ X34 )
      | ( ( k2_relat_1 @ X35 )
        = X34 )
      | ~ ( v5_relat_1 @ X35 @ X34 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('84',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['80','81','84'])).

thf('86',plain,
    ( sk_A
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','85'])).

thf('87',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('88',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X19 ) @ ( k9_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v2_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['86','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v3_funct_2 @ X31 @ X32 @ X33 )
      | ( v2_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('93',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('99',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','96','97','98'])).

thf('100',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['58','99'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('101',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ( ( k10_relat_1 @ X17 @ ( k9_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('104',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['102','103','104','105'])).

thf('107',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('109',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k8_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k10_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('112',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k7_relset_1 @ X24 @ X25 @ X23 @ X26 )
        = ( k9_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['114'])).

thf('116',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['113','115'])).

thf('117',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['110','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k10_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('119',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['114'])).

thf('120',plain,
    ( ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
     != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('122',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('125',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('127',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('129',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k7_relat_1 @ X12 @ X13 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('131',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_C @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('133',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('135',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('139',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k2_relat_1 @ X15 ) )
      | ( ( k9_relat_1 @ X15 @ ( k10_relat_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ X0 ) )
        = X0 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['137','140'])).

thf('142',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['131','132'])).

thf('143',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['131','132'])).

thf('144',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['131','132'])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['131','132'])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('148',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['65','66'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['141','142','143','144','145','146','147','148'])).

thf('150',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['80','81','84'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['122','151'])).

thf('153',plain,
    ( ( sk_B != sk_B )
   <= ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['120','121','152'])).

thf('154',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = sk_B ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B )
    | ( ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
     != sk_B ) ),
    inference(split,[status(esa)],['114'])).

thf('156',plain,(
    ( k8_relset_1 @ sk_A @ sk_A @ sk_C @ ( k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['154','155'])).

thf('157',plain,(
    ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['117','156'])).

thf('158',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['107','157'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eEgP7FmTXu
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.69  % Solved by: fo/fo7.sh
% 0.51/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.69  % done 385 iterations in 0.237s
% 0.51/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.69  % SZS output start Refutation
% 0.51/0.69  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.51/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.69  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.51/0.69  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.51/0.69  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.51/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.51/0.69  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.51/0.69  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.51/0.69  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.51/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.69  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.51/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.69  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.51/0.69  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.51/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.51/0.69  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.51/0.69  thf(t92_funct_2, conjecture,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.51/0.69         ( v3_funct_2 @ C @ A @ A ) & 
% 0.51/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.51/0.69       ( ( r1_tarski @ B @ A ) =>
% 0.51/0.69         ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.51/0.69             ( B ) ) & 
% 0.51/0.69           ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.51/0.69             ( B ) ) ) ) ))).
% 0.51/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.69    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.69        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.51/0.69            ( v3_funct_2 @ C @ A @ A ) & 
% 0.51/0.69            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.51/0.69          ( ( r1_tarski @ B @ A ) =>
% 0.51/0.69            ( ( ( k7_relset_1 @ A @ A @ C @ ( k8_relset_1 @ A @ A @ C @ B ) ) =
% 0.51/0.69                ( B ) ) & 
% 0.51/0.69              ( ( k8_relset_1 @ A @ A @ C @ ( k7_relset_1 @ A @ A @ C @ B ) ) =
% 0.51/0.69                ( B ) ) ) ) ) )),
% 0.51/0.69    inference('cnf.neg', [status(esa)], [t92_funct_2])).
% 0.51/0.69  thf('0', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('1', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(dt_k2_funct_2, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.51/0.69         ( v3_funct_2 @ B @ A @ A ) & 
% 0.51/0.69         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.51/0.69       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.51/0.69         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.51/0.69         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.51/0.69         ( m1_subset_1 @
% 0.51/0.69           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.51/0.69  thf('2', plain,
% 0.51/0.69      (![X36 : $i, X37 : $i]:
% 0.51/0.69         ((m1_subset_1 @ (k2_funct_2 @ X36 @ X37) @ 
% 0.51/0.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))
% 0.51/0.69          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))
% 0.51/0.69          | ~ (v3_funct_2 @ X37 @ X36 @ X36)
% 0.51/0.69          | ~ (v1_funct_2 @ X37 @ X36 @ X36)
% 0.51/0.69          | ~ (v1_funct_1 @ X37))),
% 0.51/0.69      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.51/0.69  thf('3', plain,
% 0.51/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.51/0.69        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.51/0.69        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.51/0.69           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.51/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.69  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('6', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('7', plain,
% 0.51/0.69      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.51/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.51/0.69  thf(cc2_relset_1, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.69       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.51/0.69  thf('8', plain,
% 0.51/0.69      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.51/0.69         ((v4_relat_1 @ X20 @ X21)
% 0.51/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.51/0.69  thf('9', plain, ((v4_relat_1 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A)),
% 0.51/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.51/0.69  thf(d18_relat_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( v1_relat_1 @ B ) =>
% 0.51/0.69       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.51/0.69  thf('10', plain,
% 0.51/0.69      (![X5 : $i, X6 : $i]:
% 0.51/0.69         (~ (v4_relat_1 @ X5 @ X6)
% 0.51/0.69          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.51/0.69          | ~ (v1_relat_1 @ X5))),
% 0.51/0.69      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.51/0.69  thf('11', plain,
% 0.51/0.69      ((~ (v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_C))
% 0.51/0.69        | (r1_tarski @ (k1_relat_1 @ (k2_funct_2 @ sk_A @ sk_C)) @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.69  thf('12', plain,
% 0.51/0.69      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.51/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.51/0.69  thf(cc2_relat_1, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( v1_relat_1 @ A ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.51/0.69  thf('13', plain,
% 0.51/0.69      (![X3 : $i, X4 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.51/0.69          | (v1_relat_1 @ X3)
% 0.51/0.69          | ~ (v1_relat_1 @ X4))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.51/0.69  thf('14', plain,
% 0.51/0.69      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 0.51/0.69        | (v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['12', '13'])).
% 0.51/0.69  thf(fc6_relat_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.51/0.69  thf('15', plain,
% 0.51/0.69      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.51/0.69      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.51/0.69  thf('16', plain, ((v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['14', '15'])).
% 0.51/0.69  thf('17', plain,
% 0.51/0.69      ((r1_tarski @ (k1_relat_1 @ (k2_funct_2 @ sk_A @ sk_C)) @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['11', '16'])).
% 0.51/0.69  thf(t97_relat_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( v1_relat_1 @ B ) =>
% 0.51/0.69       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.51/0.69         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.51/0.69  thf('18', plain,
% 0.51/0.69      (![X12 : $i, X13 : $i]:
% 0.51/0.69         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.51/0.69          | ((k7_relat_1 @ X12 @ X13) = (X12))
% 0.51/0.69          | ~ (v1_relat_1 @ X12))),
% 0.51/0.69      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.51/0.69  thf('19', plain,
% 0.51/0.69      ((~ (v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_C))
% 0.51/0.69        | ((k7_relat_1 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A)
% 0.51/0.69            = (k2_funct_2 @ sk_A @ sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['17', '18'])).
% 0.51/0.69  thf('20', plain, ((v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['14', '15'])).
% 0.51/0.69  thf('21', plain,
% 0.51/0.69      (((k7_relat_1 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A)
% 0.51/0.69         = (k2_funct_2 @ sk_A @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['19', '20'])).
% 0.51/0.69  thf(t148_relat_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( v1_relat_1 @ B ) =>
% 0.51/0.69       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.51/0.69  thf('22', plain,
% 0.51/0.69      (![X9 : $i, X10 : $i]:
% 0.51/0.69         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.51/0.69          | ~ (v1_relat_1 @ X9))),
% 0.51/0.69      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.51/0.69  thf('23', plain,
% 0.51/0.69      ((((k2_relat_1 @ (k2_funct_2 @ sk_A @ sk_C))
% 0.51/0.69          = (k9_relat_1 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A))
% 0.51/0.69        | ~ (v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_C)))),
% 0.51/0.69      inference('sup+', [status(thm)], ['21', '22'])).
% 0.51/0.69  thf('24', plain,
% 0.51/0.69      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.51/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.51/0.69  thf(cc2_funct_2, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.69       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.51/0.69         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.51/0.69  thf('25', plain,
% 0.51/0.69      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.51/0.69         (~ (v1_funct_1 @ X31)
% 0.51/0.69          | ~ (v3_funct_2 @ X31 @ X32 @ X33)
% 0.51/0.69          | (v2_funct_2 @ X31 @ X33)
% 0.51/0.69          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.51/0.69  thf('26', plain,
% 0.51/0.69      (((v2_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A)
% 0.51/0.69        | ~ (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A @ sk_A)
% 0.51/0.69        | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.51/0.69  thf('27', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('28', plain,
% 0.51/0.69      (![X36 : $i, X37 : $i]:
% 0.51/0.69         ((v3_funct_2 @ (k2_funct_2 @ X36 @ X37) @ X36 @ X36)
% 0.51/0.69          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))
% 0.51/0.69          | ~ (v3_funct_2 @ X37 @ X36 @ X36)
% 0.51/0.69          | ~ (v1_funct_2 @ X37 @ X36 @ X36)
% 0.51/0.69          | ~ (v1_funct_1 @ X37))),
% 0.51/0.69      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.51/0.69  thf('29', plain,
% 0.51/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.51/0.69        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.51/0.69        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.51/0.69  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('32', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('33', plain, ((v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.51/0.69  thf('34', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('35', plain,
% 0.51/0.69      (![X36 : $i, X37 : $i]:
% 0.51/0.69         ((v1_funct_1 @ (k2_funct_2 @ X36 @ X37))
% 0.51/0.69          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))
% 0.51/0.69          | ~ (v3_funct_2 @ X37 @ X36 @ X36)
% 0.51/0.69          | ~ (v1_funct_2 @ X37 @ X36 @ X36)
% 0.51/0.69          | ~ (v1_funct_1 @ X37))),
% 0.51/0.69      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.51/0.69  thf('36', plain,
% 0.51/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.51/0.69        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.51/0.69        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['34', '35'])).
% 0.51/0.69  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('38', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('39', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('40', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.51/0.69  thf('41', plain, ((v2_funct_2 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['26', '33', '40'])).
% 0.51/0.69  thf(d3_funct_2, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.51/0.69       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.51/0.69  thf('42', plain,
% 0.51/0.69      (![X34 : $i, X35 : $i]:
% 0.51/0.69         (~ (v2_funct_2 @ X35 @ X34)
% 0.51/0.69          | ((k2_relat_1 @ X35) = (X34))
% 0.51/0.69          | ~ (v5_relat_1 @ X35 @ X34)
% 0.51/0.69          | ~ (v1_relat_1 @ X35))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.51/0.69  thf('43', plain,
% 0.51/0.69      ((~ (v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_C))
% 0.51/0.69        | ~ (v5_relat_1 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A)
% 0.51/0.69        | ((k2_relat_1 @ (k2_funct_2 @ sk_A @ sk_C)) = (sk_A)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['41', '42'])).
% 0.51/0.69  thf('44', plain, ((v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['14', '15'])).
% 0.51/0.69  thf('45', plain,
% 0.51/0.69      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_C) @ 
% 0.51/0.69        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.51/0.69  thf('46', plain,
% 0.51/0.69      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.51/0.69         ((v5_relat_1 @ X20 @ X22)
% 0.51/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.51/0.69  thf('47', plain, ((v5_relat_1 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A)),
% 0.51/0.69      inference('sup-', [status(thm)], ['45', '46'])).
% 0.51/0.69  thf('48', plain, (((k2_relat_1 @ (k2_funct_2 @ sk_A @ sk_C)) = (sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['43', '44', '47'])).
% 0.51/0.69  thf('49', plain, ((v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['14', '15'])).
% 0.51/0.69  thf('50', plain,
% 0.51/0.69      (((sk_A) = (k9_relat_1 @ (k2_funct_2 @ sk_A @ sk_C) @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['23', '48', '49'])).
% 0.51/0.69  thf('51', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(redefinition_k2_funct_2, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.51/0.69         ( v3_funct_2 @ B @ A @ A ) & 
% 0.51/0.69         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.51/0.69       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.51/0.69  thf('52', plain,
% 0.51/0.69      (![X38 : $i, X39 : $i]:
% 0.51/0.69         (((k2_funct_2 @ X39 @ X38) = (k2_funct_1 @ X38))
% 0.51/0.69          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X39)))
% 0.51/0.69          | ~ (v3_funct_2 @ X38 @ X39 @ X39)
% 0.51/0.69          | ~ (v1_funct_2 @ X38 @ X39 @ X39)
% 0.51/0.69          | ~ (v1_funct_1 @ X38))),
% 0.51/0.69      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.51/0.69  thf('53', plain,
% 0.51/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.51/0.69        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.51/0.69        | ((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['51', '52'])).
% 0.51/0.69  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('55', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('56', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('57', plain, (((k2_funct_2 @ sk_A @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.51/0.69  thf('58', plain, (((sk_A) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['50', '57'])).
% 0.51/0.69  thf(d10_xboole_0, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.51/0.69  thf('59', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.51/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.69  thf('60', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.51/0.69      inference('simplify', [status(thm)], ['59'])).
% 0.51/0.69  thf('61', plain,
% 0.51/0.69      (![X12 : $i, X13 : $i]:
% 0.51/0.69         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.51/0.69          | ((k7_relat_1 @ X12 @ X13) = (X12))
% 0.51/0.69          | ~ (v1_relat_1 @ X12))),
% 0.51/0.69      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.51/0.69  thf('62', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['60', '61'])).
% 0.51/0.69  thf('63', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('64', plain,
% 0.51/0.69      (![X3 : $i, X4 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.51/0.69          | (v1_relat_1 @ X3)
% 0.51/0.69          | ~ (v1_relat_1 @ X4))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.51/0.69  thf('65', plain,
% 0.51/0.69      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['63', '64'])).
% 0.51/0.69  thf('66', plain,
% 0.51/0.69      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.51/0.69      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.51/0.69  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['65', '66'])).
% 0.51/0.69  thf('68', plain,
% 0.51/0.69      (![X9 : $i, X10 : $i]:
% 0.51/0.69         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.51/0.69          | ~ (v1_relat_1 @ X9))),
% 0.51/0.69      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.51/0.69  thf('69', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)) = (k9_relat_1 @ sk_C @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['67', '68'])).
% 0.51/0.69  thf('70', plain,
% 0.51/0.69      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.51/0.69        | ~ (v1_relat_1 @ sk_C))),
% 0.51/0.69      inference('sup+', [status(thm)], ['62', '69'])).
% 0.51/0.69  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['65', '66'])).
% 0.51/0.69  thf('72', plain,
% 0.51/0.69      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['70', '71'])).
% 0.51/0.69  thf('73', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('74', plain,
% 0.51/0.69      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.51/0.69         (~ (v1_funct_1 @ X31)
% 0.51/0.69          | ~ (v3_funct_2 @ X31 @ X32 @ X33)
% 0.51/0.69          | (v2_funct_2 @ X31 @ X33)
% 0.51/0.69          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.51/0.69  thf('75', plain,
% 0.51/0.69      (((v2_funct_2 @ sk_C @ sk_A)
% 0.51/0.69        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.51/0.69        | ~ (v1_funct_1 @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['73', '74'])).
% 0.51/0.69  thf('76', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('78', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.51/0.69  thf('79', plain,
% 0.51/0.69      (![X34 : $i, X35 : $i]:
% 0.51/0.69         (~ (v2_funct_2 @ X35 @ X34)
% 0.51/0.69          | ((k2_relat_1 @ X35) = (X34))
% 0.51/0.69          | ~ (v5_relat_1 @ X35 @ X34)
% 0.51/0.69          | ~ (v1_relat_1 @ X35))),
% 0.51/0.69      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.51/0.69  thf('80', plain,
% 0.51/0.69      ((~ (v1_relat_1 @ sk_C)
% 0.51/0.69        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.51/0.69        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['78', '79'])).
% 0.51/0.69  thf('81', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['65', '66'])).
% 0.51/0.69  thf('82', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('83', plain,
% 0.51/0.69      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.51/0.69         ((v5_relat_1 @ X20 @ X22)
% 0.51/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.51/0.69  thf('84', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.51/0.69      inference('sup-', [status(thm)], ['82', '83'])).
% 0.51/0.69  thf('85', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['80', '81', '84'])).
% 0.51/0.69  thf('86', plain, (((sk_A) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['72', '85'])).
% 0.51/0.69  thf('87', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.51/0.69      inference('simplify', [status(thm)], ['59'])).
% 0.51/0.69  thf(t177_funct_1, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.51/0.69           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.51/0.69             ( B ) ) ) ) ))).
% 0.51/0.69  thf('88', plain,
% 0.51/0.69      (![X18 : $i, X19 : $i]:
% 0.51/0.69         (~ (r1_tarski @ X18 @ (k1_relat_1 @ X19))
% 0.51/0.69          | ((k9_relat_1 @ (k2_funct_1 @ X19) @ (k9_relat_1 @ X19 @ X18))
% 0.51/0.69              = (X18))
% 0.51/0.69          | ~ (v2_funct_1 @ X19)
% 0.51/0.69          | ~ (v1_funct_1 @ X19)
% 0.51/0.69          | ~ (v1_relat_1 @ X19))),
% 0.51/0.69      inference('cnf', [status(esa)], [t177_funct_1])).
% 0.51/0.69  thf('89', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (v1_relat_1 @ X0)
% 0.51/0.69          | ~ (v1_funct_1 @ X0)
% 0.51/0.69          | ~ (v2_funct_1 @ X0)
% 0.51/0.69          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.51/0.69              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['87', '88'])).
% 0.51/0.69  thf('90', plain,
% 0.51/0.69      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A) = (k1_relat_1 @ sk_C))
% 0.51/0.69        | ~ (v2_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v1_relat_1 @ sk_C))),
% 0.51/0.69      inference('sup+', [status(thm)], ['86', '89'])).
% 0.51/0.69  thf('91', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('92', plain,
% 0.51/0.69      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.51/0.69         (~ (v1_funct_1 @ X31)
% 0.51/0.69          | ~ (v3_funct_2 @ X31 @ X32 @ X33)
% 0.51/0.69          | (v2_funct_1 @ X31)
% 0.51/0.69          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.51/0.69  thf('93', plain,
% 0.51/0.69      (((v2_funct_1 @ sk_C)
% 0.51/0.69        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.51/0.69        | ~ (v1_funct_1 @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['91', '92'])).
% 0.51/0.69  thf('94', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('96', plain, ((v2_funct_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.51/0.69  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['65', '66'])).
% 0.51/0.69  thf('99', plain,
% 0.51/0.69      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['90', '96', '97', '98'])).
% 0.51/0.69  thf('100', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.51/0.69      inference('sup+', [status(thm)], ['58', '99'])).
% 0.51/0.69  thf(t164_funct_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.69     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.69       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.51/0.69         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.51/0.69  thf('101', plain,
% 0.51/0.69      (![X16 : $i, X17 : $i]:
% 0.51/0.69         (~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 0.51/0.69          | ~ (v2_funct_1 @ X17)
% 0.51/0.69          | ((k10_relat_1 @ X17 @ (k9_relat_1 @ X17 @ X16)) = (X16))
% 0.51/0.69          | ~ (v1_funct_1 @ X17)
% 0.51/0.69          | ~ (v1_relat_1 @ X17))),
% 0.51/0.69      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.51/0.69  thf('102', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (r1_tarski @ X0 @ sk_A)
% 0.51/0.69          | ~ (v1_relat_1 @ sk_C)
% 0.51/0.69          | ~ (v1_funct_1 @ sk_C)
% 0.51/0.69          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0))
% 0.51/0.69          | ~ (v2_funct_1 @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['100', '101'])).
% 0.51/0.69  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['65', '66'])).
% 0.51/0.69  thf('104', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('105', plain, ((v2_funct_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.51/0.69  thf('106', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (r1_tarski @ X0 @ sk_A)
% 0.51/0.69          | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.51/0.69      inference('demod', [status(thm)], ['102', '103', '104', '105'])).
% 0.51/0.69  thf('107', plain,
% 0.51/0.69      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.51/0.69      inference('sup-', [status(thm)], ['0', '106'])).
% 0.51/0.69  thf('108', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(redefinition_k8_relset_1, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.69       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.51/0.69  thf('109', plain,
% 0.51/0.69      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.51/0.69          | ((k8_relset_1 @ X28 @ X29 @ X27 @ X30) = (k10_relat_1 @ X27 @ X30)))),
% 0.51/0.69      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.51/0.69  thf('110', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['108', '109'])).
% 0.51/0.69  thf('111', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(redefinition_k7_relset_1, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.69       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.51/0.69  thf('112', plain,
% 0.51/0.69      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.51/0.69          | ((k7_relset_1 @ X24 @ X25 @ X23 @ X26) = (k9_relat_1 @ X23 @ X26)))),
% 0.51/0.69      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.51/0.69  thf('113', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['111', '112'])).
% 0.51/0.69  thf('114', plain,
% 0.51/0.69      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.51/0.69          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B))
% 0.51/0.69        | ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.51/0.69            (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('115', plain,
% 0.51/0.69      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.51/0.69          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.51/0.69         <= (~
% 0.51/0.69             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.51/0.69                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.51/0.69      inference('split', [status(esa)], ['114'])).
% 0.51/0.69  thf('116', plain,
% 0.51/0.69      ((((k8_relset_1 @ sk_A @ sk_A @ sk_C @ (k9_relat_1 @ sk_C @ sk_B))
% 0.51/0.69          != (sk_B)))
% 0.51/0.69         <= (~
% 0.51/0.69             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.51/0.69                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.51/0.69      inference('sup-', [status(thm)], ['113', '115'])).
% 0.51/0.69  thf('117', plain,
% 0.51/0.69      ((((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B)))
% 0.51/0.69         <= (~
% 0.51/0.69             (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.51/0.69                (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.51/0.69      inference('sup-', [status(thm)], ['110', '116'])).
% 0.51/0.69  thf('118', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((k8_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k10_relat_1 @ sk_C @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['108', '109'])).
% 0.51/0.69  thf('119', plain,
% 0.51/0.69      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.51/0.69          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_B)))
% 0.51/0.69         <= (~
% 0.51/0.69             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.51/0.69                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.51/0.69      inference('split', [status(esa)], ['114'])).
% 0.51/0.69  thf('120', plain,
% 0.51/0.69      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ (k10_relat_1 @ sk_C @ sk_B))
% 0.51/0.69          != (sk_B)))
% 0.51/0.69         <= (~
% 0.51/0.69             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.51/0.69                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.51/0.69      inference('sup-', [status(thm)], ['118', '119'])).
% 0.51/0.69  thf('121', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((k7_relset_1 @ sk_A @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.51/0.69      inference('sup-', [status(thm)], ['111', '112'])).
% 0.51/0.69  thf('122', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('123', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('124', plain,
% 0.51/0.69      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.51/0.69         ((v4_relat_1 @ X20 @ X21)
% 0.51/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.51/0.69  thf('125', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.51/0.69      inference('sup-', [status(thm)], ['123', '124'])).
% 0.51/0.69  thf('126', plain,
% 0.51/0.69      (![X5 : $i, X6 : $i]:
% 0.51/0.69         (~ (v4_relat_1 @ X5 @ X6)
% 0.51/0.69          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.51/0.69          | ~ (v1_relat_1 @ X5))),
% 0.51/0.69      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.51/0.69  thf('127', plain,
% 0.51/0.69      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['125', '126'])).
% 0.51/0.69  thf('128', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['65', '66'])).
% 0.51/0.69  thf('129', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['127', '128'])).
% 0.51/0.69  thf('130', plain,
% 0.51/0.69      (![X12 : $i, X13 : $i]:
% 0.51/0.69         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.51/0.69          | ((k7_relat_1 @ X12 @ X13) = (X12))
% 0.51/0.69          | ~ (v1_relat_1 @ X12))),
% 0.51/0.69      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.51/0.69  thf('131', plain,
% 0.51/0.69      ((~ (v1_relat_1 @ sk_C) | ((k7_relat_1 @ sk_C @ sk_A) = (sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['129', '130'])).
% 0.51/0.69  thf('132', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['65', '66'])).
% 0.51/0.69  thf('133', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['131', '132'])).
% 0.51/0.69  thf('134', plain,
% 0.51/0.69      (![X9 : $i, X10 : $i]:
% 0.51/0.69         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.51/0.69          | ~ (v1_relat_1 @ X9))),
% 0.51/0.69      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.51/0.69  thf('135', plain,
% 0.51/0.69      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.51/0.69        | ~ (v1_relat_1 @ sk_C))),
% 0.51/0.69      inference('sup+', [status(thm)], ['133', '134'])).
% 0.51/0.69  thf('136', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.69      inference('demod', [status(thm)], ['65', '66'])).
% 0.51/0.69  thf('137', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.51/0.69      inference('demod', [status(thm)], ['135', '136'])).
% 0.51/0.69  thf('138', plain,
% 0.51/0.69      (![X9 : $i, X10 : $i]:
% 0.51/0.69         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.51/0.69          | ~ (v1_relat_1 @ X9))),
% 0.51/0.69      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.51/0.69  thf(t147_funct_1, axiom,
% 0.51/0.69    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.70       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.51/0.70         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.51/0.70  thf('139', plain,
% 0.51/0.70      (![X14 : $i, X15 : $i]:
% 0.51/0.70         (~ (r1_tarski @ X14 @ (k2_relat_1 @ X15))
% 0.51/0.70          | ((k9_relat_1 @ X15 @ (k10_relat_1 @ X15 @ X14)) = (X14))
% 0.51/0.70          | ~ (v1_funct_1 @ X15)
% 0.51/0.70          | ~ (v1_relat_1 @ X15))),
% 0.51/0.70      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.51/0.70  thf('140', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.70         (~ (r1_tarski @ X2 @ (k9_relat_1 @ X1 @ X0))
% 0.51/0.70          | ~ (v1_relat_1 @ X1)
% 0.51/0.70          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.51/0.70          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.51/0.70          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.51/0.70              (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)) = (X2)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['138', '139'])).
% 0.51/0.70  thf('141', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (r1_tarski @ X0 @ (k2_relat_1 @ sk_C))
% 0.51/0.70          | ((k9_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.51/0.70              (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ X0)) = (X0))
% 0.51/0.70          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.51/0.70          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.51/0.70          | ~ (v1_relat_1 @ sk_C))),
% 0.51/0.70      inference('sup-', [status(thm)], ['137', '140'])).
% 0.51/0.70  thf('142', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.51/0.70      inference('demod', [status(thm)], ['131', '132'])).
% 0.51/0.70  thf('143', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.51/0.70      inference('demod', [status(thm)], ['131', '132'])).
% 0.51/0.70  thf('144', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.51/0.70      inference('demod', [status(thm)], ['131', '132'])).
% 0.51/0.70  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('146', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.51/0.70      inference('demod', [status(thm)], ['131', '132'])).
% 0.51/0.70  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['65', '66'])).
% 0.51/0.70  thf('148', plain, ((v1_relat_1 @ sk_C)),
% 0.51/0.70      inference('demod', [status(thm)], ['65', '66'])).
% 0.51/0.70  thf('149', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (r1_tarski @ X0 @ (k2_relat_1 @ sk_C))
% 0.51/0.70          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.51/0.70      inference('demod', [status(thm)],
% 0.51/0.70                ['141', '142', '143', '144', '145', '146', '147', '148'])).
% 0.51/0.70  thf('150', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['80', '81', '84'])).
% 0.51/0.70  thf('151', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (r1_tarski @ X0 @ sk_A)
% 0.51/0.70          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.51/0.70      inference('demod', [status(thm)], ['149', '150'])).
% 0.51/0.70  thf('152', plain,
% 0.51/0.70      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 0.51/0.70      inference('sup-', [status(thm)], ['122', '151'])).
% 0.51/0.70  thf('153', plain,
% 0.51/0.70      ((((sk_B) != (sk_B)))
% 0.51/0.70         <= (~
% 0.51/0.70             (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.51/0.70                (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))))),
% 0.51/0.70      inference('demod', [status(thm)], ['120', '121', '152'])).
% 0.51/0.70  thf('154', plain,
% 0.51/0.70      ((((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.51/0.70          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.51/0.70      inference('simplify', [status(thm)], ['153'])).
% 0.51/0.70  thf('155', plain,
% 0.51/0.70      (~
% 0.51/0.70       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.51/0.70          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B))) | 
% 0.51/0.70       ~
% 0.51/0.70       (((k7_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.51/0.70          (k8_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.51/0.70      inference('split', [status(esa)], ['114'])).
% 0.51/0.70  thf('156', plain,
% 0.51/0.70      (~
% 0.51/0.70       (((k8_relset_1 @ sk_A @ sk_A @ sk_C @ 
% 0.51/0.70          (k7_relset_1 @ sk_A @ sk_A @ sk_C @ sk_B)) = (sk_B)))),
% 0.51/0.70      inference('sat_resolution*', [status(thm)], ['154', '155'])).
% 0.51/0.70  thf('157', plain,
% 0.51/0.70      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) != (sk_B))),
% 0.51/0.70      inference('simpl_trail', [status(thm)], ['117', '156'])).
% 0.51/0.70  thf('158', plain, ($false),
% 0.51/0.70      inference('simplify_reflect-', [status(thm)], ['107', '157'])).
% 0.51/0.70  
% 0.51/0.70  % SZS output end Refutation
% 0.51/0.70  
% 0.51/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
