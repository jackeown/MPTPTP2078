%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dn8ZSzJCc1

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 167 expanded)
%              Number of leaves         :   37 (  67 expanded)
%              Depth                    :   17
%              Number of atoms          :  803 (1544 expanded)
%              Number of equality atoms :   51 (  89 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X29: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X29 ) @ X29 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(t32_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C )
       => ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) )
          & ( B
            = ( k2_relset_1 @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C )
         => ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) )
            & ( B
              = ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_relset_1])).

thf('1',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
       => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
          & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('3',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X39 ) @ X40 )
      | ( r1_tarski @ X39 @ ( k2_relset_1 @ X41 @ X42 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[t30_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf(t217_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ( v4_relat_1 @ X21 @ X23 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v4_relat_1 @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( v4_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('14',plain,(
    v4_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( ( k6_relat_1 @ sk_B )
      = ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k7_relat_1 @ X27 @ X26 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X27 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X32 ) @ ( k6_relat_1 @ X31 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X29: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X29 ) @ X29 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v5_relat_1 @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ( v4_relat_1 @ X21 @ X23 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ sk_B )
      | ~ ( v4_relat_1 @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( v4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','36'])).

thf('38',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('39',plain,(
    v4_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('43',plain,
    ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
    = ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('45',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('46',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('47',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('50',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('53',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('56',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','54','59'])).

thf('61',plain,
    ( ( k6_relat_1 @ sk_B )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17','22','60'])).

thf('62',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('63',plain,
    ( ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('65',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('69',plain,
    ( ( sk_B
     != ( k2_relat_1 @ sk_C ) )
   <= ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X39 ) @ X40 )
      | ( r1_tarski @ X39 @ ( k1_relset_1 @ X41 @ X42 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[t30_relset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['66'])).

thf('76',plain,(
    r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['66'])).

thf('78',plain,(
    sk_B
 != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['76','77'])).

thf('79',plain,(
    sk_B
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['69','78'])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dn8ZSzJCc1
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:00:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 101 iterations in 0.047s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(fc24_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.51       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.21/0.51       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.51  thf('0', plain, (![X29 : $i]: (v4_relat_1 @ (k6_relat_1 @ X29) @ X29)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.51  thf(t32_relset_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.21/0.51         ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) ) & 
% 0.21/0.51           ( ( B ) = ( k2_relset_1 @ A @ B @ C ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51          ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.21/0.51            ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) ) & 
% 0.21/0.51              ( ( B ) = ( k2_relset_1 @ A @ B @ C ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t32_relset_1])).
% 0.21/0.51  thf('1', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t30_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.21/0.51         ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.21/0.51           ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k6_relat_1 @ X39) @ X40)
% 0.21/0.51          | (r1_tarski @ X39 @ (k2_relset_1 @ X41 @ X42 @ X40))
% 0.21/0.51          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.21/0.51      inference('cnf', [status(esa)], [t30_relset_1])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ X0 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.21/0.51          | ~ (r1_tarski @ (k6_relat_1 @ X0) @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.21/0.51         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 0.21/0.51          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.51  thf('7', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ X0 @ (k2_relat_1 @ sk_C))
% 0.21/0.51          | ~ (r1_tarski @ (k6_relat_1 @ X0) @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '7'])).
% 0.21/0.51  thf('9', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '8'])).
% 0.21/0.51  thf(t217_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.51       ( ![C:$i]:
% 0.21/0.51         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 0.21/0.51           ( v4_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X21)
% 0.21/0.51          | ~ (v4_relat_1 @ X21 @ X22)
% 0.21/0.51          | (v4_relat_1 @ X21 @ X23)
% 0.21/0.51          | ~ (r1_tarski @ X22 @ X23))),
% 0.21/0.51      inference('cnf', [status(esa)], [t217_relat_1])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v4_relat_1 @ X0 @ (k2_relat_1 @ sk_C))
% 0.21/0.51          | ~ (v4_relat_1 @ X0 @ sk_B)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.21/0.51        | (v4_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '11'])).
% 0.21/0.51  thf('13', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.51  thf('14', plain, ((v4_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf(t209_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.51       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i]:
% 0.21/0.51         (((X19) = (k7_relat_1 @ X19 @ X20))
% 0.21/0.51          | ~ (v4_relat_1 @ X19 @ X20)
% 0.21/0.51          | ~ (v1_relat_1 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.21/0.51        | ((k6_relat_1 @ sk_B)
% 0.21/0.51            = (k7_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.51  thf(t94_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X26 : $i, X27 : $i]:
% 0.21/0.51         (((k7_relat_1 @ X27 @ X26) = (k5_relat_1 @ (k6_relat_1 @ X26) @ X27))
% 0.21/0.51          | ~ (v1_relat_1 @ X27))),
% 0.21/0.51      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.21/0.51  thf(t43_funct_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.21/0.51       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X31 : $i, X32 : $i]:
% 0.21/0.51         ((k5_relat_1 @ (k6_relat_1 @ X32) @ (k6_relat_1 @ X31))
% 0.21/0.51           = (k6_relat_1 @ (k3_xboole_0 @ X31 @ X32)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.51            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.51           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('23', plain, (![X29 : $i]: (v4_relat_1 @ (k6_relat_1 @ X29) @ X29)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.51         ((v5_relat_1 @ X33 @ X35)
% 0.21/0.51          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.51  thf('26', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf(d19_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (v5_relat_1 @ X11 @ X12)
% 0.21/0.51          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.21/0.51          | ~ (v1_relat_1 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc2_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.21/0.51          | (v1_relat_1 @ X9)
% 0.21/0.51          | ~ (v1_relat_1 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf(fc6_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.51  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['28', '33'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X21)
% 0.21/0.51          | ~ (v4_relat_1 @ X21 @ X22)
% 0.21/0.51          | (v4_relat_1 @ X21 @ X23)
% 0.21/0.51          | ~ (r1_tarski @ X22 @ X23))),
% 0.21/0.51      inference('cnf', [status(esa)], [t217_relat_1])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v4_relat_1 @ X0 @ sk_B)
% 0.21/0.51          | ~ (v4_relat_1 @ X0 @ (k2_relat_1 @ sk_C))
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.21/0.51        | (v4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '36'])).
% 0.21/0.51  thf('38', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.51  thf('39', plain, ((v4_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i]:
% 0.21/0.51         (((X19) = (k7_relat_1 @ X19 @ X20))
% 0.21/0.51          | ~ (v4_relat_1 @ X19 @ X20)
% 0.21/0.51          | ~ (v1_relat_1 @ X19))),
% 0.21/0.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.21/0.51        | ((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.21/0.51            = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.51  thf('42', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.21/0.51         = (k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf(t148_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i]:
% 0.21/0.51         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 0.21/0.51          | ~ (v1_relat_1 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      ((((k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.21/0.51          = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))
% 0.21/0.51        | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C))))),
% 0.21/0.51      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.51  thf(t71_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.51       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.51  thf('46', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 0.21/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.51  thf('47', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (((k2_relat_1 @ sk_C)
% 0.21/0.51         = (k9_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)) @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.51  thf('49', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.21/0.51           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i]:
% 0.21/0.51         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 0.21/0.51          | ~ (v1_relat_1 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.51            = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['49', '50'])).
% 0.21/0.51  thf('52', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 0.21/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.51  thf('53', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.21/0.51  thf(commutativity_k2_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.51  thf(t12_setfam_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.51  thf('56', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]:
% 0.21/0.51         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['55', '56'])).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i]:
% 0.21/0.51         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['57', '58'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (((k2_relat_1 @ sk_C) = (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['48', '54', '59'])).
% 0.21/0.51  thf('61', plain,
% 0.21/0.51      (((k6_relat_1 @ sk_B) = (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '17', '22', '60'])).
% 0.21/0.51  thf('62', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 0.21/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (((k1_relat_1 @ (k6_relat_1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup+', [status(thm)], ['61', '62'])).
% 0.21/0.51  thf('64', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 0.21/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.51  thf('65', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      ((~ (r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.21/0.51        | ((sk_B) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      ((((sk_B) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.21/0.51         <= (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.21/0.51      inference('split', [status(esa)], ['66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      ((((sk_B) != (k2_relat_1 @ sk_C)))
% 0.21/0.51         <= (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.21/0.51      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.51  thf('70', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('72', plain,
% 0.21/0.51      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.51         (~ (r1_tarski @ (k6_relat_1 @ X39) @ X40)
% 0.21/0.51          | (r1_tarski @ X39 @ (k1_relset_1 @ X41 @ X42 @ X40))
% 0.21/0.51          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.21/0.51      inference('cnf', [status(esa)], [t30_relset_1])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r1_tarski @ X0 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.21/0.51          | ~ (r1_tarski @ (k6_relat_1 @ X0) @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.51  thf('74', plain, ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['70', '73'])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      ((~ (r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.21/0.51         <= (~ ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.21/0.51      inference('split', [status(esa)], ['66'])).
% 0.21/0.51  thf('76', plain, (((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.21/0.51       ~ ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['66'])).
% 0.21/0.51  thf('78', plain, (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['76', '77'])).
% 0.21/0.51  thf('79', plain, (((sk_B) != (k2_relat_1 @ sk_C))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['69', '78'])).
% 0.21/0.51  thf('80', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['65', '79'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
