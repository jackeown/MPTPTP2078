%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qph5yN9aRd

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:07 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 301 expanded)
%              Number of leaves         :   36 ( 106 expanded)
%              Depth                    :   19
%              Number of atoms          :  722 (3213 expanded)
%              Number of equality atoms :   43 ( 120 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ( ( k7_relset_1 @ X56 @ X57 @ X55 @ X58 )
        = ( k9_relat_1 @ X55 @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( v4_relat_1 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v4_relat_1 @ X37 @ X38 )
      | ( r1_tarski @ ( k1_relat_1 @ X37 ) @ X38 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_relat_1 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X39: $i,X40: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33
        = ( k1_tarski @ X32 ) )
      | ( X33 = k1_xboole_0 )
      | ~ ( r1_tarski @ X33 @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('17',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X50: $i,X51: $i] :
      ( ( ( k1_relat_1 @ X51 )
       != ( k1_tarski @ X50 ) )
      | ( ( k2_relat_1 @ X51 )
        = ( k1_tarski @ ( k1_funct_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['19'])).

thf('21',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('23',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X41 @ X42 ) )
        = ( k9_relat_1 @ X41 @ X42 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('27',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X48 @ X49 ) @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('29',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ~ ( r1_tarski @ X59 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_relat_1 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X39: $i,X40: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X48 @ X49 ) @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_relat_1 @ X45 )
      | ( r1_tarski @ ( k2_relat_1 @ X46 ) @ ( k2_relat_1 @ X45 ) )
      | ~ ( r1_tarski @ X46 @ X45 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['26','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','47'])).

thf('49',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X37 ) @ X38 )
      | ( v4_relat_1 @ X37 @ X38 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('51',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('53',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_D @ X0 ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X43: $i,X44: $i] :
      ( ( X43
        = ( k7_relat_1 @ X43 @ X44 ) )
      | ~ ( v4_relat_1 @ X43 @ X44 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( sk_D
        = ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('57',plain,(
    ! [X0: $i] :
      ( sk_D
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X41 @ X42 ) )
        = ( k9_relat_1 @ X41 @ X42 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = ( k9_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','47'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('61',plain,(
    ! [X47: $i] :
      ( ( ( k1_relat_1 @ X47 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X47 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('67',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['59','65','66'])).

thf('68',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['4','67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qph5yN9aRd
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.76  % Solved by: fo/fo7.sh
% 0.51/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.76  % done 615 iterations in 0.302s
% 0.51/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.76  % SZS output start Refutation
% 0.51/0.76  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.51/0.76  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.51/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.76  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.51/0.76  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.51/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.76  thf(sk_D_type, type, sk_D: $i).
% 0.51/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.76  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.58/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.76  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.76  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.76  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.58/0.76  thf(t64_funct_2, conjecture,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.58/0.76         ( m1_subset_1 @
% 0.58/0.76           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.58/0.76       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.58/0.76         ( r1_tarski @
% 0.58/0.76           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.58/0.76           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.58/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.76    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.58/0.76            ( m1_subset_1 @
% 0.58/0.76              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.58/0.76          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.58/0.76            ( r1_tarski @
% 0.58/0.76              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.58/0.76              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.58/0.76    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.58/0.76  thf('0', plain,
% 0.58/0.76      (~ (r1_tarski @ 
% 0.58/0.76          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.58/0.76          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('1', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ 
% 0.58/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(redefinition_k7_relset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.58/0.76  thf('2', plain,
% 0.58/0.76      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 0.58/0.76          | ((k7_relset_1 @ X56 @ X57 @ X55 @ X58) = (k9_relat_1 @ X55 @ X58)))),
% 0.58/0.76      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.58/0.76  thf('3', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.58/0.76           = (k9_relat_1 @ sk_D @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.76  thf('4', plain,
% 0.58/0.76      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.58/0.76          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.58/0.76      inference('demod', [status(thm)], ['0', '3'])).
% 0.58/0.76  thf('5', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ 
% 0.58/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(cc2_relset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.76       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.58/0.76  thf('6', plain,
% 0.58/0.76      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.58/0.76         ((v4_relat_1 @ X52 @ X53)
% 0.58/0.76          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54))))),
% 0.58/0.76      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.58/0.76  thf('7', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.76  thf(d18_relat_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( v1_relat_1 @ B ) =>
% 0.58/0.76       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.58/0.76  thf('8', plain,
% 0.58/0.76      (![X37 : $i, X38 : $i]:
% 0.58/0.76         (~ (v4_relat_1 @ X37 @ X38)
% 0.58/0.76          | (r1_tarski @ (k1_relat_1 @ X37) @ X38)
% 0.58/0.76          | ~ (v1_relat_1 @ X37))),
% 0.58/0.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.58/0.76  thf('9', plain,
% 0.58/0.76      ((~ (v1_relat_1 @ sk_D)
% 0.58/0.76        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.58/0.76  thf('10', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ 
% 0.58/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(cc2_relat_1, axiom,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ( v1_relat_1 @ A ) =>
% 0.58/0.76       ( ![B:$i]:
% 0.58/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.58/0.76  thf('11', plain,
% 0.58/0.76      (![X35 : $i, X36 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.58/0.76          | (v1_relat_1 @ X35)
% 0.58/0.76          | ~ (v1_relat_1 @ X36))),
% 0.58/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.58/0.76  thf('12', plain,
% 0.58/0.76      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.58/0.76        | (v1_relat_1 @ sk_D))),
% 0.58/0.76      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.76  thf(fc6_relat_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.58/0.76  thf('13', plain,
% 0.58/0.76      (![X39 : $i, X40 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X39 @ X40))),
% 0.58/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.58/0.76  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.76      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.76  thf('15', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.58/0.76      inference('demod', [status(thm)], ['9', '14'])).
% 0.58/0.76  thf(l3_zfmisc_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.58/0.76       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.58/0.76  thf('16', plain,
% 0.58/0.76      (![X32 : $i, X33 : $i]:
% 0.58/0.76         (((X33) = (k1_tarski @ X32))
% 0.58/0.76          | ((X33) = (k1_xboole_0))
% 0.58/0.76          | ~ (r1_tarski @ X33 @ (k1_tarski @ X32)))),
% 0.58/0.76      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.58/0.76  thf('17', plain,
% 0.58/0.76      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.58/0.76        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.76  thf(t14_funct_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.76       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.58/0.76         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.58/0.76  thf('18', plain,
% 0.58/0.76      (![X50 : $i, X51 : $i]:
% 0.58/0.76         (((k1_relat_1 @ X51) != (k1_tarski @ X50))
% 0.58/0.76          | ((k2_relat_1 @ X51) = (k1_tarski @ (k1_funct_1 @ X51 @ X50)))
% 0.58/0.76          | ~ (v1_funct_1 @ X51)
% 0.58/0.76          | ~ (v1_relat_1 @ X51))),
% 0.58/0.76      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.58/0.76  thf('19', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.58/0.76          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.58/0.76          | ~ (v1_relat_1 @ X0)
% 0.58/0.76          | ~ (v1_funct_1 @ X0)
% 0.58/0.76          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.58/0.76      inference('sup-', [status(thm)], ['17', '18'])).
% 0.58/0.76  thf('20', plain,
% 0.58/0.76      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.58/0.76        | ~ (v1_funct_1 @ sk_D)
% 0.58/0.76        | ~ (v1_relat_1 @ sk_D)
% 0.58/0.76        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.58/0.76      inference('eq_res', [status(thm)], ['19'])).
% 0.58/0.76  thf('21', plain, ((v1_funct_1 @ sk_D)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.76      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.76  thf('23', plain,
% 0.58/0.76      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.58/0.76        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.58/0.76      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.58/0.76  thf('24', plain,
% 0.58/0.76      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.58/0.76          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.58/0.76      inference('demod', [status(thm)], ['0', '3'])).
% 0.58/0.76  thf('25', plain,
% 0.58/0.76      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.58/0.76        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.76  thf(t148_relat_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( v1_relat_1 @ B ) =>
% 0.58/0.76       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.58/0.76  thf('26', plain,
% 0.58/0.76      (![X41 : $i, X42 : $i]:
% 0.58/0.76         (((k2_relat_1 @ (k7_relat_1 @ X41 @ X42)) = (k9_relat_1 @ X41 @ X42))
% 0.58/0.76          | ~ (v1_relat_1 @ X41))),
% 0.58/0.76      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.58/0.76  thf(t88_relat_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.58/0.76  thf('27', plain,
% 0.58/0.76      (![X48 : $i, X49 : $i]:
% 0.58/0.76         ((r1_tarski @ (k7_relat_1 @ X48 @ X49) @ X48) | ~ (v1_relat_1 @ X48))),
% 0.58/0.76      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.58/0.76  thf('28', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_D @ 
% 0.58/0.76        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(t4_relset_1, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.58/0.76       ( ( r1_tarski @ A @ D ) =>
% 0.58/0.76         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.58/0.76  thf('29', plain,
% 0.58/0.76      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 0.58/0.76         ((m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 0.58/0.76          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 0.58/0.76          | ~ (r1_tarski @ X59 @ X62))),
% 0.58/0.76      inference('cnf', [status(esa)], [t4_relset_1])).
% 0.58/0.76  thf('30', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (~ (r1_tarski @ X0 @ sk_D)
% 0.58/0.76          | (m1_subset_1 @ X0 @ 
% 0.58/0.76             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))))),
% 0.58/0.76      inference('sup-', [status(thm)], ['28', '29'])).
% 0.58/0.76  thf('31', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (~ (v1_relat_1 @ sk_D)
% 0.58/0.76          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.58/0.76             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))))),
% 0.58/0.76      inference('sup-', [status(thm)], ['27', '30'])).
% 0.58/0.76  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.76      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.76  thf('33', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.58/0.76          (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.76      inference('demod', [status(thm)], ['31', '32'])).
% 0.58/0.76  thf('34', plain,
% 0.58/0.76      (![X35 : $i, X36 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.58/0.76          | (v1_relat_1 @ X35)
% 0.58/0.76          | ~ (v1_relat_1 @ X36))),
% 0.58/0.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.58/0.76  thf('35', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.58/0.76          | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['33', '34'])).
% 0.58/0.76  thf('36', plain,
% 0.58/0.76      (![X39 : $i, X40 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X39 @ X40))),
% 0.58/0.76      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.58/0.76  thf('37', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['35', '36'])).
% 0.58/0.76  thf('38', plain,
% 0.58/0.76      (![X48 : $i, X49 : $i]:
% 0.58/0.76         ((r1_tarski @ (k7_relat_1 @ X48 @ X49) @ X48) | ~ (v1_relat_1 @ X48))),
% 0.58/0.76      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.58/0.76  thf(t25_relat_1, axiom,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ( v1_relat_1 @ A ) =>
% 0.58/0.76       ( ![B:$i]:
% 0.58/0.76         ( ( v1_relat_1 @ B ) =>
% 0.58/0.76           ( ( r1_tarski @ A @ B ) =>
% 0.58/0.76             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.58/0.76               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.58/0.76  thf('39', plain,
% 0.58/0.76      (![X45 : $i, X46 : $i]:
% 0.58/0.76         (~ (v1_relat_1 @ X45)
% 0.58/0.76          | (r1_tarski @ (k2_relat_1 @ X46) @ (k2_relat_1 @ X45))
% 0.58/0.76          | ~ (r1_tarski @ X46 @ X45)
% 0.58/0.76          | ~ (v1_relat_1 @ X46))),
% 0.58/0.76      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.58/0.76  thf('40', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         (~ (v1_relat_1 @ X0)
% 0.58/0.76          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.58/0.76          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.58/0.76             (k2_relat_1 @ X0))
% 0.58/0.76          | ~ (v1_relat_1 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.76  thf('41', plain,
% 0.58/0.76      (![X0 : $i, X1 : $i]:
% 0.58/0.76         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.58/0.76           (k2_relat_1 @ X0))
% 0.58/0.76          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.58/0.76          | ~ (v1_relat_1 @ X0))),
% 0.58/0.76      inference('simplify', [status(thm)], ['40'])).
% 0.58/0.76  thf('42', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (~ (v1_relat_1 @ sk_D)
% 0.58/0.76          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.58/0.76             (k2_relat_1 @ sk_D)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['37', '41'])).
% 0.58/0.76  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.76      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.76  thf('44', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.58/0.76          (k2_relat_1 @ sk_D))),
% 0.58/0.76      inference('demod', [status(thm)], ['42', '43'])).
% 0.58/0.76  thf('45', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 0.58/0.76          | ~ (v1_relat_1 @ sk_D))),
% 0.58/0.76      inference('sup+', [status(thm)], ['26', '44'])).
% 0.58/0.76  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.76      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.76  thf('47', plain,
% 0.58/0.76      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 0.58/0.76      inference('demod', [status(thm)], ['45', '46'])).
% 0.58/0.76  thf('48', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.58/0.76      inference('demod', [status(thm)], ['25', '47'])).
% 0.58/0.76  thf('49', plain,
% 0.58/0.76      (![X37 : $i, X38 : $i]:
% 0.58/0.76         (~ (r1_tarski @ (k1_relat_1 @ X37) @ X38)
% 0.58/0.76          | (v4_relat_1 @ X37 @ X38)
% 0.58/0.76          | ~ (v1_relat_1 @ X37))),
% 0.58/0.76      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.58/0.76  thf('50', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.58/0.76          | ~ (v1_relat_1 @ sk_D)
% 0.58/0.76          | (v4_relat_1 @ sk_D @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.76  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.58/0.76  thf('51', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.58/0.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.76  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.76      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.76  thf('53', plain, (![X0 : $i]: (v4_relat_1 @ sk_D @ X0)),
% 0.58/0.76      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.58/0.76  thf(t209_relat_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.58/0.76       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.58/0.76  thf('54', plain,
% 0.58/0.76      (![X43 : $i, X44 : $i]:
% 0.58/0.76         (((X43) = (k7_relat_1 @ X43 @ X44))
% 0.58/0.76          | ~ (v4_relat_1 @ X43 @ X44)
% 0.58/0.76          | ~ (v1_relat_1 @ X43))),
% 0.58/0.76      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.58/0.76  thf('55', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ X0)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['53', '54'])).
% 0.58/0.76  thf('56', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.76      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.76  thf('57', plain, (![X0 : $i]: ((sk_D) = (k7_relat_1 @ sk_D @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['55', '56'])).
% 0.58/0.76  thf('58', plain,
% 0.58/0.76      (![X41 : $i, X42 : $i]:
% 0.58/0.76         (((k2_relat_1 @ (k7_relat_1 @ X41 @ X42)) = (k9_relat_1 @ X41 @ X42))
% 0.58/0.76          | ~ (v1_relat_1 @ X41))),
% 0.58/0.76      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.58/0.76  thf('59', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ X0))
% 0.58/0.76          | ~ (v1_relat_1 @ sk_D))),
% 0.58/0.76      inference('sup+', [status(thm)], ['57', '58'])).
% 0.58/0.76  thf('60', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.58/0.76      inference('demod', [status(thm)], ['25', '47'])).
% 0.58/0.76  thf(t65_relat_1, axiom,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ( v1_relat_1 @ A ) =>
% 0.58/0.76       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.58/0.76         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.58/0.76  thf('61', plain,
% 0.58/0.76      (![X47 : $i]:
% 0.58/0.76         (((k1_relat_1 @ X47) != (k1_xboole_0))
% 0.58/0.76          | ((k2_relat_1 @ X47) = (k1_xboole_0))
% 0.58/0.76          | ~ (v1_relat_1 @ X47))),
% 0.58/0.76      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.58/0.76  thf('62', plain,
% 0.58/0.76      ((((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.76        | ~ (v1_relat_1 @ sk_D)
% 0.58/0.76        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['60', '61'])).
% 0.58/0.76  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.76      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.76  thf('64', plain,
% 0.58/0.76      ((((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.76        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.58/0.76      inference('demod', [status(thm)], ['62', '63'])).
% 0.58/0.76  thf('65', plain, (((k2_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.58/0.76      inference('simplify', [status(thm)], ['64'])).
% 0.58/0.76  thf('66', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.76      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.76  thf('67', plain, (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ sk_D @ X0))),
% 0.58/0.76      inference('demod', [status(thm)], ['59', '65', '66'])).
% 0.58/0.76  thf('68', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.58/0.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.76  thf('69', plain, ($false),
% 0.58/0.76      inference('demod', [status(thm)], ['4', '67', '68'])).
% 0.58/0.76  
% 0.58/0.76  % SZS output end Refutation
% 0.58/0.76  
% 0.60/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
