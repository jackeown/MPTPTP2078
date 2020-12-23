%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KhU8cEPJUP

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 147 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  611 (1383 expanded)
%              Number of equality atoms :   24 (  48 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k6_relat_1 @ sk_B ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X15: $i] :
      ( ( r1_tarski @ X15 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k6_relat_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k6_relat_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,
    ( ( r1_tarski @ ( k6_relat_1 @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) )
    | ( r1_tarski @ ( k6_relat_1 @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('31',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('32',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('33',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B
     != ( k2_relat_1 @ sk_C_1 ) )
   <= ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('42',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v4_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('47',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('48',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('50',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('51',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['35'])).

thf('53',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['35'])).

thf('56',plain,(
    sk_B
 != ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    sk_B
 != ( k2_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['40','56'])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KhU8cEPJUP
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:25:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 180 iterations in 0.095s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.56  thf(t32_relset_1, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.21/0.56         ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) ) & 
% 0.21/0.56           ( ( B ) = ( k2_relset_1 @ A @ B @ C ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.56        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56          ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.21/0.56            ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) ) & 
% 0.21/0.56              ( ( B ) = ( k2_relset_1 @ A @ B @ C ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t32_relset_1])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(cc2_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.56         ((v5_relat_1 @ X21 @ X23)
% 0.21/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.56  thf('2', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.56  thf(d19_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ B ) =>
% 0.21/0.56       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i]:
% 0.21/0.56         (~ (v5_relat_1 @ X12 @ X13)
% 0.21/0.56          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.21/0.56          | ~ (v1_relat_1 @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(cc1_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( v1_relat_1 @ C ) ))).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.56         ((v1_relat_1 @ X18)
% 0.21/0.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.56  thf('7', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.56  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.21/0.56      inference('demod', [status(thm)], ['4', '7'])).
% 0.21/0.56  thf(d10_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X4 : $i, X6 : $i]:
% 0.21/0.56         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.21/0.56        | ((sk_B) = (k2_relat_1 @ sk_C_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.56  thf(d3_tarski, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X1 : $i, X3 : $i]:
% 0.21/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('12', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.56          | (r2_hidden @ X0 @ X2)
% 0.21/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ (k6_relat_1 @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_tarski @ (k6_relat_1 @ sk_B) @ X0)
% 0.21/0.56          | (r2_hidden @ (sk_C @ X0 @ (k6_relat_1 @ sk_B)) @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['11', '14'])).
% 0.21/0.56  thf(t21_relat_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ A ) =>
% 0.21/0.56       ( r1_tarski @
% 0.21/0.56         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X15 : $i]:
% 0.21/0.56         ((r1_tarski @ X15 @ 
% 0.21/0.56           (k2_zfmisc_1 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)))
% 0.21/0.56          | ~ (v1_relat_1 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.56          | (r2_hidden @ X0 @ X2)
% 0.21/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X0)
% 0.21/0.56          | (r2_hidden @ X1 @ 
% 0.21/0.56             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.21/0.56          | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_tarski @ (k6_relat_1 @ sk_B) @ X0)
% 0.21/0.56          | (r2_hidden @ (sk_C @ X0 @ (k6_relat_1 @ sk_B)) @ 
% 0.21/0.56             (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1)))
% 0.21/0.56          | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.56  thf('20', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_tarski @ (k6_relat_1 @ sk_B) @ X0)
% 0.21/0.56          | (r2_hidden @ (sk_C @ X0 @ (k6_relat_1 @ sk_B)) @ 
% 0.21/0.56             (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1))))),
% 0.21/0.56      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X1 : $i, X3 : $i]:
% 0.21/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (((r1_tarski @ (k6_relat_1 @ sk_B) @ 
% 0.21/0.56         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1)))
% 0.21/0.56        | (r1_tarski @ (k6_relat_1 @ sk_B) @ 
% 0.21/0.56           (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      ((r1_tarski @ (k6_relat_1 @ sk_B) @ 
% 0.21/0.56        (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.56  thf(t3_subset, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X7 : $i, X9 : $i]:
% 0.21/0.56         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      ((m1_subset_1 @ (k6_relat_1 @ sk_B) @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.56         ((v5_relat_1 @ X21 @ X23)
% 0.21/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      ((v5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i]:
% 0.21/0.56         (~ (v5_relat_1 @ X12 @ X13)
% 0.21/0.56          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.21/0.56          | ~ (v1_relat_1 @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.21/0.56        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_B)) @ 
% 0.21/0.56           (k2_relat_1 @ sk_C_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.56  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.56  thf('31', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.56  thf(t71_relat_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.56       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.56  thf('32', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.56  thf('33', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.56  thf('34', plain, (((sk_B) = (k2_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['10', '33'])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      ((~ (r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))
% 0.21/0.56        | ((sk_B) != (k2_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      ((((sk_B) != (k2_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.21/0.56         <= (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.56      inference('split', [status(esa)], ['35'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.56         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.21/0.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      ((((sk_B) != (k2_relat_1 @ sk_C_1)))
% 0.21/0.56         <= (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.56      inference('demod', [status(thm)], ['36', '39'])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      ((m1_subset_1 @ (k6_relat_1 @ sk_B) @ 
% 0.21/0.56        (k1_zfmisc_1 @ 
% 0.21/0.56         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.56         ((v4_relat_1 @ X21 @ X22)
% 0.21/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.21/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      ((v4_relat_1 @ (k6_relat_1 @ sk_B) @ (k1_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.56  thf(d18_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( v1_relat_1 @ B ) =>
% 0.21/0.56       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i]:
% 0.21/0.56         (~ (v4_relat_1 @ X10 @ X11)
% 0.21/0.56          | (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.21/0.56          | ~ (v1_relat_1 @ X10))),
% 0.21/0.56      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.21/0.56        | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_B)) @ 
% 0.21/0.56           (k1_relat_1 @ sk_C_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('46', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.56  thf('47', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 0.21/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.56  thf('48', plain, ((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.56  thf('50', plain,
% 0.21/0.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.56         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.21/0.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.21/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.56  thf('51', plain,
% 0.21/0.56      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      ((~ (r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.21/0.56         <= (~ ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.56      inference('split', [status(esa)], ['35'])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_1)))
% 0.21/0.56         <= (~ ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      (((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['48', '53'])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 0.21/0.56       ~ ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.56      inference('split', [status(esa)], ['35'])).
% 0.21/0.56  thf('56', plain, (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.21/0.56      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 0.21/0.56  thf('57', plain, (((sk_B) != (k2_relat_1 @ sk_C_1))),
% 0.21/0.56      inference('simpl_trail', [status(thm)], ['40', '56'])).
% 0.21/0.56  thf('58', plain, ($false),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['34', '57'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
