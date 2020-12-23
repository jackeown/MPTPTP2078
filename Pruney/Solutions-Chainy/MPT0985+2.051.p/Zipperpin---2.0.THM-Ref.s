%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FnWRioKsRM

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:33 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  266 (3485 expanded)
%              Number of leaves         :   60 (1068 expanded)
%              Depth                    :   34
%              Number of atoms          : 1821 (54342 expanded)
%              Number of equality atoms :   91 (1945 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v1_relat_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( v4_relat_1 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('17',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X32: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k1_relat_1 @ X32 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('19',plain,(
    ! [X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('20',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('21',plain,(
    ! [X32: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relat_1 @ X32 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('22',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k2_relset_1 @ X44 @ X45 @ X43 )
        = ( k2_relat_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X32: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relat_1 @ X32 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v2_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('43',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['26','44'])).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('50',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_B ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('53',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X26 @ ( k2_relat_1 @ X27 ) )
      | ( ( k9_relat_1 @ X27 @ ( k10_relat_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('56',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['21','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('62',plain,(
    ! [X17: $i] :
      ( ( ( k10_relat_1 @ X17 @ ( k2_relat_1 @ X17 ) )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('63',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ sk_B )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('65',plain,
    ( ( k10_relat_1 @ sk_C_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('68',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k10_relat_1 @ sk_C_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('70',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    = sk_B ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('72',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['59','60','65','70','71','72','73'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X56: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('79',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['19','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('83',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['18','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('87',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('90',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X46 ) @ X47 )
      | ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X47 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    = sk_B ),
    inference(demod,[status(thm)],['68','69'])).

thf('93',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('94',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X29 ) @ ( k9_relat_1 @ X29 @ X28 ) )
        = X28 )
      | ~ ( v2_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('98',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['59','60','65','70','71','72','73'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('99',plain,(
    ! [X16: $i] :
      ( ( ( k9_relat_1 @ X16 @ ( k1_relat_1 @ X16 ) )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('100',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('103',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('108',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['96','104','105','106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['91','108'])).

thf('110',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','109'])).

thf('111',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('112',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('114',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['10','112','113'])).

thf('115',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','114'])).

thf('116',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['96','104','105','106','107'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('117',plain,(
    ! [X19: $i] :
      ( ( ( k2_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X19 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('118',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('120',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v1_relat_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('121',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['59','60','65','70','71','72','73'])).

thf('123',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['118','121','122'])).

thf('124',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('125',plain,(
    ! [X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('126',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf(t9_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
            & ( v1_funct_2 @ D @ A @ C )
            & ( v1_funct_1 @ D ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ A )
     => ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ A ) ) ) ) )).

thf('127',plain,(
    ! [X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ~ ( r1_tarski @ X62 @ X63 )
      | ( zip_tseitin_1 @ X62 @ X64 )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( v1_funct_2 @ X65 @ X64 @ X62 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X62 ) ) )
      | ( zip_tseitin_0 @ X65 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X32: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k1_relat_1 @ X32 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('130',plain,(
    ! [X23: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('131',plain,(
    ! [X23: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('132',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['59','60','65','70','71','72','73'])).

thf('133',plain,(
    ! [X56: $i] :
      ( ( v1_funct_2 @ X56 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('134',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['131','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('137',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['130','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('141',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['129','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('145',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['128','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['125','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('151',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ sk_B )
    | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['124','152'])).

thf('154',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( v1_funct_2 @ X57 @ X59 @ X58 )
      | ~ ( zip_tseitin_0 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('155',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','114'])).

thf('157',plain,(
    zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X60: $i,X61: $i] :
      ( ( X60 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('159',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','159'])).

thf('161',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['115','161'])).

thf('163',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['157','158'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('164',plain,(
    ! [X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('165',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('167',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['167'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('169',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('170',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('171',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['169','170'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('172',plain,(
    ! [X36: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X36 ) )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('173',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('174',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('175',plain,(
    ! [X36: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X36 ) )
      = ( k6_partfun1 @ X36 ) ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['171','175'])).

thf('177',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['169','170'])).

thf('178',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['169','170'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('180',plain,(
    ! [X53: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X53 ) @ X53 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('181',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('183',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['169','170'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('184',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('185',plain,(
    ! [X54: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X54 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('186',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['184','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['183','188'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('190',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('191',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['182','191'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('193',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('194',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('195',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_partfun1 @ X50 @ X51 )
      | ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['169','170'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('198',plain,(
    ! [X25: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('199',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('200',plain,(
    ! [X25: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X25 ) ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['197','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['196','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['181','202'])).

thf('204',plain,(
    $false ),
    inference(demod,[status(thm)],['162','168','178','203'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FnWRioKsRM
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:07:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.76/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.97  % Solved by: fo/fo7.sh
% 0.76/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.97  % done 1293 iterations in 0.513s
% 0.76/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.97  % SZS output start Refutation
% 0.76/0.97  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.97  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.76/0.97  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.76/0.97  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.76/0.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.97  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.97  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.76/0.97  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.76/0.97  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.76/0.97  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.97  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.97  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.76/0.97  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.76/0.97  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.76/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.97  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.76/0.97  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.76/0.97  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.76/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.97  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.76/0.97  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.76/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.97  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.97  thf(t31_funct_2, conjecture,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.97       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.76/0.97         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.76/0.97           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.76/0.97           ( m1_subset_1 @
% 0.76/0.97             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.76/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.97    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.97        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.97            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.97          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.76/0.97            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.76/0.97              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.76/0.97              ( m1_subset_1 @
% 0.76/0.97                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.76/0.97    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.76/0.97  thf('0', plain,
% 0.76/0.97      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.76/0.97        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 0.76/0.97        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('1', plain,
% 0.76/0.97      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 0.76/0.97         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.76/0.97      inference('split', [status(esa)], ['0'])).
% 0.76/0.97  thf('2', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(cc1_relset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.97       ( v1_relat_1 @ C ) ))).
% 0.76/0.97  thf('3', plain,
% 0.76/0.97      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.76/0.97         ((v1_relat_1 @ X37)
% 0.76/0.97          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.76/0.97      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/0.97  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf(dt_k2_funct_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.97       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.76/0.97         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.76/0.97  thf('5', plain,
% 0.76/0.97      (![X23 : $i]:
% 0.76/0.97         ((v1_funct_1 @ (k2_funct_1 @ X23))
% 0.76/0.97          | ~ (v1_funct_1 @ X23)
% 0.76/0.97          | ~ (v1_relat_1 @ X23))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.76/0.97  thf('6', plain,
% 0.76/0.97      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 0.76/0.97         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.76/0.97      inference('split', [status(esa)], ['0'])).
% 0.76/0.97  thf('7', plain,
% 0.76/0.97      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 0.76/0.97         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['5', '6'])).
% 0.76/0.97  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('9', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.76/0.97      inference('demod', [status(thm)], ['7', '8'])).
% 0.76/0.97  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['4', '9'])).
% 0.76/0.97  thf('11', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(cc2_relset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.97       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.76/0.97  thf('12', plain,
% 0.76/0.97      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.76/0.97         ((v4_relat_1 @ X40 @ X41)
% 0.76/0.97          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.76/0.97      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.97  thf('13', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.76/0.97      inference('sup-', [status(thm)], ['11', '12'])).
% 0.76/0.97  thf(d18_relat_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ B ) =>
% 0.76/0.97       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.76/0.97  thf('14', plain,
% 0.76/0.97      (![X12 : $i, X13 : $i]:
% 0.76/0.97         (~ (v4_relat_1 @ X12 @ X13)
% 0.76/0.97          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.76/0.97          | ~ (v1_relat_1 @ X12))),
% 0.76/0.97      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.76/0.97  thf('15', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['13', '14'])).
% 0.76/0.97  thf('16', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('17', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 0.76/0.97      inference('demod', [status(thm)], ['15', '16'])).
% 0.76/0.97  thf(t55_funct_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.97       ( ( v2_funct_1 @ A ) =>
% 0.76/0.97         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.76/0.97           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.76/0.97  thf('18', plain,
% 0.76/0.97      (![X32 : $i]:
% 0.76/0.97         (~ (v2_funct_1 @ X32)
% 0.76/0.97          | ((k1_relat_1 @ X32) = (k2_relat_1 @ (k2_funct_1 @ X32)))
% 0.76/0.97          | ~ (v1_funct_1 @ X32)
% 0.76/0.97          | ~ (v1_relat_1 @ X32))),
% 0.76/0.97      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.76/0.97  thf('19', plain,
% 0.76/0.97      (![X23 : $i]:
% 0.76/0.97         ((v1_funct_1 @ (k2_funct_1 @ X23))
% 0.76/0.97          | ~ (v1_funct_1 @ X23)
% 0.76/0.97          | ~ (v1_relat_1 @ X23))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.76/0.97  thf('20', plain,
% 0.76/0.97      (![X23 : $i]:
% 0.76/0.97         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 0.76/0.97          | ~ (v1_funct_1 @ X23)
% 0.76/0.97          | ~ (v1_relat_1 @ X23))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.76/0.97  thf('21', plain,
% 0.76/0.97      (![X32 : $i]:
% 0.76/0.97         (~ (v2_funct_1 @ X32)
% 0.76/0.97          | ((k2_relat_1 @ X32) = (k1_relat_1 @ (k2_funct_1 @ X32)))
% 0.76/0.97          | ~ (v1_funct_1 @ X32)
% 0.76/0.97          | ~ (v1_relat_1 @ X32))),
% 0.76/0.97      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.76/0.97  thf('22', plain,
% 0.76/0.97      (![X23 : $i]:
% 0.76/0.97         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 0.76/0.97          | ~ (v1_funct_1 @ X23)
% 0.76/0.97          | ~ (v1_relat_1 @ X23))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.76/0.97  thf(d3_tarski, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( r1_tarski @ A @ B ) <=>
% 0.76/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.76/0.97  thf('23', plain,
% 0.76/0.97      (![X1 : $i, X3 : $i]:
% 0.76/0.97         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.97  thf('24', plain,
% 0.76/0.97      (![X1 : $i, X3 : $i]:
% 0.76/0.97         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.97  thf('25', plain,
% 0.76/0.97      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['23', '24'])).
% 0.76/0.97  thf('26', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.76/0.97      inference('simplify', [status(thm)], ['25'])).
% 0.76/0.97  thf('27', plain,
% 0.76/0.97      (![X23 : $i]:
% 0.76/0.97         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 0.76/0.97          | ~ (v1_funct_1 @ X23)
% 0.76/0.97          | ~ (v1_relat_1 @ X23))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.76/0.97  thf('28', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(redefinition_k2_relset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.97       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.76/0.97  thf('29', plain,
% 0.76/0.97      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.76/0.97         (((k2_relset_1 @ X44 @ X45 @ X43) = (k2_relat_1 @ X43))
% 0.76/0.97          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/0.97  thf('30', plain,
% 0.76/0.97      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['28', '29'])).
% 0.76/0.97  thf('31', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('32', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.76/0.97      inference('sup+', [status(thm)], ['30', '31'])).
% 0.76/0.97  thf('33', plain,
% 0.76/0.97      (![X32 : $i]:
% 0.76/0.97         (~ (v2_funct_1 @ X32)
% 0.76/0.97          | ((k2_relat_1 @ X32) = (k1_relat_1 @ (k2_funct_1 @ X32)))
% 0.76/0.97          | ~ (v1_funct_1 @ X32)
% 0.76/0.97          | ~ (v1_relat_1 @ X32))),
% 0.76/0.97      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.76/0.97  thf('34', plain,
% 0.76/0.97      (![X12 : $i, X13 : $i]:
% 0.76/0.97         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.76/0.97          | (v4_relat_1 @ X12 @ X13)
% 0.76/0.97          | ~ (v1_relat_1 @ X12))),
% 0.76/0.97      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.76/0.97  thf('35', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.76/0.97          | ~ (v1_relat_1 @ X0)
% 0.76/0.97          | ~ (v1_funct_1 @ X0)
% 0.76/0.97          | ~ (v2_funct_1 @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.76/0.97          | (v4_relat_1 @ (k2_funct_1 @ X0) @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['33', '34'])).
% 0.76/0.97  thf('36', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (r1_tarski @ sk_B @ X0)
% 0.76/0.97          | (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.76/0.97          | ~ (v2_funct_1 @ sk_C_1)
% 0.76/0.97          | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.97          | ~ (v1_relat_1 @ sk_C_1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['32', '35'])).
% 0.76/0.97  thf('37', plain, ((v2_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('38', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('40', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (r1_tarski @ sk_B @ X0)
% 0.76/0.97          | (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.76/0.97      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.76/0.97  thf('41', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ sk_C_1)
% 0.76/0.97          | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.97          | (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0)
% 0.76/0.97          | ~ (r1_tarski @ sk_B @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['27', '40'])).
% 0.76/0.97  thf('42', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('43', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('44', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.76/0.97      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.76/0.97  thf('45', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_B)),
% 0.76/0.97      inference('sup-', [status(thm)], ['26', '44'])).
% 0.76/0.97  thf('46', plain,
% 0.76/0.97      (![X12 : $i, X13 : $i]:
% 0.76/0.97         (~ (v4_relat_1 @ X12 @ X13)
% 0.76/0.97          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.76/0.97          | ~ (v1_relat_1 @ X12))),
% 0.76/0.97      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.76/0.97  thf('47', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.76/0.97        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['45', '46'])).
% 0.76/0.97  thf('48', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ sk_C_1)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.97        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['22', '47'])).
% 0.76/0.97  thf('49', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('50', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('51', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_B)),
% 0.76/0.97      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.76/0.97  thf('52', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.76/0.97      inference('sup+', [status(thm)], ['30', '31'])).
% 0.76/0.97  thf(t147_funct_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.76/0.97       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.76/0.97         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.76/0.97  thf('53', plain,
% 0.76/0.97      (![X26 : $i, X27 : $i]:
% 0.76/0.97         (~ (r1_tarski @ X26 @ (k2_relat_1 @ X27))
% 0.76/0.97          | ((k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X26)) = (X26))
% 0.76/0.97          | ~ (v1_funct_1 @ X27)
% 0.76/0.97          | ~ (v1_relat_1 @ X27))),
% 0.76/0.97      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.76/0.97  thf('54', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (r1_tarski @ X0 @ sk_B)
% 0.76/0.97          | ~ (v1_relat_1 @ sk_C_1)
% 0.76/0.97          | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.97          | ((k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ X0)) = (X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['52', '53'])).
% 0.76/0.97  thf('55', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('56', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('57', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (r1_tarski @ X0 @ sk_B)
% 0.76/0.97          | ((k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ X0)) = (X0)))),
% 0.76/0.97      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.76/0.97  thf('58', plain,
% 0.76/0.97      (((k9_relat_1 @ sk_C_1 @ 
% 0.76/0.97         (k10_relat_1 @ sk_C_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1))))
% 0.76/0.97         = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['51', '57'])).
% 0.76/0.97  thf('59', plain,
% 0.76/0.97      ((((k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ (k2_relat_1 @ sk_C_1)))
% 0.76/0.97          = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 0.76/0.97        | ~ (v1_relat_1 @ sk_C_1)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.97        | ~ (v2_funct_1 @ sk_C_1))),
% 0.76/0.97      inference('sup+', [status(thm)], ['21', '58'])).
% 0.76/0.97  thf('60', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.76/0.97      inference('sup+', [status(thm)], ['30', '31'])).
% 0.76/0.97  thf('61', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.76/0.97      inference('sup+', [status(thm)], ['30', '31'])).
% 0.76/0.97  thf(t169_relat_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ A ) =>
% 0.76/0.97       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.76/0.97  thf('62', plain,
% 0.76/0.97      (![X17 : $i]:
% 0.76/0.97         (((k10_relat_1 @ X17 @ (k2_relat_1 @ X17)) = (k1_relat_1 @ X17))
% 0.76/0.97          | ~ (v1_relat_1 @ X17))),
% 0.76/0.97      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.76/0.97  thf('63', plain,
% 0.76/0.97      ((((k10_relat_1 @ sk_C_1 @ sk_B) = (k1_relat_1 @ sk_C_1))
% 0.76/0.97        | ~ (v1_relat_1 @ sk_C_1))),
% 0.76/0.97      inference('sup+', [status(thm)], ['61', '62'])).
% 0.76/0.97  thf('64', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('65', plain, (((k10_relat_1 @ sk_C_1 @ sk_B) = (k1_relat_1 @ sk_C_1))),
% 0.76/0.97      inference('demod', [status(thm)], ['63', '64'])).
% 0.76/0.97  thf('66', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.76/0.97      inference('simplify', [status(thm)], ['25'])).
% 0.76/0.97  thf('67', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (r1_tarski @ X0 @ sk_B)
% 0.76/0.97          | ((k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ X0)) = (X0)))),
% 0.76/0.97      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.76/0.97  thf('68', plain,
% 0.76/0.97      (((k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ sk_B)) = (sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['66', '67'])).
% 0.76/0.97  thf('69', plain, (((k10_relat_1 @ sk_C_1 @ sk_B) = (k1_relat_1 @ sk_C_1))),
% 0.76/0.97      inference('demod', [status(thm)], ['63', '64'])).
% 0.76/0.97  thf('70', plain, (((k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)) = (sk_B))),
% 0.76/0.97      inference('demod', [status(thm)], ['68', '69'])).
% 0.76/0.97  thf('71', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('72', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('73', plain, ((v2_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('74', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.76/0.97      inference('demod', [status(thm)],
% 0.76/0.97                ['59', '60', '65', '70', '71', '72', '73'])).
% 0.76/0.97  thf(t3_funct_2, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.97       ( ( v1_funct_1 @ A ) & 
% 0.76/0.97         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.76/0.97         ( m1_subset_1 @
% 0.76/0.97           A @ 
% 0.76/0.97           ( k1_zfmisc_1 @
% 0.76/0.97             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.76/0.97  thf('75', plain,
% 0.76/0.97      (![X56 : $i]:
% 0.76/0.97         ((m1_subset_1 @ X56 @ 
% 0.76/0.97           (k1_zfmisc_1 @ 
% 0.76/0.97            (k2_zfmisc_1 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 0.76/0.97          | ~ (v1_funct_1 @ X56)
% 0.76/0.97          | ~ (v1_relat_1 @ X56))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.76/0.97  thf('76', plain,
% 0.76/0.97      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97         (k1_zfmisc_1 @ 
% 0.76/0.97          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))
% 0.76/0.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.76/0.97        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.76/0.97      inference('sup+', [status(thm)], ['74', '75'])).
% 0.76/0.97  thf('77', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ sk_C_1)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.97        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.76/0.97        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97           (k1_zfmisc_1 @ 
% 0.76/0.97            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['20', '76'])).
% 0.76/0.97  thf('78', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('79', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('80', plain,
% 0.76/0.97      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.76/0.97        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97           (k1_zfmisc_1 @ 
% 0.76/0.97            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))),
% 0.76/0.97      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.76/0.97  thf('81', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ sk_C_1)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.97        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97           (k1_zfmisc_1 @ 
% 0.76/0.97            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['19', '80'])).
% 0.76/0.97  thf('82', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('83', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('84', plain,
% 0.76/0.97      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97        (k1_zfmisc_1 @ 
% 0.76/0.97         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))),
% 0.76/0.97      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.76/0.97  thf('85', plain,
% 0.76/0.97      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))
% 0.76/0.97        | ~ (v1_relat_1 @ sk_C_1)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.97        | ~ (v2_funct_1 @ sk_C_1))),
% 0.76/0.97      inference('sup+', [status(thm)], ['18', '84'])).
% 0.76/0.97  thf('86', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('87', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('88', plain, ((v2_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('89', plain,
% 0.76/0.97      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 0.76/0.97      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.76/0.97  thf(t14_relset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.76/0.97       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.76/0.97         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.76/0.97  thf('90', plain,
% 0.76/0.97      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.76/0.97         (~ (r1_tarski @ (k2_relat_1 @ X46) @ X47)
% 0.76/0.97          | (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X47)))
% 0.76/0.97          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 0.76/0.97      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.76/0.97  thf('91', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.76/0.97          | ~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)) @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['89', '90'])).
% 0.76/0.97  thf('92', plain, (((k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)) = (sk_B))),
% 0.76/0.97      inference('demod', [status(thm)], ['68', '69'])).
% 0.76/0.97  thf('93', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.76/0.97      inference('simplify', [status(thm)], ['25'])).
% 0.76/0.97  thf(t177_funct_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.97       ( ![B:$i]:
% 0.76/0.97         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.76/0.97           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.76/0.97             ( B ) ) ) ) ))).
% 0.76/0.97  thf('94', plain,
% 0.76/0.97      (![X28 : $i, X29 : $i]:
% 0.76/0.97         (~ (r1_tarski @ X28 @ (k1_relat_1 @ X29))
% 0.76/0.97          | ((k9_relat_1 @ (k2_funct_1 @ X29) @ (k9_relat_1 @ X29 @ X28))
% 0.76/0.97              = (X28))
% 0.76/0.97          | ~ (v2_funct_1 @ X29)
% 0.76/0.97          | ~ (v1_funct_1 @ X29)
% 0.76/0.97          | ~ (v1_relat_1 @ X29))),
% 0.76/0.97      inference('cnf', [status(esa)], [t177_funct_1])).
% 0.76/0.97  thf('95', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ X0)
% 0.76/0.97          | ~ (v1_funct_1 @ X0)
% 0.76/0.97          | ~ (v2_funct_1 @ X0)
% 0.76/0.97          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.76/0.97              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['93', '94'])).
% 0.76/0.97  thf('96', plain,
% 0.76/0.97      ((((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_B) = (k1_relat_1 @ sk_C_1))
% 0.76/0.97        | ~ (v2_funct_1 @ sk_C_1)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.97        | ~ (v1_relat_1 @ sk_C_1))),
% 0.76/0.97      inference('sup+', [status(thm)], ['92', '95'])).
% 0.76/0.97  thf('97', plain,
% 0.76/0.97      (![X23 : $i]:
% 0.76/0.97         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 0.76/0.97          | ~ (v1_funct_1 @ X23)
% 0.76/0.97          | ~ (v1_relat_1 @ X23))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.76/0.97  thf('98', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.76/0.97      inference('demod', [status(thm)],
% 0.76/0.97                ['59', '60', '65', '70', '71', '72', '73'])).
% 0.76/0.97  thf(t146_relat_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ A ) =>
% 0.76/0.97       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.76/0.97  thf('99', plain,
% 0.76/0.97      (![X16 : $i]:
% 0.76/0.97         (((k9_relat_1 @ X16 @ (k1_relat_1 @ X16)) = (k2_relat_1 @ X16))
% 0.76/0.97          | ~ (v1_relat_1 @ X16))),
% 0.76/0.97      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.76/0.97  thf('100', plain,
% 0.76/0.97      ((((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_B)
% 0.76/0.97          = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 0.76/0.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.76/0.97      inference('sup+', [status(thm)], ['98', '99'])).
% 0.76/0.97  thf('101', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ sk_C_1)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.97        | ((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_B)
% 0.76/0.97            = (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['97', '100'])).
% 0.76/0.97  thf('102', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('103', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('104', plain,
% 0.76/0.97      (((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_B)
% 0.76/0.97         = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.76/0.97      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.76/0.97  thf('105', plain, ((v2_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('106', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('107', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('108', plain,
% 0.76/0.97      (((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k1_relat_1 @ sk_C_1))),
% 0.76/0.97      inference('demod', [status(thm)], ['96', '104', '105', '106', '107'])).
% 0.76/0.97  thf('109', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.76/0.97          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 0.76/0.97      inference('demod', [status(thm)], ['91', '108'])).
% 0.76/0.97  thf('110', plain,
% 0.76/0.97      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['17', '109'])).
% 0.76/0.97  thf('111', plain,
% 0.76/0.97      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.76/0.97         <= (~
% 0.76/0.97             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.76/0.97      inference('split', [status(esa)], ['0'])).
% 0.76/0.97  thf('112', plain,
% 0.76/0.97      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['110', '111'])).
% 0.76/0.97  thf('113', plain,
% 0.76/0.97      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)) | 
% 0.76/0.97       ~
% 0.76/0.97       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.76/0.97       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.76/0.97      inference('split', [status(esa)], ['0'])).
% 0.76/0.97  thf('114', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 0.76/0.97      inference('sat_resolution*', [status(thm)], ['10', '112', '113'])).
% 0.76/0.97  thf('115', plain, (~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)),
% 0.76/0.97      inference('simpl_trail', [status(thm)], ['1', '114'])).
% 0.76/0.97  thf('116', plain,
% 0.76/0.97      (((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k1_relat_1 @ sk_C_1))),
% 0.76/0.97      inference('demod', [status(thm)], ['96', '104', '105', '106', '107'])).
% 0.76/0.97  thf(t65_relat_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ A ) =>
% 0.76/0.97       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.76/0.97         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.76/0.97  thf('117', plain,
% 0.76/0.97      (![X19 : $i]:
% 0.76/0.97         (((k2_relat_1 @ X19) != (k1_xboole_0))
% 0.76/0.97          | ((k1_relat_1 @ X19) = (k1_xboole_0))
% 0.76/0.97          | ~ (v1_relat_1 @ X19))),
% 0.76/0.97      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.76/0.97  thf('118', plain,
% 0.76/0.97      ((((k1_relat_1 @ sk_C_1) != (k1_xboole_0))
% 0.76/0.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.76/0.97        | ((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k1_xboole_0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['116', '117'])).
% 0.76/0.97  thf('119', plain,
% 0.76/0.97      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97        (k1_zfmisc_1 @ 
% 0.76/0.97         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))),
% 0.76/0.97      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.76/0.97  thf('120', plain,
% 0.76/0.97      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.76/0.97         ((v1_relat_1 @ X37)
% 0.76/0.97          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.76/0.97      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/0.97  thf('121', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['119', '120'])).
% 0.76/0.97  thf('122', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.76/0.97      inference('demod', [status(thm)],
% 0.76/0.97                ['59', '60', '65', '70', '71', '72', '73'])).
% 0.76/0.97  thf('123', plain,
% 0.76/0.97      ((((k1_relat_1 @ sk_C_1) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.97      inference('demod', [status(thm)], ['118', '121', '122'])).
% 0.76/0.97  thf('124', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 0.76/0.97      inference('demod', [status(thm)], ['15', '16'])).
% 0.76/0.97  thf('125', plain,
% 0.76/0.97      (![X23 : $i]:
% 0.76/0.97         ((v1_funct_1 @ (k2_funct_1 @ X23))
% 0.76/0.97          | ~ (v1_funct_1 @ X23)
% 0.76/0.97          | ~ (v1_relat_1 @ X23))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.76/0.97  thf('126', plain,
% 0.76/0.97      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.76/0.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 0.76/0.97      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.76/0.97  thf(t9_funct_2, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.97     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.76/0.97         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.76/0.97       ( ( r1_tarski @ B @ C ) =>
% 0.76/0.97         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.76/0.97             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.76/0.97           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.76/0.97  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.76/0.97  thf(zf_stmt_2, axiom,
% 0.76/0.97    (![B:$i,A:$i]:
% 0.76/0.97     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.76/0.97       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.76/0.97  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.76/0.97  thf(zf_stmt_4, axiom,
% 0.76/0.97    (![D:$i,C:$i,A:$i]:
% 0.76/0.97     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 0.76/0.97       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.76/0.97         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.76/0.97  thf(zf_stmt_5, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.97     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.76/0.97         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.97       ( ( r1_tarski @ B @ C ) =>
% 0.76/0.97         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 0.76/0.97  thf('127', plain,
% 0.76/0.97      (![X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 0.76/0.97         (~ (r1_tarski @ X62 @ X63)
% 0.76/0.97          | (zip_tseitin_1 @ X62 @ X64)
% 0.76/0.97          | ~ (v1_funct_1 @ X65)
% 0.76/0.97          | ~ (v1_funct_2 @ X65 @ X64 @ X62)
% 0.76/0.97          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X62)))
% 0.76/0.97          | (zip_tseitin_0 @ X65 @ X63 @ X64))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.97  thf('128', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 0.76/0.97          | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.76/0.97               (k1_relat_1 @ sk_C_1))
% 0.76/0.97          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.76/0.97          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.76/0.97          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['126', '127'])).
% 0.76/0.97  thf('129', plain,
% 0.76/0.97      (![X32 : $i]:
% 0.76/0.97         (~ (v2_funct_1 @ X32)
% 0.76/0.97          | ((k1_relat_1 @ X32) = (k2_relat_1 @ (k2_funct_1 @ X32)))
% 0.76/0.97          | ~ (v1_funct_1 @ X32)
% 0.76/0.97          | ~ (v1_relat_1 @ X32))),
% 0.76/0.97      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.76/0.97  thf('130', plain,
% 0.76/0.97      (![X23 : $i]:
% 0.76/0.97         ((v1_funct_1 @ (k2_funct_1 @ X23))
% 0.76/0.97          | ~ (v1_funct_1 @ X23)
% 0.76/0.97          | ~ (v1_relat_1 @ X23))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.76/0.97  thf('131', plain,
% 0.76/0.97      (![X23 : $i]:
% 0.76/0.97         ((v1_relat_1 @ (k2_funct_1 @ X23))
% 0.76/0.97          | ~ (v1_funct_1 @ X23)
% 0.76/0.97          | ~ (v1_relat_1 @ X23))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.76/0.97  thf('132', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.76/0.97      inference('demod', [status(thm)],
% 0.76/0.97                ['59', '60', '65', '70', '71', '72', '73'])).
% 0.76/0.97  thf('133', plain,
% 0.76/0.97      (![X56 : $i]:
% 0.76/0.97         ((v1_funct_2 @ X56 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))
% 0.76/0.97          | ~ (v1_funct_1 @ X56)
% 0.76/0.97          | ~ (v1_relat_1 @ X56))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.76/0.97  thf('134', plain,
% 0.76/0.97      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.76/0.97         (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 0.76/0.97        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 0.76/0.97        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.76/0.97      inference('sup+', [status(thm)], ['132', '133'])).
% 0.76/0.97  thf('135', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ sk_C_1)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.97        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.76/0.97        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.76/0.97           (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['131', '134'])).
% 0.76/0.97  thf('136', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('137', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('138', plain,
% 0.76/0.97      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.76/0.97        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.76/0.97           (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.76/0.97      inference('demod', [status(thm)], ['135', '136', '137'])).
% 0.76/0.97  thf('139', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ sk_C_1)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.97        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.76/0.97           (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['130', '138'])).
% 0.76/0.97  thf('140', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('141', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('142', plain,
% 0.76/0.97      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ 
% 0.76/0.97        (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.76/0.97      inference('demod', [status(thm)], ['139', '140', '141'])).
% 0.76/0.97  thf('143', plain,
% 0.76/0.97      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ (k1_relat_1 @ sk_C_1))
% 0.76/0.97        | ~ (v1_relat_1 @ sk_C_1)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.97        | ~ (v2_funct_1 @ sk_C_1))),
% 0.76/0.97      inference('sup+', [status(thm)], ['129', '142'])).
% 0.76/0.97  thf('144', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('145', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('146', plain, ((v2_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('147', plain,
% 0.76/0.97      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ (k1_relat_1 @ sk_C_1))),
% 0.76/0.97      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 0.76/0.97  thf('148', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B)
% 0.76/0.97          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.76/0.97          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.76/0.97          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 0.76/0.97      inference('demod', [status(thm)], ['128', '147'])).
% 0.76/0.97  thf('149', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ sk_C_1)
% 0.76/0.97          | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.97          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0)
% 0.76/0.97          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.76/0.97          | (zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['125', '148'])).
% 0.76/0.97  thf('150', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.97  thf('151', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('152', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0)
% 0.76/0.97          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.76/0.97          | (zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B))),
% 0.76/0.97      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.76/0.97  thf('153', plain,
% 0.76/0.97      (((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ sk_A @ sk_B)
% 0.76/0.97        | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 0.76/0.97      inference('sup-', [status(thm)], ['124', '152'])).
% 0.76/0.97  thf('154', plain,
% 0.76/0.97      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.76/0.97         ((v1_funct_2 @ X57 @ X59 @ X58) | ~ (zip_tseitin_0 @ X57 @ X58 @ X59))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.76/0.97  thf('155', plain,
% 0.76/0.97      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.76/0.97        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['153', '154'])).
% 0.76/0.97  thf('156', plain, (~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)),
% 0.76/0.97      inference('simpl_trail', [status(thm)], ['1', '114'])).
% 0.76/0.97  thf('157', plain, ((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)),
% 0.76/0.97      inference('clc', [status(thm)], ['155', '156'])).
% 0.76/0.97  thf('158', plain,
% 0.76/0.97      (![X60 : $i, X61 : $i]:
% 0.76/0.97         (((X60) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X60 @ X61))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.97  thf('159', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['157', '158'])).
% 0.76/0.97  thf('160', plain,
% 0.76/0.97      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.97      inference('demod', [status(thm)], ['123', '159'])).
% 0.76/0.97  thf('161', plain, (((sk_B) = (k1_xboole_0))),
% 0.76/0.97      inference('simplify', [status(thm)], ['160'])).
% 0.76/0.97  thf('162', plain,
% 0.76/0.97      (~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ k1_xboole_0 @ sk_A)),
% 0.76/0.97      inference('demod', [status(thm)], ['115', '161'])).
% 0.76/0.97  thf('163', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['157', '158'])).
% 0.76/0.97  thf(t64_relat_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ A ) =>
% 0.76/0.97       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.76/0.97           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.97         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.76/0.97  thf('164', plain,
% 0.76/0.98      (![X18 : $i]:
% 0.76/0.98         (((k1_relat_1 @ X18) != (k1_xboole_0))
% 0.76/0.98          | ((X18) = (k1_xboole_0))
% 0.76/0.98          | ~ (v1_relat_1 @ X18))),
% 0.76/0.98      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.76/0.98  thf('165', plain,
% 0.76/0.98      ((((k1_xboole_0) != (k1_xboole_0))
% 0.76/0.98        | ~ (v1_relat_1 @ sk_C_1)
% 0.76/0.98        | ((sk_C_1) = (k1_xboole_0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['163', '164'])).
% 0.76/0.98  thf('166', plain, ((v1_relat_1 @ sk_C_1)),
% 0.76/0.98      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.98  thf('167', plain,
% 0.76/0.98      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.76/0.98      inference('demod', [status(thm)], ['165', '166'])).
% 0.76/0.98  thf('168', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.76/0.98      inference('simplify', [status(thm)], ['167'])).
% 0.76/0.98  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.76/0.98  thf('169', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.76/0.98  thf(redefinition_k6_partfun1, axiom,
% 0.76/0.98    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.76/0.98  thf('170', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.76/0.98  thf('171', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('demod', [status(thm)], ['169', '170'])).
% 0.76/0.98  thf(t67_funct_1, axiom,
% 0.76/0.98    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.76/0.98  thf('172', plain,
% 0.76/0.98      (![X36 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X36)) = (k6_relat_1 @ X36))),
% 0.76/0.98      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.76/0.98  thf('173', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.76/0.98  thf('174', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.76/0.98  thf('175', plain,
% 0.76/0.98      (![X36 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X36)) = (k6_partfun1 @ X36))),
% 0.76/0.98      inference('demod', [status(thm)], ['172', '173', '174'])).
% 0.76/0.98  thf('176', plain,
% 0.76/0.98      (((k2_funct_1 @ k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 0.76/0.98      inference('sup+', [status(thm)], ['171', '175'])).
% 0.76/0.98  thf('177', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('demod', [status(thm)], ['169', '170'])).
% 0.76/0.98  thf('178', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('demod', [status(thm)], ['176', '177'])).
% 0.76/0.98  thf('179', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('demod', [status(thm)], ['169', '170'])).
% 0.76/0.98  thf(dt_k6_partfun1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( m1_subset_1 @
% 0.76/0.98         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.76/0.98       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.76/0.98  thf('180', plain, (![X53 : $i]: (v1_partfun1 @ (k6_partfun1 @ X53) @ X53)),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.76/0.98  thf('181', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.76/0.98      inference('sup+', [status(thm)], ['179', '180'])).
% 0.76/0.98  thf('182', plain,
% 0.76/0.98      (![X1 : $i, X3 : $i]:
% 0.76/0.98         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.76/0.98      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.98  thf('183', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('demod', [status(thm)], ['169', '170'])).
% 0.76/0.98  thf(fc4_zfmisc_1, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.76/0.98  thf('184', plain,
% 0.76/0.98      (![X4 : $i, X5 : $i]:
% 0.76/0.98         (~ (v1_xboole_0 @ X4) | (v1_xboole_0 @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.76/0.98  thf('185', plain,
% 0.76/0.98      (![X54 : $i]:
% 0.76/0.98         (m1_subset_1 @ (k6_partfun1 @ X54) @ 
% 0.76/0.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X54)))),
% 0.76/0.98      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.76/0.98  thf(t5_subset, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.76/0.98          ( v1_xboole_0 @ C ) ) ))).
% 0.76/0.98  thf('186', plain,
% 0.76/0.98      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.98         (~ (r2_hidden @ X9 @ X10)
% 0.76/0.98          | ~ (v1_xboole_0 @ X11)
% 0.76/0.98          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.76/0.98      inference('cnf', [status(esa)], [t5_subset])).
% 0.76/0.98  thf('187', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 0.76/0.98          | ~ (r2_hidden @ X1 @ (k6_partfun1 @ X0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['185', '186'])).
% 0.76/0.98  thf('188', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ (k6_partfun1 @ X0)))),
% 0.76/0.98      inference('sup-', [status(thm)], ['184', '187'])).
% 0.76/0.98  thf('189', plain,
% 0.76/0.98      (![X0 : $i]:
% 0.76/0.98         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['183', '188'])).
% 0.76/0.98  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.76/0.98  thf('190', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.98  thf('191', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.76/0.98      inference('demod', [status(thm)], ['189', '190'])).
% 0.76/0.98  thf('192', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['182', '191'])).
% 0.76/0.98  thf(t3_subset, axiom,
% 0.76/0.98    (![A:$i,B:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.98  thf('193', plain,
% 0.76/0.98      (![X6 : $i, X8 : $i]:
% 0.76/0.98         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.76/0.98      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.98  thf('194', plain,
% 0.76/0.98      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['192', '193'])).
% 0.76/0.98  thf(cc1_funct_2, axiom,
% 0.76/0.98    (![A:$i,B:$i,C:$i]:
% 0.76/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.98       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.76/0.98         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.76/0.98  thf('195', plain,
% 0.76/0.98      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.76/0.98         (~ (v1_funct_1 @ X50)
% 0.76/0.98          | ~ (v1_partfun1 @ X50 @ X51)
% 0.76/0.98          | (v1_funct_2 @ X50 @ X51 @ X52)
% 0.76/0.98          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 0.76/0.98      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.76/0.98  thf('196', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.76/0.98          | ~ (v1_partfun1 @ k1_xboole_0 @ X1)
% 0.76/0.98          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.76/0.98      inference('sup-', [status(thm)], ['194', '195'])).
% 0.76/0.98  thf('197', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.98      inference('demod', [status(thm)], ['169', '170'])).
% 0.76/0.98  thf(fc3_funct_1, axiom,
% 0.76/0.98    (![A:$i]:
% 0.76/0.98     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.76/0.98       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.76/0.98  thf('198', plain, (![X25 : $i]: (v1_funct_1 @ (k6_relat_1 @ X25))),
% 0.76/0.98      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.76/0.98  thf('199', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.76/0.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.76/0.98  thf('200', plain, (![X25 : $i]: (v1_funct_1 @ (k6_partfun1 @ X25))),
% 0.76/0.98      inference('demod', [status(thm)], ['198', '199'])).
% 0.76/0.98  thf('201', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.76/0.98      inference('sup+', [status(thm)], ['197', '200'])).
% 0.76/0.98  thf('202', plain,
% 0.76/0.98      (![X0 : $i, X1 : $i]:
% 0.76/0.98         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.76/0.98          | ~ (v1_partfun1 @ k1_xboole_0 @ X1))),
% 0.76/0.98      inference('demod', [status(thm)], ['196', '201'])).
% 0.76/0.98  thf('203', plain,
% 0.76/0.98      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.76/0.98      inference('sup-', [status(thm)], ['181', '202'])).
% 0.76/0.98  thf('204', plain, ($false),
% 0.76/0.98      inference('demod', [status(thm)], ['162', '168', '178', '203'])).
% 0.76/0.98  
% 0.76/0.98  % SZS output end Refutation
% 0.76/0.98  
% 0.76/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
