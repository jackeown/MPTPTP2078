%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oxNjX1oIFq

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:10 EST 2020

% Result     : Theorem 12.23s
% Output     : Refutation 12.23s
% Verified   : 
% Statistics : Number of formulae       :  391 (21265 expanded)
%              Number of leaves         :   68 (6438 expanded)
%              Depth                    :   31
%              Number of atoms          : 3423 (472476 expanded)
%              Number of equality atoms :  194 (4777 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t88_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
        & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
          & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_funct_2])).

thf('0',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X78: $i] :
      ( ( k6_partfun1 @ X78 )
      = ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X76: $i,X77: $i] :
      ( ( ( k2_funct_2 @ X77 @ X76 )
        = ( k2_funct_1 @ X76 ) )
      | ~ ( m1_subset_1 @ X76 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X77 @ X77 ) ) )
      | ~ ( v3_funct_2 @ X76 @ X77 @ X77 )
      | ~ ( v1_funct_2 @ X76 @ X77 @ X77 )
      | ~ ( v1_funct_1 @ X76 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_B_2 )
    | ~ ( v1_funct_2 @ sk_B_2 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_2 @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B_2 )
      = ( k2_funct_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_2 )
    = ( k2_funct_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ ( k2_funct_1 @ sk_B_2 ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('18',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('21',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X62 ) ) )
      | ~ ( v1_funct_1 @ X60 )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X65 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X61 @ X62 @ X64 @ X65 @ X60 @ X63 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X61 @ X65 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ X1 @ X0 @ X4 @ X2 @ k1_xboole_0 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('23',plain,(
    ! [X68: $i,X69: $i] :
      ( v4_relat_1 @ ( sk_C @ X68 @ X69 ) @ X69 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v4_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C @ X1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X68: $i,X69: $i] :
      ( v1_relat_1 @ ( sk_C @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('28',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k1_relat_1 @ ( sk_C @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C @ X0 @ k1_xboole_0 ) )
      | ( ( sk_C @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X68: $i,X69: $i] :
      ( v1_relat_1 @ ( sk_C @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( sk_C @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X68: $i,X69: $i] :
      ( v1_funct_1 @ ( sk_C @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('40',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ X1 @ X0 @ X4 @ X2 @ k1_xboole_0 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['22','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_B_2 )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X1 @ sk_A @ sk_A @ k1_xboole_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X1 @ sk_A @ sk_A @ k1_xboole_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_partfun1 @ k1_xboole_0 @ X0 @ sk_A @ sk_A @ k1_xboole_0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','44'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('46',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_partfun1 @ k1_xboole_0 @ X0 @ sk_A @ sk_A @ k1_xboole_0 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k1_partfun1 @ k1_xboole_0 @ X0 @ sk_A @ sk_A @ k1_xboole_0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_partfun1 @ X0 @ X1 @ sk_A @ sk_A @ k1_xboole_0 @ sk_B_2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_partfun1 @ X2 @ X1 @ sk_A @ sk_A @ X0 @ sk_B_2 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ X2 @ X1 @ sk_A @ sk_A @ X0 @ sk_B_2 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','51'])).

thf('53',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_2 )
    = ( k2_funct_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('54',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    ! [X78: $i] :
      ( ( k6_partfun1 @ X78 )
      = ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_2 ) @ sk_B_2 ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ k1_xboole_0 @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B_2 ) )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('62',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('63',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('64',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','69'])).

thf('71',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('72',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( r2_relset_1 @ X44 @ X45 @ X46 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ k1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','74'])).

thf('76',plain,
    ( ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B_2 ) ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['58','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('78',plain,(
    ! [X66: $i,X67: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X66 @ X67 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X66 ) ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X66 ) ) )
      | ~ ( v3_funct_2 @ X67 @ X66 @ X66 )
      | ~ ( v1_funct_2 @ X67 @ X66 @ X66 )
      | ~ ( v1_funct_1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ sk_B_2 )
    | ~ ( v1_funct_2 @ sk_B_2 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_2 @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v3_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('84',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( v1_funct_1 @ X55 )
      | ~ ( v3_funct_2 @ X55 @ X56 @ X57 )
      | ( v2_funct_2 @ X55 @ X57 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('85',plain,
    ( ( v2_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X66: $i,X67: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X66 @ X67 ) @ X66 @ X66 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X66 ) ) )
      | ~ ( v3_funct_2 @ X67 @ X66 @ X66 )
      | ~ ( v1_funct_2 @ X67 @ X66 @ X66 )
      | ~ ( v1_funct_1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('88',plain,
    ( ~ ( v1_funct_1 @ sk_B_2 )
    | ~ ( v1_funct_2 @ sk_B_2 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_2 @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v3_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X66: $i,X67: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X66 @ X67 ) )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X66 ) ) )
      | ~ ( v3_funct_2 @ X67 @ X66 @ X66 )
      | ~ ( v1_funct_2 @ X67 @ X66 @ X66 )
      | ~ ( v1_funct_1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('95',plain,
    ( ~ ( v1_funct_1 @ sk_B_2 )
    | ~ ( v1_funct_2 @ sk_B_2 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_2 @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v3_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('100',plain,(
    v2_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['85','92','99'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('101',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v2_funct_2 @ X59 @ X58 )
      | ( ( k2_relat_1 @ X59 )
        = X58 )
      | ~ ( v5_relat_1 @ X59 @ X58 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) )
    | ~ ( v5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('104',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('105',plain,(
    v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('107',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v5_relat_1 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('108',plain,(
    v5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k2_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) )
    = sk_A ),
    inference(demod,[status(thm)],['102','105','108'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('110',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('112',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('113',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('114',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v4_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('117',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('118',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('119',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['117','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['116','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('124',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('126',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('127',plain,(
    ! [X25: $i] :
      ( ( ( k9_relat_1 @ X25 @ ( k1_relat_1 @ X25 ) )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('128',plain,
    ( ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['117','120'])).

thf('130',plain,
    ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('132',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X37 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('135',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( ( k7_relset_1 @ X49 @ X50 @ X51 @ X49 )
        = ( k2_relset_1 @ X49 @ X50 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X1 )
      = ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('138',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k7_relset_1 @ X41 @ X42 @ X40 @ X43 )
        = ( k9_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k9_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X1 )
      = ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['136','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ k1_xboole_0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['133','140'])).

thf('142',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['130','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['111','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','146'])).

thf('148',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['109','147'])).

thf('149',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_2 )
    = ( k2_funct_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('150',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B_2 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['76','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('153',plain,(
    ! [X79: $i,X80: $i,X81: $i] :
      ( ( X79 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X80 )
      | ~ ( v1_funct_2 @ X80 @ X81 @ X79 )
      | ~ ( m1_subset_1 @ X80 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X81 @ X79 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X80 ) @ X80 )
        = ( k6_partfun1 @ X79 ) )
      | ~ ( v2_funct_1 @ X80 )
      | ( ( k2_relset_1 @ X81 @ X79 @ X80 )
       != X79 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('154',plain,(
    ! [X78: $i] :
      ( ( k6_partfun1 @ X78 )
      = ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('155',plain,(
    ! [X79: $i,X80: $i,X81: $i] :
      ( ( X79 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X80 )
      | ~ ( v1_funct_2 @ X80 @ X81 @ X79 )
      | ~ ( m1_subset_1 @ X80 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X81 @ X79 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X80 ) @ X80 )
        = ( k6_relat_1 @ X79 ) )
      | ~ ( v2_funct_1 @ X80 )
      | ( ( k2_relset_1 @ X81 @ X79 @ X80 )
       != X79 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_2 )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_2 ) @ sk_B_2 )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_B_2 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['152','155'])).

thf('157',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( ( k7_relset_1 @ X49 @ X50 @ X51 @ X49 )
        = ( k2_relset_1 @ X49 @ X50 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('159',plain,
    ( ( k7_relset_1 @ sk_A @ sk_A @ sk_B_2 @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k7_relset_1 @ X41 @ X42 @ X40 @ X43 )
        = ( k9_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_A @ sk_B_2 @ X0 )
      = ( k9_relat_1 @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k9_relat_1 @ sk_B_2 @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['159','162'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('164',plain,(
    ! [X27: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k1_relat_1 @ X27 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('165',plain,
    ( ( k2_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) )
    = sk_A ),
    inference(demod,[status(thm)],['102','105','108'])).

thf('166',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_2 )
    = ( k2_funct_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('167',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B_2 ) )
    = sk_A ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( k1_relat_1 @ sk_B_2 )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_B_2 )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['164','167'])).

thf('169',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('171',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('173',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( v1_funct_1 @ X55 )
      | ~ ( v3_funct_2 @ X55 @ X56 @ X57 )
      | ( v2_funct_1 @ X55 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('177',plain,
    ( ( v2_funct_1 @ sk_B_2 )
    | ~ ( v3_funct_2 @ sk_B_2 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v3_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_funct_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,
    ( ( k1_relat_1 @ sk_B_2 )
    = sk_A ),
    inference(demod,[status(thm)],['168','173','174','180'])).

thf('182',plain,(
    ! [X25: $i] :
      ( ( ( k9_relat_1 @ X25 @ ( k1_relat_1 @ X25 ) )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('183',plain,
    ( ( ( k9_relat_1 @ sk_B_2 @ sk_A )
      = ( k2_relat_1 @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( v1_funct_1 @ X55 )
      | ~ ( v3_funct_2 @ X55 @ X56 @ X57 )
      | ( v2_funct_2 @ X55 @ X57 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('186',plain,
    ( ( v2_funct_2 @ sk_B_2 @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_2 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v3_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_funct_2 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( v2_funct_2 @ X59 @ X58 )
      | ( ( k2_relat_1 @ X59 )
        = X58 )
      | ~ ( v5_relat_1 @ X59 @ X58 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('191',plain,
    ( ~ ( v1_relat_1 @ sk_B_2 )
    | ~ ( v5_relat_1 @ sk_B_2 @ sk_A )
    | ( ( k2_relat_1 @ sk_B_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['171','172'])).

thf('193',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v5_relat_1 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('195',plain,(
    v5_relat_1 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,
    ( ( k2_relat_1 @ sk_B_2 )
    = sk_A ),
    inference(demod,[status(thm)],['191','192','195'])).

thf('197',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['171','172'])).

thf('198',plain,
    ( ( k9_relat_1 @ sk_B_2 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['183','196','197'])).

thf('199',plain,
    ( sk_A
    = ( k2_relset_1 @ sk_A @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['163','198'])).

thf('200',plain,(
    v2_funct_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('201',plain,(
    v1_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( sk_A != sk_A )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_2 ) @ sk_B_2 )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['156','199','200','201','202'])).

thf('204',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B_2 ) @ sk_B_2 )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('207',plain,(
    ! [X70: $i,X71: $i,X72: $i,X73: $i,X74: $i,X75: $i] :
      ( ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X71 @ X72 ) ) )
      | ~ ( v1_funct_1 @ X70 )
      | ~ ( v1_funct_1 @ X73 )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X74 @ X75 ) ) )
      | ( ( k1_partfun1 @ X71 @ X72 @ X74 @ X75 @ X70 @ X73 )
        = ( k5_relat_1 @ X70 @ X73 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('208',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('210',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_2 )
    = ( k2_funct_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('212',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_2 )
    = ( k2_funct_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('213',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B_2 ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_2 ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['210','211','212'])).

thf('214',plain,
    ( ~ ( v1_funct_1 @ sk_B_2 )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_2 ) @ sk_B_2 )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['205','213'])).

thf('215',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_2 ) @ sk_B_2 )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B_2 ) @ sk_B_2 ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('218',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B_2 ) @ sk_B_2 ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['204','218'])).

thf('220',plain,(
    ! [X48: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('221',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['72'])).

thf('222',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['219','222'])).

thf('224',plain,
    ( ( k2_relat_1 @ sk_B_2 )
    = sk_A ),
    inference(demod,[status(thm)],['191','192','195'])).

thf('225',plain,(
    ! [X26: $i] :
      ( ( ( k2_relat_1 @ X26 )
       != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('226',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_2 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['171','172'])).

thf('228',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['223','228'])).

thf('230',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['151','230'])).

thf('232',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['219','222'])).

thf('233',plain,
    ( ( k2_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) )
    = sk_A ),
    inference(demod,[status(thm)],['102','105','108'])).

thf('234',plain,(
    ! [X26: $i] :
      ( ( ( k2_relat_1 @ X26 )
       != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('235',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) )
    | ( ( k2_funct_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    v1_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('237',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_funct_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_2 )
    = ( k2_funct_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('239',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_funct_1 @ sk_B_2 )
        = k1_xboole_0 ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['232','239'])).

thf('241',plain,
    ( ( ( k2_funct_1 @ sk_B_2 )
      = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('243',plain,
    ( ( ( k2_funct_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('245',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['231','243','244'])).

thf('246',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ sk_B_2 ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('247',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['245','246'])).

thf('248',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ ( k2_funct_1 @ sk_B_2 ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','247'])).

thf('249',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('250',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_2 )
    = ( k2_funct_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('251',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    ! [X70: $i,X71: $i,X72: $i,X73: $i,X74: $i,X75: $i] :
      ( ~ ( m1_subset_1 @ X70 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X71 @ X72 ) ) )
      | ~ ( v1_funct_1 @ X70 )
      | ~ ( v1_funct_1 @ X73 )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X74 @ X75 ) ) )
      | ( ( k1_partfun1 @ X71 @ X72 @ X74 @ X75 @ X70 @ X73 )
        = ( k5_relat_1 @ X70 @ X73 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('254',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_2 @ X0 )
        = ( k5_relat_1 @ sk_B_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_2 @ X0 )
        = ( k5_relat_1 @ sk_B_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ ( k2_funct_1 @ sk_B_2 ) )
      = ( k5_relat_1 @ sk_B_2 @ ( k2_funct_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['251','256'])).

thf('258',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['95','96','97','98'])).

thf('259',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_2 )
    = ( k2_funct_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('260',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ ( k2_funct_1 @ sk_B_2 ) )
    = ( k5_relat_1 @ sk_B_2 @ ( k2_funct_1 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['257','260'])).

thf('262',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B_2 @ ( k2_funct_1 @ sk_B_2 ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['248','261'])).

thf('263',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    ! [X79: $i,X80: $i,X81: $i] :
      ( ( X79 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X80 )
      | ~ ( v1_funct_2 @ X80 @ X81 @ X79 )
      | ~ ( m1_subset_1 @ X80 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X81 @ X79 ) ) )
      | ( ( k5_relat_1 @ X80 @ ( k2_funct_1 @ X80 ) )
        = ( k6_partfun1 @ X81 ) )
      | ~ ( v2_funct_1 @ X80 )
      | ( ( k2_relset_1 @ X81 @ X79 @ X80 )
       != X79 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('265',plain,(
    ! [X78: $i] :
      ( ( k6_partfun1 @ X78 )
      = ( k6_relat_1 @ X78 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('266',plain,(
    ! [X79: $i,X80: $i,X81: $i] :
      ( ( X79 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X80 )
      | ~ ( v1_funct_2 @ X80 @ X81 @ X79 )
      | ~ ( m1_subset_1 @ X80 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X81 @ X79 ) ) )
      | ( ( k5_relat_1 @ X80 @ ( k2_funct_1 @ X80 ) )
        = ( k6_relat_1 @ X81 ) )
      | ~ ( v2_funct_1 @ X80 )
      | ( ( k2_relset_1 @ X81 @ X79 @ X80 )
       != X79 ) ) ),
    inference(demod,[status(thm)],['264','265'])).

thf('267',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_2 )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 )
    | ( ( k5_relat_1 @ sk_B_2 @ ( k2_funct_1 @ sk_B_2 ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_B_2 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_2 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['263','266'])).

thf('268',plain,
    ( ( k9_relat_1 @ sk_B_2 @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['159','162'])).

thf('269',plain,(
    v2_funct_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('270',plain,(
    v1_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ( ( k9_relat_1 @ sk_B_2 @ sk_A )
     != sk_A )
    | ( ( k5_relat_1 @ sk_B_2 @ ( k2_funct_1 @ sk_B_2 ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['267','268','269','270','271'])).

thf('273',plain,
    ( ( k9_relat_1 @ sk_B_2 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['183','196','197'])).

thf('274',plain,
    ( ( sk_A != sk_A )
    | ( ( k5_relat_1 @ sk_B_2 @ ( k2_funct_1 @ sk_B_2 ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['272','273'])).

thf('275',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_B_2 @ ( k2_funct_1 @ sk_B_2 ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['274'])).

thf('276',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B_2 @ ( k2_funct_1 @ sk_B_2 ) ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['248','261'])).

thf('277',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('279',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['277','278'])).

thf('280',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['277','278'])).

thf('281',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['277','278'])).

thf('282',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('283',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('284',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('285',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['283','284'])).

thf('286',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('287',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['285','286'])).

thf('288',plain,(
    v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['282','287'])).

thf('289',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('290',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k5_relat_1 @ sk_B_2 @ ( k2_funct_1 @ sk_B_2 ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['262','279','280','281','290'])).

thf('292',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('293',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['277','278'])).

thf('294',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['292','293'])).

thf('295',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['294'])).

thf('296',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['294'])).

thf('297',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('298',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['277','278'])).

thf('299',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_funct_1 @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['297','298'])).

thf('300',plain,
    ( ( k2_funct_1 @ sk_B_2 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['299'])).

thf('301',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['294'])).

thf('302',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['300','301'])).

thf('303',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_2 @ X0 )
        = ( k5_relat_1 @ sk_B_2 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('305',plain,
    ( ~ ( v1_funct_1 @ sk_B_2 )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ sk_B_2 )
      = ( k5_relat_1 @ sk_B_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('306',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ sk_B_2 )
    = ( k5_relat_1 @ sk_B_2 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['305','306'])).

thf('308',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ X2 @ X1 @ sk_A @ sk_A @ X0 @ sk_B_2 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','51'])).

thf('309',plain,
    ( ( ( k5_relat_1 @ sk_B_2 @ sk_B_2 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['307','308'])).

thf('310',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('312',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['310','311'])).

thf('313',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( ( k5_relat_1 @ sk_B_2 @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['309','312'])).

thf('314',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['277','278'])).

thf('315',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('316',plain,
    ( ( k5_relat_1 @ sk_B_2 @ sk_B_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['313','314','315'])).

thf('317',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['294'])).

thf('318',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['294'])).

thf('319',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['316','317','318'])).

thf('320',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('321',plain,(
    $false ),
    inference(demod,[status(thm)],['291','295','296','302','319','320'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oxNjX1oIFq
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:03:31 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 12.23/12.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 12.23/12.44  % Solved by: fo/fo7.sh
% 12.23/12.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.23/12.44  % done 14156 iterations in 11.963s
% 12.23/12.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 12.23/12.44  % SZS output start Refutation
% 12.23/12.44  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 12.23/12.44  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 12.23/12.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.23/12.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 12.23/12.44  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 12.23/12.44  thf(sk_B_type, type, sk_B: $i > $i).
% 12.23/12.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.23/12.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 12.23/12.44  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 12.23/12.44  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 12.23/12.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 12.23/12.44  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 12.23/12.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 12.23/12.44  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 12.23/12.44  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 12.23/12.44  thf(sk_A_type, type, sk_A: $i).
% 12.23/12.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 12.23/12.44  thf(sk_B_2_type, type, sk_B_2: $i).
% 12.23/12.44  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 12.23/12.44  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 12.23/12.44  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 12.23/12.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.23/12.44  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 12.23/12.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 12.23/12.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.23/12.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.23/12.44  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 12.23/12.44  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 12.23/12.44  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 12.23/12.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 12.23/12.44  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 12.23/12.44  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 12.23/12.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 12.23/12.44  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 12.23/12.44  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 12.23/12.44  thf(t88_funct_2, conjecture,
% 12.23/12.44    (![A:$i,B:$i]:
% 12.23/12.44     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 12.23/12.44         ( v3_funct_2 @ B @ A @ A ) & 
% 12.23/12.44         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 12.23/12.44       ( ( r2_relset_1 @
% 12.23/12.44           A @ A @ 
% 12.23/12.44           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 12.23/12.44           ( k6_partfun1 @ A ) ) & 
% 12.23/12.44         ( r2_relset_1 @
% 12.23/12.44           A @ A @ 
% 12.23/12.44           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 12.23/12.44           ( k6_partfun1 @ A ) ) ) ))).
% 12.23/12.44  thf(zf_stmt_0, negated_conjecture,
% 12.23/12.44    (~( ![A:$i,B:$i]:
% 12.23/12.44        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 12.23/12.44            ( v3_funct_2 @ B @ A @ A ) & 
% 12.23/12.44            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 12.23/12.44          ( ( r2_relset_1 @
% 12.23/12.44              A @ A @ 
% 12.23/12.44              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 12.23/12.44              ( k6_partfun1 @ A ) ) & 
% 12.23/12.44            ( r2_relset_1 @
% 12.23/12.44              A @ A @ 
% 12.23/12.44              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 12.23/12.44              ( k6_partfun1 @ A ) ) ) ) )),
% 12.23/12.44    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 12.23/12.44  thf('0', plain,
% 12.23/12.44      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ 
% 12.23/12.44            (k2_funct_2 @ sk_A @ sk_B_2)) @ 
% 12.23/12.44           (k6_partfun1 @ sk_A))
% 12.23/12.44        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44              (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44             (k6_partfun1 @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('1', plain,
% 12.23/12.44      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ 
% 12.23/12.44            (k2_funct_2 @ sk_A @ sk_B_2)) @ 
% 12.23/12.44           (k6_partfun1 @ sk_A)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2)) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('split', [status(esa)], ['0'])).
% 12.23/12.44  thf(redefinition_k6_partfun1, axiom,
% 12.23/12.44    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 12.23/12.44  thf('2', plain, (![X78 : $i]: ((k6_partfun1 @ X78) = (k6_relat_1 @ X78))),
% 12.23/12.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 12.23/12.44  thf('3', plain,
% 12.23/12.44      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ 
% 12.23/12.44            (k2_funct_2 @ sk_A @ sk_B_2)) @ 
% 12.23/12.44           (k6_relat_1 @ sk_A)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2)) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('demod', [status(thm)], ['1', '2'])).
% 12.23/12.44  thf('4', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf(redefinition_k2_funct_2, axiom,
% 12.23/12.44    (![A:$i,B:$i]:
% 12.23/12.44     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 12.23/12.44         ( v3_funct_2 @ B @ A @ A ) & 
% 12.23/12.44         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 12.23/12.44       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 12.23/12.44  thf('5', plain,
% 12.23/12.44      (![X76 : $i, X77 : $i]:
% 12.23/12.44         (((k2_funct_2 @ X77 @ X76) = (k2_funct_1 @ X76))
% 12.23/12.44          | ~ (m1_subset_1 @ X76 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X77 @ X77)))
% 12.23/12.44          | ~ (v3_funct_2 @ X76 @ X77 @ X77)
% 12.23/12.44          | ~ (v1_funct_2 @ X76 @ X77 @ X77)
% 12.23/12.44          | ~ (v1_funct_1 @ X76))),
% 12.23/12.44      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 12.23/12.44  thf('6', plain,
% 12.23/12.44      ((~ (v1_funct_1 @ sk_B_2)
% 12.23/12.44        | ~ (v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)
% 12.23/12.44        | ~ (v3_funct_2 @ sk_B_2 @ sk_A @ sk_A)
% 12.23/12.44        | ((k2_funct_2 @ sk_A @ sk_B_2) = (k2_funct_1 @ sk_B_2)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['4', '5'])).
% 12.23/12.44  thf('7', plain, ((v1_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('8', plain, ((v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('9', plain, ((v3_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B_2) = (k2_funct_1 @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 12.23/12.44  thf('11', plain,
% 12.23/12.44      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ 
% 12.23/12.44            (k2_funct_1 @ sk_B_2)) @ 
% 12.23/12.44           (k6_relat_1 @ sk_A)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2)) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('demod', [status(thm)], ['3', '10'])).
% 12.23/12.44  thf(t7_xboole_0, axiom,
% 12.23/12.44    (![A:$i]:
% 12.23/12.44     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 12.23/12.44          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 12.23/12.44  thf('12', plain,
% 12.23/12.44      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 12.23/12.44      inference('cnf', [status(esa)], [t7_xboole_0])).
% 12.23/12.44  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 12.23/12.44  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 12.23/12.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 12.23/12.44  thf(t8_boole, axiom,
% 12.23/12.44    (![A:$i,B:$i]:
% 12.23/12.44     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 12.23/12.44  thf('14', plain,
% 12.23/12.44      (![X7 : $i, X8 : $i]:
% 12.23/12.44         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 12.23/12.44      inference('cnf', [status(esa)], [t8_boole])).
% 12.23/12.44  thf('15', plain,
% 12.23/12.44      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['13', '14'])).
% 12.23/12.44  thf('16', plain,
% 12.23/12.44      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['13', '14'])).
% 12.23/12.44  thf(t113_zfmisc_1, axiom,
% 12.23/12.44    (![A:$i,B:$i]:
% 12.23/12.44     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 12.23/12.44       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 12.23/12.44  thf('17', plain,
% 12.23/12.44      (![X10 : $i, X11 : $i]:
% 12.23/12.44         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 12.23/12.44          | ((X10) != (k1_xboole_0)))),
% 12.23/12.44      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 12.23/12.44  thf('18', plain,
% 12.23/12.44      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 12.23/12.44      inference('simplify', [status(thm)], ['17'])).
% 12.23/12.44  thf('19', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf(t4_subset_1, axiom,
% 12.23/12.44    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 12.23/12.44  thf('20', plain,
% 12.23/12.44      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 12.23/12.44      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.23/12.44  thf(dt_k1_partfun1, axiom,
% 12.23/12.44    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 12.23/12.44     ( ( ( v1_funct_1 @ E ) & 
% 12.23/12.44         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 12.23/12.44         ( v1_funct_1 @ F ) & 
% 12.23/12.44         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 12.23/12.44       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 12.23/12.44         ( m1_subset_1 @
% 12.23/12.44           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 12.23/12.44           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 12.23/12.44  thf('21', plain,
% 12.23/12.44      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 12.23/12.44         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X62)))
% 12.23/12.44          | ~ (v1_funct_1 @ X60)
% 12.23/12.44          | ~ (v1_funct_1 @ X63)
% 12.23/12.44          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X65)))
% 12.23/12.44          | (m1_subset_1 @ (k1_partfun1 @ X61 @ X62 @ X64 @ X65 @ X60 @ X63) @ 
% 12.23/12.44             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X61 @ X65))))),
% 12.23/12.44      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 12.23/12.44  thf('22', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.23/12.44         ((m1_subset_1 @ 
% 12.23/12.44           (k1_partfun1 @ X1 @ X0 @ X4 @ X2 @ k1_xboole_0 @ X3) @ 
% 12.23/12.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 12.23/12.44          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X2)))
% 12.23/12.44          | ~ (v1_funct_1 @ X3)
% 12.23/12.44          | ~ (v1_funct_1 @ k1_xboole_0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['20', '21'])).
% 12.23/12.44  thf(rc1_funct_2, axiom,
% 12.23/12.44    (![A:$i,B:$i]:
% 12.23/12.44     ( ?[C:$i]:
% 12.23/12.44       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 12.23/12.44         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 12.23/12.44         ( v1_relat_1 @ C ) & 
% 12.23/12.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 12.23/12.44  thf('23', plain,
% 12.23/12.44      (![X68 : $i, X69 : $i]: (v4_relat_1 @ (sk_C @ X68 @ X69) @ X69)),
% 12.23/12.44      inference('cnf', [status(esa)], [rc1_funct_2])).
% 12.23/12.44  thf(d18_relat_1, axiom,
% 12.23/12.44    (![A:$i,B:$i]:
% 12.23/12.44     ( ( v1_relat_1 @ B ) =>
% 12.23/12.44       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 12.23/12.44  thf('24', plain,
% 12.23/12.44      (![X21 : $i, X22 : $i]:
% 12.23/12.44         (~ (v4_relat_1 @ X21 @ X22)
% 12.23/12.44          | (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 12.23/12.44          | ~ (v1_relat_1 @ X21))),
% 12.23/12.44      inference('cnf', [status(esa)], [d18_relat_1])).
% 12.23/12.44  thf('25', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]:
% 12.23/12.44         (~ (v1_relat_1 @ (sk_C @ X1 @ X0))
% 12.23/12.44          | (r1_tarski @ (k1_relat_1 @ (sk_C @ X1 @ X0)) @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['23', '24'])).
% 12.23/12.44  thf('26', plain, (![X68 : $i, X69 : $i]: (v1_relat_1 @ (sk_C @ X68 @ X69))),
% 12.23/12.44      inference('cnf', [status(esa)], [rc1_funct_2])).
% 12.23/12.44  thf('27', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]: (r1_tarski @ (k1_relat_1 @ (sk_C @ X1 @ X0)) @ X0)),
% 12.23/12.44      inference('demod', [status(thm)], ['25', '26'])).
% 12.23/12.44  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 12.23/12.44  thf('28', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 12.23/12.44      inference('cnf', [status(esa)], [t65_xboole_1])).
% 12.23/12.44  thf(t69_xboole_1, axiom,
% 12.23/12.44    (![A:$i,B:$i]:
% 12.23/12.44     ( ( ~( v1_xboole_0 @ B ) ) =>
% 12.23/12.44       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 12.23/12.44  thf('29', plain,
% 12.23/12.44      (![X5 : $i, X6 : $i]:
% 12.23/12.44         (~ (r1_xboole_0 @ X5 @ X6)
% 12.23/12.44          | ~ (r1_tarski @ X5 @ X6)
% 12.23/12.44          | (v1_xboole_0 @ X5))),
% 12.23/12.44      inference('cnf', [status(esa)], [t69_xboole_1])).
% 12.23/12.44  thf('30', plain,
% 12.23/12.44      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['28', '29'])).
% 12.23/12.44  thf('31', plain,
% 12.23/12.44      (![X0 : $i]: (v1_xboole_0 @ (k1_relat_1 @ (sk_C @ X0 @ k1_xboole_0)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['27', '30'])).
% 12.23/12.44  thf('32', plain,
% 12.23/12.44      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['13', '14'])).
% 12.23/12.44  thf(t64_relat_1, axiom,
% 12.23/12.44    (![A:$i]:
% 12.23/12.44     ( ( v1_relat_1 @ A ) =>
% 12.23/12.44       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 12.23/12.44           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 12.23/12.44         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 12.23/12.44  thf('33', plain,
% 12.23/12.44      (![X26 : $i]:
% 12.23/12.44         (((k1_relat_1 @ X26) != (k1_xboole_0))
% 12.23/12.44          | ((X26) = (k1_xboole_0))
% 12.23/12.44          | ~ (v1_relat_1 @ X26))),
% 12.23/12.44      inference('cnf', [status(esa)], [t64_relat_1])).
% 12.23/12.44  thf('34', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]:
% 12.23/12.44         (((k1_relat_1 @ X1) != (X0))
% 12.23/12.44          | ~ (v1_xboole_0 @ X0)
% 12.23/12.44          | ~ (v1_relat_1 @ X1)
% 12.23/12.44          | ((X1) = (k1_xboole_0)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['32', '33'])).
% 12.23/12.44  thf('35', plain,
% 12.23/12.44      (![X1 : $i]:
% 12.23/12.44         (((X1) = (k1_xboole_0))
% 12.23/12.44          | ~ (v1_relat_1 @ X1)
% 12.23/12.44          | ~ (v1_xboole_0 @ (k1_relat_1 @ X1)))),
% 12.23/12.44      inference('simplify', [status(thm)], ['34'])).
% 12.23/12.44  thf('36', plain,
% 12.23/12.44      (![X0 : $i]:
% 12.23/12.44         (~ (v1_relat_1 @ (sk_C @ X0 @ k1_xboole_0))
% 12.23/12.44          | ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['31', '35'])).
% 12.23/12.44  thf('37', plain, (![X68 : $i, X69 : $i]: (v1_relat_1 @ (sk_C @ X68 @ X69))),
% 12.23/12.44      inference('cnf', [status(esa)], [rc1_funct_2])).
% 12.23/12.44  thf('38', plain, (![X0 : $i]: ((sk_C @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 12.23/12.44      inference('demod', [status(thm)], ['36', '37'])).
% 12.23/12.44  thf('39', plain, (![X68 : $i, X69 : $i]: (v1_funct_1 @ (sk_C @ X68 @ X69))),
% 12.23/12.44      inference('cnf', [status(esa)], [rc1_funct_2])).
% 12.23/12.44  thf('40', plain, ((v1_funct_1 @ k1_xboole_0)),
% 12.23/12.44      inference('sup+', [status(thm)], ['38', '39'])).
% 12.23/12.44  thf('41', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 12.23/12.44         ((m1_subset_1 @ 
% 12.23/12.44           (k1_partfun1 @ X1 @ X0 @ X4 @ X2 @ k1_xboole_0 @ X3) @ 
% 12.23/12.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 12.23/12.44          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X2)))
% 12.23/12.44          | ~ (v1_funct_1 @ X3))),
% 12.23/12.44      inference('demod', [status(thm)], ['22', '40'])).
% 12.23/12.44  thf('42', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]:
% 12.23/12.44         (~ (v1_funct_1 @ sk_B_2)
% 12.23/12.44          | (m1_subset_1 @ 
% 12.23/12.44             (k1_partfun1 @ X0 @ X1 @ sk_A @ sk_A @ k1_xboole_0 @ sk_B_2) @ 
% 12.23/12.44             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 12.23/12.44      inference('sup-', [status(thm)], ['19', '41'])).
% 12.23/12.44  thf('43', plain, ((v1_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('44', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]:
% 12.23/12.44         (m1_subset_1 @ 
% 12.23/12.44          (k1_partfun1 @ X0 @ X1 @ sk_A @ sk_A @ k1_xboole_0 @ sk_B_2) @ 
% 12.23/12.44          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))),
% 12.23/12.44      inference('demod', [status(thm)], ['42', '43'])).
% 12.23/12.44  thf('45', plain,
% 12.23/12.44      (![X0 : $i]:
% 12.23/12.44         (m1_subset_1 @ 
% 12.23/12.44          (k1_partfun1 @ k1_xboole_0 @ X0 @ sk_A @ sk_A @ k1_xboole_0 @ sk_B_2) @ 
% 12.23/12.44          (k1_zfmisc_1 @ k1_xboole_0))),
% 12.23/12.44      inference('sup+', [status(thm)], ['18', '44'])).
% 12.23/12.44  thf(t5_subset, axiom,
% 12.23/12.44    (![A:$i,B:$i,C:$i]:
% 12.23/12.44     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 12.23/12.44          ( v1_xboole_0 @ C ) ) ))).
% 12.23/12.44  thf('46', plain,
% 12.23/12.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.23/12.44         (~ (r2_hidden @ X16 @ X17)
% 12.23/12.44          | ~ (v1_xboole_0 @ X18)
% 12.23/12.44          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 12.23/12.44      inference('cnf', [status(esa)], [t5_subset])).
% 12.23/12.44  thf('47', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]:
% 12.23/12.44         (~ (v1_xboole_0 @ k1_xboole_0)
% 12.23/12.44          | ~ (r2_hidden @ X1 @ 
% 12.23/12.44               (k1_partfun1 @ k1_xboole_0 @ X0 @ sk_A @ sk_A @ k1_xboole_0 @ 
% 12.23/12.44                sk_B_2)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['45', '46'])).
% 12.23/12.44  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 12.23/12.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 12.23/12.44  thf('49', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]:
% 12.23/12.44         ~ (r2_hidden @ X1 @ 
% 12.23/12.44            (k1_partfun1 @ k1_xboole_0 @ X0 @ sk_A @ sk_A @ k1_xboole_0 @ 
% 12.23/12.44             sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['47', '48'])).
% 12.23/12.44  thf('50', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.23/12.44         (~ (r2_hidden @ X2 @ 
% 12.23/12.44             (k1_partfun1 @ X0 @ X1 @ sk_A @ sk_A @ k1_xboole_0 @ sk_B_2))
% 12.23/12.44          | ~ (v1_xboole_0 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['16', '49'])).
% 12.23/12.44  thf('51', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.23/12.44         (~ (r2_hidden @ X3 @ 
% 12.23/12.44             (k1_partfun1 @ X2 @ X1 @ sk_A @ sk_A @ X0 @ sk_B_2))
% 12.23/12.44          | ~ (v1_xboole_0 @ X0)
% 12.23/12.44          | ~ (v1_xboole_0 @ X2))),
% 12.23/12.44      inference('sup-', [status(thm)], ['15', '50'])).
% 12.23/12.44  thf('52', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.23/12.44         (((k1_partfun1 @ X2 @ X1 @ sk_A @ sk_A @ X0 @ sk_B_2) = (k1_xboole_0))
% 12.23/12.44          | ~ (v1_xboole_0 @ X2)
% 12.23/12.44          | ~ (v1_xboole_0 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['12', '51'])).
% 12.23/12.44  thf('53', plain, (((k2_funct_2 @ sk_A @ sk_B_2) = (k2_funct_1 @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 12.23/12.44  thf('54', plain,
% 12.23/12.44      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44            (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44           (k6_partfun1 @ sk_A)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('split', [status(esa)], ['0'])).
% 12.23/12.44  thf('55', plain, (![X78 : $i]: ((k6_partfun1 @ X78) = (k6_relat_1 @ X78))),
% 12.23/12.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 12.23/12.44  thf('56', plain,
% 12.23/12.44      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44            (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44           (k6_relat_1 @ sk_A)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('demod', [status(thm)], ['54', '55'])).
% 12.23/12.44  thf('57', plain,
% 12.23/12.44      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_2) @ 
% 12.23/12.44            sk_B_2) @ 
% 12.23/12.44           (k6_relat_1 @ sk_A)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('sup-', [status(thm)], ['53', '56'])).
% 12.23/12.44  thf('58', plain,
% 12.23/12.44      (((~ (r2_relset_1 @ sk_A @ sk_A @ k1_xboole_0 @ (k6_relat_1 @ sk_A))
% 12.23/12.44         | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B_2))
% 12.23/12.44         | ~ (v1_xboole_0 @ sk_A)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('sup-', [status(thm)], ['52', '57'])).
% 12.23/12.44  thf('59', plain,
% 12.23/12.44      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 12.23/12.44      inference('cnf', [status(esa)], [t7_xboole_0])).
% 12.23/12.44  thf('60', plain,
% 12.23/12.44      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['13', '14'])).
% 12.23/12.44  thf('61', plain,
% 12.23/12.44      (![X10 : $i, X11 : $i]:
% 12.23/12.44         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 12.23/12.44          | ((X11) != (k1_xboole_0)))),
% 12.23/12.44      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 12.23/12.44  thf('62', plain,
% 12.23/12.44      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 12.23/12.44      inference('simplify', [status(thm)], ['61'])).
% 12.23/12.44  thf(t29_relset_1, axiom,
% 12.23/12.44    (![A:$i]:
% 12.23/12.44     ( m1_subset_1 @
% 12.23/12.44       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 12.23/12.44  thf('63', plain,
% 12.23/12.44      (![X48 : $i]:
% 12.23/12.44         (m1_subset_1 @ (k6_relat_1 @ X48) @ 
% 12.23/12.44          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X48)))),
% 12.23/12.44      inference('cnf', [status(esa)], [t29_relset_1])).
% 12.23/12.44  thf('64', plain,
% 12.23/12.44      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 12.23/12.44      inference('sup+', [status(thm)], ['62', '63'])).
% 12.23/12.44  thf('65', plain,
% 12.23/12.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.23/12.44         (~ (r2_hidden @ X16 @ X17)
% 12.23/12.44          | ~ (v1_xboole_0 @ X18)
% 12.23/12.44          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 12.23/12.44      inference('cnf', [status(esa)], [t5_subset])).
% 12.23/12.44  thf('66', plain,
% 12.23/12.44      (![X0 : $i]:
% 12.23/12.44         (~ (v1_xboole_0 @ k1_xboole_0)
% 12.23/12.44          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['64', '65'])).
% 12.23/12.44  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 12.23/12.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 12.23/12.44  thf('68', plain,
% 12.23/12.44      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 12.23/12.44      inference('demod', [status(thm)], ['66', '67'])).
% 12.23/12.44  thf('69', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]:
% 12.23/12.44         (~ (r2_hidden @ X1 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['60', '68'])).
% 12.23/12.44  thf('70', plain,
% 12.23/12.44      (![X0 : $i]: (((k6_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['59', '69'])).
% 12.23/12.44  thf('71', plain,
% 12.23/12.44      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 12.23/12.44      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.23/12.44  thf(reflexivity_r2_relset_1, axiom,
% 12.23/12.44    (![A:$i,B:$i,C:$i,D:$i]:
% 12.23/12.44     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 12.23/12.44         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.23/12.44       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 12.23/12.44  thf('72', plain,
% 12.23/12.44      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 12.23/12.44         ((r2_relset_1 @ X44 @ X45 @ X46 @ X46)
% 12.23/12.44          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 12.23/12.44          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 12.23/12.44      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 12.23/12.44  thf('73', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.23/12.44         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 12.23/12.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 12.23/12.44      inference('condensation', [status(thm)], ['72'])).
% 12.23/12.44  thf('74', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 12.23/12.44      inference('sup-', [status(thm)], ['71', '73'])).
% 12.23/12.44  thf('75', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.23/12.44         ((r2_relset_1 @ X2 @ X1 @ k1_xboole_0 @ (k6_relat_1 @ X0))
% 12.23/12.44          | ~ (v1_xboole_0 @ X0))),
% 12.23/12.44      inference('sup+', [status(thm)], ['70', '74'])).
% 12.23/12.44  thf('76', plain,
% 12.23/12.44      (((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B_2))))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('clc', [status(thm)], ['58', '75'])).
% 12.23/12.44  thf('77', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf(dt_k2_funct_2, axiom,
% 12.23/12.44    (![A:$i,B:$i]:
% 12.23/12.44     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 12.23/12.44         ( v3_funct_2 @ B @ A @ A ) & 
% 12.23/12.44         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 12.23/12.44       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 12.23/12.44         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 12.23/12.44         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 12.23/12.44         ( m1_subset_1 @
% 12.23/12.44           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 12.23/12.44  thf('78', plain,
% 12.23/12.44      (![X66 : $i, X67 : $i]:
% 12.23/12.44         ((m1_subset_1 @ (k2_funct_2 @ X66 @ X67) @ 
% 12.23/12.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X66)))
% 12.23/12.44          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X66)))
% 12.23/12.44          | ~ (v3_funct_2 @ X67 @ X66 @ X66)
% 12.23/12.44          | ~ (v1_funct_2 @ X67 @ X66 @ X66)
% 12.23/12.44          | ~ (v1_funct_1 @ X67))),
% 12.23/12.44      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 12.23/12.44  thf('79', plain,
% 12.23/12.44      ((~ (v1_funct_1 @ sk_B_2)
% 12.23/12.44        | ~ (v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)
% 12.23/12.44        | ~ (v3_funct_2 @ sk_B_2 @ sk_A @ sk_A)
% 12.23/12.44        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_2) @ 
% 12.23/12.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 12.23/12.44      inference('sup-', [status(thm)], ['77', '78'])).
% 12.23/12.44  thf('80', plain, ((v1_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('81', plain, ((v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('82', plain, ((v3_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('83', plain,
% 12.23/12.44      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_2) @ 
% 12.23/12.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 12.23/12.44  thf(cc2_funct_2, axiom,
% 12.23/12.44    (![A:$i,B:$i,C:$i]:
% 12.23/12.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.23/12.44       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 12.23/12.44         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 12.23/12.44  thf('84', plain,
% 12.23/12.44      (![X55 : $i, X56 : $i, X57 : $i]:
% 12.23/12.44         (~ (v1_funct_1 @ X55)
% 12.23/12.44          | ~ (v3_funct_2 @ X55 @ X56 @ X57)
% 12.23/12.44          | (v2_funct_2 @ X55 @ X57)
% 12.23/12.44          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57))))),
% 12.23/12.44      inference('cnf', [status(esa)], [cc2_funct_2])).
% 12.23/12.44  thf('85', plain,
% 12.23/12.44      (((v2_funct_2 @ (k2_funct_2 @ sk_A @ sk_B_2) @ sk_A)
% 12.23/12.44        | ~ (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B_2) @ sk_A @ sk_A)
% 12.23/12.44        | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_2)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['83', '84'])).
% 12.23/12.44  thf('86', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('87', plain,
% 12.23/12.44      (![X66 : $i, X67 : $i]:
% 12.23/12.44         ((v3_funct_2 @ (k2_funct_2 @ X66 @ X67) @ X66 @ X66)
% 12.23/12.44          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X66)))
% 12.23/12.44          | ~ (v3_funct_2 @ X67 @ X66 @ X66)
% 12.23/12.44          | ~ (v1_funct_2 @ X67 @ X66 @ X66)
% 12.23/12.44          | ~ (v1_funct_1 @ X67))),
% 12.23/12.44      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 12.23/12.44  thf('88', plain,
% 12.23/12.44      ((~ (v1_funct_1 @ sk_B_2)
% 12.23/12.44        | ~ (v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)
% 12.23/12.44        | ~ (v3_funct_2 @ sk_B_2 @ sk_A @ sk_A)
% 12.23/12.44        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B_2) @ sk_A @ sk_A))),
% 12.23/12.44      inference('sup-', [status(thm)], ['86', '87'])).
% 12.23/12.44  thf('89', plain, ((v1_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('90', plain, ((v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('91', plain, ((v3_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('92', plain, ((v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B_2) @ sk_A @ sk_A)),
% 12.23/12.44      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 12.23/12.44  thf('93', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('94', plain,
% 12.23/12.44      (![X66 : $i, X67 : $i]:
% 12.23/12.44         ((v1_funct_1 @ (k2_funct_2 @ X66 @ X67))
% 12.23/12.44          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X66)))
% 12.23/12.44          | ~ (v3_funct_2 @ X67 @ X66 @ X66)
% 12.23/12.44          | ~ (v1_funct_2 @ X67 @ X66 @ X66)
% 12.23/12.44          | ~ (v1_funct_1 @ X67))),
% 12.23/12.44      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 12.23/12.44  thf('95', plain,
% 12.23/12.44      ((~ (v1_funct_1 @ sk_B_2)
% 12.23/12.44        | ~ (v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)
% 12.23/12.44        | ~ (v3_funct_2 @ sk_B_2 @ sk_A @ sk_A)
% 12.23/12.44        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_2)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['93', '94'])).
% 12.23/12.44  thf('96', plain, ((v1_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('97', plain, ((v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('98', plain, ((v3_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('99', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 12.23/12.44  thf('100', plain, ((v2_funct_2 @ (k2_funct_2 @ sk_A @ sk_B_2) @ sk_A)),
% 12.23/12.44      inference('demod', [status(thm)], ['85', '92', '99'])).
% 12.23/12.44  thf(d3_funct_2, axiom,
% 12.23/12.44    (![A:$i,B:$i]:
% 12.23/12.44     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 12.23/12.44       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 12.23/12.44  thf('101', plain,
% 12.23/12.44      (![X58 : $i, X59 : $i]:
% 12.23/12.44         (~ (v2_funct_2 @ X59 @ X58)
% 12.23/12.44          | ((k2_relat_1 @ X59) = (X58))
% 12.23/12.44          | ~ (v5_relat_1 @ X59 @ X58)
% 12.23/12.44          | ~ (v1_relat_1 @ X59))),
% 12.23/12.44      inference('cnf', [status(esa)], [d3_funct_2])).
% 12.23/12.44  thf('102', plain,
% 12.23/12.44      ((~ (v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_2))
% 12.23/12.44        | ~ (v5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_2) @ sk_A)
% 12.23/12.44        | ((k2_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_2)) = (sk_A)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['100', '101'])).
% 12.23/12.44  thf('103', plain,
% 12.23/12.44      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_2) @ 
% 12.23/12.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 12.23/12.44  thf(cc1_relset_1, axiom,
% 12.23/12.44    (![A:$i,B:$i,C:$i]:
% 12.23/12.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.23/12.44       ( v1_relat_1 @ C ) ))).
% 12.23/12.44  thf('104', plain,
% 12.23/12.44      (![X28 : $i, X29 : $i, X30 : $i]:
% 12.23/12.44         ((v1_relat_1 @ X28)
% 12.23/12.44          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 12.23/12.44      inference('cnf', [status(esa)], [cc1_relset_1])).
% 12.23/12.44  thf('105', plain, ((v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_2))),
% 12.23/12.44      inference('sup-', [status(thm)], ['103', '104'])).
% 12.23/12.44  thf('106', plain,
% 12.23/12.44      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_2) @ 
% 12.23/12.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 12.23/12.44  thf(cc2_relset_1, axiom,
% 12.23/12.44    (![A:$i,B:$i,C:$i]:
% 12.23/12.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.23/12.44       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 12.23/12.44  thf('107', plain,
% 12.23/12.44      (![X31 : $i, X32 : $i, X33 : $i]:
% 12.23/12.44         ((v5_relat_1 @ X31 @ X33)
% 12.23/12.44          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 12.23/12.44      inference('cnf', [status(esa)], [cc2_relset_1])).
% 12.23/12.44  thf('108', plain, ((v5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_2) @ sk_A)),
% 12.23/12.44      inference('sup-', [status(thm)], ['106', '107'])).
% 12.23/12.44  thf('109', plain, (((k2_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_2)) = (sk_A))),
% 12.23/12.44      inference('demod', [status(thm)], ['102', '105', '108'])).
% 12.23/12.44  thf(d1_xboole_0, axiom,
% 12.23/12.44    (![A:$i]:
% 12.23/12.44     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 12.23/12.44  thf('110', plain,
% 12.23/12.44      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 12.23/12.44      inference('cnf', [status(esa)], [d1_xboole_0])).
% 12.23/12.44  thf('111', plain,
% 12.23/12.44      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['13', '14'])).
% 12.23/12.44  thf('112', plain,
% 12.23/12.44      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 12.23/12.44      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.23/12.44  thf('113', plain,
% 12.23/12.44      (![X31 : $i, X32 : $i, X33 : $i]:
% 12.23/12.44         ((v4_relat_1 @ X31 @ X32)
% 12.23/12.44          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 12.23/12.44      inference('cnf', [status(esa)], [cc2_relset_1])).
% 12.23/12.44  thf('114', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 12.23/12.44      inference('sup-', [status(thm)], ['112', '113'])).
% 12.23/12.44  thf('115', plain,
% 12.23/12.44      (![X21 : $i, X22 : $i]:
% 12.23/12.44         (~ (v4_relat_1 @ X21 @ X22)
% 12.23/12.44          | (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 12.23/12.44          | ~ (v1_relat_1 @ X21))),
% 12.23/12.44      inference('cnf', [status(esa)], [d18_relat_1])).
% 12.23/12.44  thf('116', plain,
% 12.23/12.44      (![X0 : $i]:
% 12.23/12.44         (~ (v1_relat_1 @ k1_xboole_0)
% 12.23/12.44          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['114', '115'])).
% 12.23/12.44  thf(fc6_relat_1, axiom,
% 12.23/12.44    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 12.23/12.44  thf('117', plain,
% 12.23/12.44      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 12.23/12.44      inference('cnf', [status(esa)], [fc6_relat_1])).
% 12.23/12.44  thf('118', plain,
% 12.23/12.44      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 12.23/12.44      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.23/12.44  thf(cc2_relat_1, axiom,
% 12.23/12.44    (![A:$i]:
% 12.23/12.44     ( ( v1_relat_1 @ A ) =>
% 12.23/12.44       ( ![B:$i]:
% 12.23/12.44         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 12.23/12.44  thf('119', plain,
% 12.23/12.44      (![X19 : $i, X20 : $i]:
% 12.23/12.44         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 12.23/12.44          | (v1_relat_1 @ X19)
% 12.23/12.44          | ~ (v1_relat_1 @ X20))),
% 12.23/12.44      inference('cnf', [status(esa)], [cc2_relat_1])).
% 12.23/12.44  thf('120', plain,
% 12.23/12.44      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['118', '119'])).
% 12.23/12.44  thf('121', plain, ((v1_relat_1 @ k1_xboole_0)),
% 12.23/12.44      inference('sup-', [status(thm)], ['117', '120'])).
% 12.23/12.44  thf('122', plain,
% 12.23/12.44      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 12.23/12.44      inference('demod', [status(thm)], ['116', '121'])).
% 12.23/12.44  thf('123', plain,
% 12.23/12.44      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['28', '29'])).
% 12.23/12.44  thf('124', plain, ((v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['122', '123'])).
% 12.23/12.44  thf('125', plain,
% 12.23/12.44      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['13', '14'])).
% 12.23/12.44  thf('126', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['124', '125'])).
% 12.23/12.44  thf(t146_relat_1, axiom,
% 12.23/12.44    (![A:$i]:
% 12.23/12.44     ( ( v1_relat_1 @ A ) =>
% 12.23/12.44       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 12.23/12.44  thf('127', plain,
% 12.23/12.44      (![X25 : $i]:
% 12.23/12.44         (((k9_relat_1 @ X25 @ (k1_relat_1 @ X25)) = (k2_relat_1 @ X25))
% 12.23/12.44          | ~ (v1_relat_1 @ X25))),
% 12.23/12.44      inference('cnf', [status(esa)], [t146_relat_1])).
% 12.23/12.44  thf('128', plain,
% 12.23/12.44      ((((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 12.23/12.44        | ~ (v1_relat_1 @ k1_xboole_0))),
% 12.23/12.44      inference('sup+', [status(thm)], ['126', '127'])).
% 12.23/12.44  thf('129', plain, ((v1_relat_1 @ k1_xboole_0)),
% 12.23/12.44      inference('sup-', [status(thm)], ['117', '120'])).
% 12.23/12.44  thf('130', plain,
% 12.23/12.44      (((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 12.23/12.44      inference('demod', [status(thm)], ['128', '129'])).
% 12.23/12.44  thf('131', plain,
% 12.23/12.44      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 12.23/12.44      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.23/12.44  thf(dt_k2_relset_1, axiom,
% 12.23/12.44    (![A:$i,B:$i,C:$i]:
% 12.23/12.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.23/12.44       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 12.23/12.44  thf('132', plain,
% 12.23/12.44      (![X37 : $i, X38 : $i, X39 : $i]:
% 12.23/12.44         ((m1_subset_1 @ (k2_relset_1 @ X37 @ X38 @ X39) @ (k1_zfmisc_1 @ X38))
% 12.23/12.44          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 12.23/12.44      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 12.23/12.44  thf('133', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]:
% 12.23/12.44         (m1_subset_1 @ (k2_relset_1 @ X1 @ X0 @ k1_xboole_0) @ 
% 12.23/12.44          (k1_zfmisc_1 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['131', '132'])).
% 12.23/12.44  thf('134', plain,
% 12.23/12.44      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 12.23/12.44      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.23/12.44  thf(t38_relset_1, axiom,
% 12.23/12.44    (![A:$i,B:$i,C:$i]:
% 12.23/12.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.23/12.44       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 12.23/12.44         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 12.23/12.44  thf('135', plain,
% 12.23/12.44      (![X49 : $i, X50 : $i, X51 : $i]:
% 12.23/12.44         (((k7_relset_1 @ X49 @ X50 @ X51 @ X49)
% 12.23/12.44            = (k2_relset_1 @ X49 @ X50 @ X51))
% 12.23/12.44          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50))))),
% 12.23/12.44      inference('cnf', [status(esa)], [t38_relset_1])).
% 12.23/12.44  thf('136', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]:
% 12.23/12.44         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X1)
% 12.23/12.44           = (k2_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['134', '135'])).
% 12.23/12.44  thf('137', plain,
% 12.23/12.44      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 12.23/12.44      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.23/12.44  thf(redefinition_k7_relset_1, axiom,
% 12.23/12.44    (![A:$i,B:$i,C:$i,D:$i]:
% 12.23/12.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.23/12.44       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 12.23/12.44  thf('138', plain,
% 12.23/12.44      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 12.23/12.44         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 12.23/12.44          | ((k7_relset_1 @ X41 @ X42 @ X40 @ X43) = (k9_relat_1 @ X40 @ X43)))),
% 12.23/12.44      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 12.23/12.44  thf('139', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.23/12.44         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 12.23/12.44           = (k9_relat_1 @ k1_xboole_0 @ X2))),
% 12.23/12.44      inference('sup-', [status(thm)], ['137', '138'])).
% 12.23/12.44  thf('140', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]:
% 12.23/12.44         ((k9_relat_1 @ k1_xboole_0 @ X1)
% 12.23/12.44           = (k2_relset_1 @ X1 @ X0 @ k1_xboole_0))),
% 12.23/12.44      inference('demod', [status(thm)], ['136', '139'])).
% 12.23/12.44  thf('141', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]:
% 12.23/12.44         (m1_subset_1 @ (k9_relat_1 @ k1_xboole_0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 12.23/12.44      inference('demod', [status(thm)], ['133', '140'])).
% 12.23/12.44  thf('142', plain,
% 12.23/12.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 12.23/12.44         (~ (r2_hidden @ X16 @ X17)
% 12.23/12.44          | ~ (v1_xboole_0 @ X18)
% 12.23/12.44          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 12.23/12.44      inference('cnf', [status(esa)], [t5_subset])).
% 12.23/12.44  thf('143', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.23/12.44         (~ (v1_xboole_0 @ X0)
% 12.23/12.44          | ~ (r2_hidden @ X2 @ (k9_relat_1 @ k1_xboole_0 @ X1)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['141', '142'])).
% 12.23/12.44  thf('144', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]:
% 12.23/12.44         (~ (r2_hidden @ X0 @ (k2_relat_1 @ k1_xboole_0))
% 12.23/12.44          | ~ (v1_xboole_0 @ X1))),
% 12.23/12.44      inference('sup-', [status(thm)], ['130', '143'])).
% 12.23/12.44  thf('145', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.23/12.44         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 12.23/12.44          | ~ (v1_xboole_0 @ X0)
% 12.23/12.44          | ~ (v1_xboole_0 @ X2))),
% 12.23/12.44      inference('sup-', [status(thm)], ['111', '144'])).
% 12.23/12.44  thf('146', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]:
% 12.23/12.44         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 12.23/12.44      inference('condensation', [status(thm)], ['145'])).
% 12.23/12.44  thf('147', plain,
% 12.23/12.44      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['110', '146'])).
% 12.23/12.44  thf('148', plain,
% 12.23/12.44      (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ (k2_funct_2 @ sk_A @ sk_B_2)))),
% 12.23/12.44      inference('sup+', [status(thm)], ['109', '147'])).
% 12.23/12.44  thf('149', plain, (((k2_funct_2 @ sk_A @ sk_B_2) = (k2_funct_1 @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 12.23/12.44  thf('150', plain,
% 12.23/12.44      (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B_2)))),
% 12.23/12.44      inference('demod', [status(thm)], ['148', '149'])).
% 12.23/12.44  thf('151', plain,
% 12.23/12.44      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_B_2)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('clc', [status(thm)], ['76', '150'])).
% 12.23/12.44  thf('152', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf(t35_funct_2, axiom,
% 12.23/12.44    (![A:$i,B:$i,C:$i]:
% 12.23/12.44     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 12.23/12.44         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.23/12.44       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 12.23/12.44         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 12.23/12.44           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 12.23/12.44             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 12.23/12.44  thf('153', plain,
% 12.23/12.44      (![X79 : $i, X80 : $i, X81 : $i]:
% 12.23/12.44         (((X79) = (k1_xboole_0))
% 12.23/12.44          | ~ (v1_funct_1 @ X80)
% 12.23/12.44          | ~ (v1_funct_2 @ X80 @ X81 @ X79)
% 12.23/12.44          | ~ (m1_subset_1 @ X80 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X81 @ X79)))
% 12.23/12.44          | ((k5_relat_1 @ (k2_funct_1 @ X80) @ X80) = (k6_partfun1 @ X79))
% 12.23/12.44          | ~ (v2_funct_1 @ X80)
% 12.23/12.44          | ((k2_relset_1 @ X81 @ X79 @ X80) != (X79)))),
% 12.23/12.44      inference('cnf', [status(esa)], [t35_funct_2])).
% 12.23/12.44  thf('154', plain, (![X78 : $i]: ((k6_partfun1 @ X78) = (k6_relat_1 @ X78))),
% 12.23/12.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 12.23/12.44  thf('155', plain,
% 12.23/12.44      (![X79 : $i, X80 : $i, X81 : $i]:
% 12.23/12.44         (((X79) = (k1_xboole_0))
% 12.23/12.44          | ~ (v1_funct_1 @ X80)
% 12.23/12.44          | ~ (v1_funct_2 @ X80 @ X81 @ X79)
% 12.23/12.44          | ~ (m1_subset_1 @ X80 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X81 @ X79)))
% 12.23/12.44          | ((k5_relat_1 @ (k2_funct_1 @ X80) @ X80) = (k6_relat_1 @ X79))
% 12.23/12.44          | ~ (v2_funct_1 @ X80)
% 12.23/12.44          | ((k2_relset_1 @ X81 @ X79 @ X80) != (X79)))),
% 12.23/12.44      inference('demod', [status(thm)], ['153', '154'])).
% 12.23/12.44  thf('156', plain,
% 12.23/12.44      ((((k2_relset_1 @ sk_A @ sk_A @ sk_B_2) != (sk_A))
% 12.23/12.44        | ~ (v2_funct_1 @ sk_B_2)
% 12.23/12.44        | ((k5_relat_1 @ (k2_funct_1 @ sk_B_2) @ sk_B_2) = (k6_relat_1 @ sk_A))
% 12.23/12.44        | ~ (v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)
% 12.23/12.44        | ~ (v1_funct_1 @ sk_B_2)
% 12.23/12.44        | ((sk_A) = (k1_xboole_0)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['152', '155'])).
% 12.23/12.44  thf('157', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('158', plain,
% 12.23/12.44      (![X49 : $i, X50 : $i, X51 : $i]:
% 12.23/12.44         (((k7_relset_1 @ X49 @ X50 @ X51 @ X49)
% 12.23/12.44            = (k2_relset_1 @ X49 @ X50 @ X51))
% 12.23/12.44          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50))))),
% 12.23/12.44      inference('cnf', [status(esa)], [t38_relset_1])).
% 12.23/12.44  thf('159', plain,
% 12.23/12.44      (((k7_relset_1 @ sk_A @ sk_A @ sk_B_2 @ sk_A)
% 12.23/12.44         = (k2_relset_1 @ sk_A @ sk_A @ sk_B_2))),
% 12.23/12.44      inference('sup-', [status(thm)], ['157', '158'])).
% 12.23/12.44  thf('160', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('161', plain,
% 12.23/12.44      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 12.23/12.44         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 12.23/12.44          | ((k7_relset_1 @ X41 @ X42 @ X40 @ X43) = (k9_relat_1 @ X40 @ X43)))),
% 12.23/12.44      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 12.23/12.44  thf('162', plain,
% 12.23/12.44      (![X0 : $i]:
% 12.23/12.44         ((k7_relset_1 @ sk_A @ sk_A @ sk_B_2 @ X0)
% 12.23/12.44           = (k9_relat_1 @ sk_B_2 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['160', '161'])).
% 12.23/12.44  thf('163', plain,
% 12.23/12.44      (((k9_relat_1 @ sk_B_2 @ sk_A) = (k2_relset_1 @ sk_A @ sk_A @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['159', '162'])).
% 12.23/12.44  thf(t55_funct_1, axiom,
% 12.23/12.44    (![A:$i]:
% 12.23/12.44     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 12.23/12.44       ( ( v2_funct_1 @ A ) =>
% 12.23/12.44         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 12.23/12.44           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 12.23/12.44  thf('164', plain,
% 12.23/12.44      (![X27 : $i]:
% 12.23/12.44         (~ (v2_funct_1 @ X27)
% 12.23/12.44          | ((k1_relat_1 @ X27) = (k2_relat_1 @ (k2_funct_1 @ X27)))
% 12.23/12.44          | ~ (v1_funct_1 @ X27)
% 12.23/12.44          | ~ (v1_relat_1 @ X27))),
% 12.23/12.44      inference('cnf', [status(esa)], [t55_funct_1])).
% 12.23/12.44  thf('165', plain, (((k2_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_2)) = (sk_A))),
% 12.23/12.44      inference('demod', [status(thm)], ['102', '105', '108'])).
% 12.23/12.44  thf('166', plain, (((k2_funct_2 @ sk_A @ sk_B_2) = (k2_funct_1 @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 12.23/12.44  thf('167', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B_2)) = (sk_A))),
% 12.23/12.44      inference('demod', [status(thm)], ['165', '166'])).
% 12.23/12.44  thf('168', plain,
% 12.23/12.44      ((((k1_relat_1 @ sk_B_2) = (sk_A))
% 12.23/12.44        | ~ (v1_relat_1 @ sk_B_2)
% 12.23/12.44        | ~ (v1_funct_1 @ sk_B_2)
% 12.23/12.44        | ~ (v2_funct_1 @ sk_B_2))),
% 12.23/12.44      inference('sup+', [status(thm)], ['164', '167'])).
% 12.23/12.44  thf('169', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('170', plain,
% 12.23/12.44      (![X19 : $i, X20 : $i]:
% 12.23/12.44         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 12.23/12.44          | (v1_relat_1 @ X19)
% 12.23/12.44          | ~ (v1_relat_1 @ X20))),
% 12.23/12.44      inference('cnf', [status(esa)], [cc2_relat_1])).
% 12.23/12.44  thf('171', plain,
% 12.23/12.44      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_2))),
% 12.23/12.44      inference('sup-', [status(thm)], ['169', '170'])).
% 12.23/12.44  thf('172', plain,
% 12.23/12.44      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 12.23/12.44      inference('cnf', [status(esa)], [fc6_relat_1])).
% 12.23/12.44  thf('173', plain, ((v1_relat_1 @ sk_B_2)),
% 12.23/12.44      inference('demod', [status(thm)], ['171', '172'])).
% 12.23/12.44  thf('174', plain, ((v1_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('175', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('176', plain,
% 12.23/12.44      (![X55 : $i, X56 : $i, X57 : $i]:
% 12.23/12.44         (~ (v1_funct_1 @ X55)
% 12.23/12.44          | ~ (v3_funct_2 @ X55 @ X56 @ X57)
% 12.23/12.44          | (v2_funct_1 @ X55)
% 12.23/12.44          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57))))),
% 12.23/12.44      inference('cnf', [status(esa)], [cc2_funct_2])).
% 12.23/12.44  thf('177', plain,
% 12.23/12.44      (((v2_funct_1 @ sk_B_2)
% 12.23/12.44        | ~ (v3_funct_2 @ sk_B_2 @ sk_A @ sk_A)
% 12.23/12.44        | ~ (v1_funct_1 @ sk_B_2))),
% 12.23/12.44      inference('sup-', [status(thm)], ['175', '176'])).
% 12.23/12.44  thf('178', plain, ((v3_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('179', plain, ((v1_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('180', plain, ((v2_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('demod', [status(thm)], ['177', '178', '179'])).
% 12.23/12.44  thf('181', plain, (((k1_relat_1 @ sk_B_2) = (sk_A))),
% 12.23/12.44      inference('demod', [status(thm)], ['168', '173', '174', '180'])).
% 12.23/12.44  thf('182', plain,
% 12.23/12.44      (![X25 : $i]:
% 12.23/12.44         (((k9_relat_1 @ X25 @ (k1_relat_1 @ X25)) = (k2_relat_1 @ X25))
% 12.23/12.44          | ~ (v1_relat_1 @ X25))),
% 12.23/12.44      inference('cnf', [status(esa)], [t146_relat_1])).
% 12.23/12.44  thf('183', plain,
% 12.23/12.44      ((((k9_relat_1 @ sk_B_2 @ sk_A) = (k2_relat_1 @ sk_B_2))
% 12.23/12.44        | ~ (v1_relat_1 @ sk_B_2))),
% 12.23/12.44      inference('sup+', [status(thm)], ['181', '182'])).
% 12.23/12.44  thf('184', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('185', plain,
% 12.23/12.44      (![X55 : $i, X56 : $i, X57 : $i]:
% 12.23/12.44         (~ (v1_funct_1 @ X55)
% 12.23/12.44          | ~ (v3_funct_2 @ X55 @ X56 @ X57)
% 12.23/12.44          | (v2_funct_2 @ X55 @ X57)
% 12.23/12.44          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57))))),
% 12.23/12.44      inference('cnf', [status(esa)], [cc2_funct_2])).
% 12.23/12.44  thf('186', plain,
% 12.23/12.44      (((v2_funct_2 @ sk_B_2 @ sk_A)
% 12.23/12.44        | ~ (v3_funct_2 @ sk_B_2 @ sk_A @ sk_A)
% 12.23/12.44        | ~ (v1_funct_1 @ sk_B_2))),
% 12.23/12.44      inference('sup-', [status(thm)], ['184', '185'])).
% 12.23/12.44  thf('187', plain, ((v3_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('188', plain, ((v1_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('189', plain, ((v2_funct_2 @ sk_B_2 @ sk_A)),
% 12.23/12.44      inference('demod', [status(thm)], ['186', '187', '188'])).
% 12.23/12.44  thf('190', plain,
% 12.23/12.44      (![X58 : $i, X59 : $i]:
% 12.23/12.44         (~ (v2_funct_2 @ X59 @ X58)
% 12.23/12.44          | ((k2_relat_1 @ X59) = (X58))
% 12.23/12.44          | ~ (v5_relat_1 @ X59 @ X58)
% 12.23/12.44          | ~ (v1_relat_1 @ X59))),
% 12.23/12.44      inference('cnf', [status(esa)], [d3_funct_2])).
% 12.23/12.44  thf('191', plain,
% 12.23/12.44      ((~ (v1_relat_1 @ sk_B_2)
% 12.23/12.44        | ~ (v5_relat_1 @ sk_B_2 @ sk_A)
% 12.23/12.44        | ((k2_relat_1 @ sk_B_2) = (sk_A)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['189', '190'])).
% 12.23/12.44  thf('192', plain, ((v1_relat_1 @ sk_B_2)),
% 12.23/12.44      inference('demod', [status(thm)], ['171', '172'])).
% 12.23/12.44  thf('193', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('194', plain,
% 12.23/12.44      (![X31 : $i, X32 : $i, X33 : $i]:
% 12.23/12.44         ((v5_relat_1 @ X31 @ X33)
% 12.23/12.44          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 12.23/12.44      inference('cnf', [status(esa)], [cc2_relset_1])).
% 12.23/12.44  thf('195', plain, ((v5_relat_1 @ sk_B_2 @ sk_A)),
% 12.23/12.44      inference('sup-', [status(thm)], ['193', '194'])).
% 12.23/12.44  thf('196', plain, (((k2_relat_1 @ sk_B_2) = (sk_A))),
% 12.23/12.44      inference('demod', [status(thm)], ['191', '192', '195'])).
% 12.23/12.44  thf('197', plain, ((v1_relat_1 @ sk_B_2)),
% 12.23/12.44      inference('demod', [status(thm)], ['171', '172'])).
% 12.23/12.44  thf('198', plain, (((k9_relat_1 @ sk_B_2 @ sk_A) = (sk_A))),
% 12.23/12.44      inference('demod', [status(thm)], ['183', '196', '197'])).
% 12.23/12.44  thf('199', plain, (((sk_A) = (k2_relset_1 @ sk_A @ sk_A @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['163', '198'])).
% 12.23/12.44  thf('200', plain, ((v2_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('demod', [status(thm)], ['177', '178', '179'])).
% 12.23/12.44  thf('201', plain, ((v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('202', plain, ((v1_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('203', plain,
% 12.23/12.44      ((((sk_A) != (sk_A))
% 12.23/12.44        | ((k5_relat_1 @ (k2_funct_1 @ sk_B_2) @ sk_B_2) = (k6_relat_1 @ sk_A))
% 12.23/12.44        | ((sk_A) = (k1_xboole_0)))),
% 12.23/12.44      inference('demod', [status(thm)], ['156', '199', '200', '201', '202'])).
% 12.23/12.44  thf('204', plain,
% 12.23/12.44      ((((sk_A) = (k1_xboole_0))
% 12.23/12.44        | ((k5_relat_1 @ (k2_funct_1 @ sk_B_2) @ sk_B_2) = (k6_relat_1 @ sk_A)))),
% 12.23/12.44      inference('simplify', [status(thm)], ['203'])).
% 12.23/12.44  thf('205', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('206', plain,
% 12.23/12.44      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_2) @ 
% 12.23/12.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 12.23/12.44  thf(redefinition_k1_partfun1, axiom,
% 12.23/12.44    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 12.23/12.44     ( ( ( v1_funct_1 @ E ) & 
% 12.23/12.44         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 12.23/12.44         ( v1_funct_1 @ F ) & 
% 12.23/12.44         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 12.23/12.44       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 12.23/12.44  thf('207', plain,
% 12.23/12.44      (![X70 : $i, X71 : $i, X72 : $i, X73 : $i, X74 : $i, X75 : $i]:
% 12.23/12.44         (~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X71 @ X72)))
% 12.23/12.44          | ~ (v1_funct_1 @ X70)
% 12.23/12.44          | ~ (v1_funct_1 @ X73)
% 12.23/12.44          | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X74 @ X75)))
% 12.23/12.44          | ((k1_partfun1 @ X71 @ X72 @ X74 @ X75 @ X70 @ X73)
% 12.23/12.44              = (k5_relat_1 @ X70 @ X73)))),
% 12.23/12.44      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 12.23/12.44  thf('208', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.23/12.44         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ 
% 12.23/12.44            (k2_funct_2 @ sk_A @ sk_B_2) @ X0)
% 12.23/12.44            = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_2) @ X0))
% 12.23/12.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 12.23/12.44          | ~ (v1_funct_1 @ X0)
% 12.23/12.44          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_2)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['206', '207'])).
% 12.23/12.44  thf('209', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 12.23/12.44  thf('210', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.23/12.44         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ 
% 12.23/12.44            (k2_funct_2 @ sk_A @ sk_B_2) @ X0)
% 12.23/12.44            = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_2) @ X0))
% 12.23/12.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 12.23/12.44          | ~ (v1_funct_1 @ X0))),
% 12.23/12.44      inference('demod', [status(thm)], ['208', '209'])).
% 12.23/12.44  thf('211', plain, (((k2_funct_2 @ sk_A @ sk_B_2) = (k2_funct_1 @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 12.23/12.44  thf('212', plain, (((k2_funct_2 @ sk_A @ sk_B_2) = (k2_funct_1 @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 12.23/12.44  thf('213', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.23/12.44         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B_2) @ X0)
% 12.23/12.44            = (k5_relat_1 @ (k2_funct_1 @ sk_B_2) @ X0))
% 12.23/12.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 12.23/12.44          | ~ (v1_funct_1 @ X0))),
% 12.23/12.44      inference('demod', [status(thm)], ['210', '211', '212'])).
% 12.23/12.44  thf('214', plain,
% 12.23/12.44      ((~ (v1_funct_1 @ sk_B_2)
% 12.23/12.44        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_2) @ 
% 12.23/12.44            sk_B_2) = (k5_relat_1 @ (k2_funct_1 @ sk_B_2) @ sk_B_2)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['205', '213'])).
% 12.23/12.44  thf('215', plain, ((v1_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('216', plain,
% 12.23/12.44      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_2) @ 
% 12.23/12.44         sk_B_2) = (k5_relat_1 @ (k2_funct_1 @ sk_B_2) @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['214', '215'])).
% 12.23/12.44  thf('217', plain,
% 12.23/12.44      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B_2) @ 
% 12.23/12.44            sk_B_2) @ 
% 12.23/12.44           (k6_relat_1 @ sk_A)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('sup-', [status(thm)], ['53', '56'])).
% 12.23/12.44  thf('218', plain,
% 12.23/12.44      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44           (k5_relat_1 @ (k2_funct_1 @ sk_B_2) @ sk_B_2) @ (k6_relat_1 @ sk_A)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('sup-', [status(thm)], ['216', '217'])).
% 12.23/12.44  thf('219', plain,
% 12.23/12.44      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 12.23/12.44            (k6_relat_1 @ sk_A))
% 12.23/12.44         | ((sk_A) = (k1_xboole_0))))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('sup-', [status(thm)], ['204', '218'])).
% 12.23/12.44  thf('220', plain,
% 12.23/12.44      (![X48 : $i]:
% 12.23/12.44         (m1_subset_1 @ (k6_relat_1 @ X48) @ 
% 12.23/12.44          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X48)))),
% 12.23/12.44      inference('cnf', [status(esa)], [t29_relset_1])).
% 12.23/12.44  thf('221', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.23/12.44         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 12.23/12.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 12.23/12.44      inference('condensation', [status(thm)], ['72'])).
% 12.23/12.44  thf('222', plain,
% 12.23/12.44      (![X0 : $i]:
% 12.23/12.44         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['220', '221'])).
% 12.23/12.44  thf('223', plain,
% 12.23/12.44      ((((sk_A) = (k1_xboole_0)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('demod', [status(thm)], ['219', '222'])).
% 12.23/12.44  thf('224', plain, (((k2_relat_1 @ sk_B_2) = (sk_A))),
% 12.23/12.44      inference('demod', [status(thm)], ['191', '192', '195'])).
% 12.23/12.44  thf('225', plain,
% 12.23/12.44      (![X26 : $i]:
% 12.23/12.44         (((k2_relat_1 @ X26) != (k1_xboole_0))
% 12.23/12.44          | ((X26) = (k1_xboole_0))
% 12.23/12.44          | ~ (v1_relat_1 @ X26))),
% 12.23/12.44      inference('cnf', [status(esa)], [t64_relat_1])).
% 12.23/12.44  thf('226', plain,
% 12.23/12.44      ((((sk_A) != (k1_xboole_0))
% 12.23/12.44        | ~ (v1_relat_1 @ sk_B_2)
% 12.23/12.44        | ((sk_B_2) = (k1_xboole_0)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['224', '225'])).
% 12.23/12.44  thf('227', plain, ((v1_relat_1 @ sk_B_2)),
% 12.23/12.44      inference('demod', [status(thm)], ['171', '172'])).
% 12.23/12.44  thf('228', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0)))),
% 12.23/12.44      inference('demod', [status(thm)], ['226', '227'])).
% 12.23/12.44  thf('229', plain,
% 12.23/12.44      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0))))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('sup-', [status(thm)], ['223', '228'])).
% 12.23/12.44  thf('230', plain,
% 12.23/12.44      ((((sk_B_2) = (k1_xboole_0)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('simplify', [status(thm)], ['229'])).
% 12.23/12.44  thf('231', plain,
% 12.23/12.44      ((~ (v1_xboole_0 @ (k2_funct_1 @ k1_xboole_0)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('demod', [status(thm)], ['151', '230'])).
% 12.23/12.44  thf('232', plain,
% 12.23/12.44      ((((sk_A) = (k1_xboole_0)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('demod', [status(thm)], ['219', '222'])).
% 12.23/12.44  thf('233', plain, (((k2_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_2)) = (sk_A))),
% 12.23/12.44      inference('demod', [status(thm)], ['102', '105', '108'])).
% 12.23/12.44  thf('234', plain,
% 12.23/12.44      (![X26 : $i]:
% 12.23/12.44         (((k2_relat_1 @ X26) != (k1_xboole_0))
% 12.23/12.44          | ((X26) = (k1_xboole_0))
% 12.23/12.44          | ~ (v1_relat_1 @ X26))),
% 12.23/12.44      inference('cnf', [status(esa)], [t64_relat_1])).
% 12.23/12.44  thf('235', plain,
% 12.23/12.44      ((((sk_A) != (k1_xboole_0))
% 12.23/12.44        | ~ (v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_2))
% 12.23/12.44        | ((k2_funct_2 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['233', '234'])).
% 12.23/12.44  thf('236', plain, ((v1_relat_1 @ (k2_funct_2 @ sk_A @ sk_B_2))),
% 12.23/12.44      inference('sup-', [status(thm)], ['103', '104'])).
% 12.23/12.44  thf('237', plain,
% 12.23/12.44      ((((sk_A) != (k1_xboole_0))
% 12.23/12.44        | ((k2_funct_2 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 12.23/12.44      inference('demod', [status(thm)], ['235', '236'])).
% 12.23/12.44  thf('238', plain, (((k2_funct_2 @ sk_A @ sk_B_2) = (k2_funct_1 @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 12.23/12.44  thf('239', plain,
% 12.23/12.44      ((((sk_A) != (k1_xboole_0)) | ((k2_funct_1 @ sk_B_2) = (k1_xboole_0)))),
% 12.23/12.44      inference('demod', [status(thm)], ['237', '238'])).
% 12.23/12.44  thf('240', plain,
% 12.23/12.44      (((((k1_xboole_0) != (k1_xboole_0))
% 12.23/12.44         | ((k2_funct_1 @ sk_B_2) = (k1_xboole_0))))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('sup-', [status(thm)], ['232', '239'])).
% 12.23/12.44  thf('241', plain,
% 12.23/12.44      ((((k2_funct_1 @ sk_B_2) = (k1_xboole_0)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('simplify', [status(thm)], ['240'])).
% 12.23/12.44  thf('242', plain,
% 12.23/12.44      ((((sk_B_2) = (k1_xboole_0)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('simplify', [status(thm)], ['229'])).
% 12.23/12.44  thf('243', plain,
% 12.23/12.44      ((((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0)))
% 12.23/12.44         <= (~
% 12.23/12.44             ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44                (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44               (k6_partfun1 @ sk_A))))),
% 12.23/12.44      inference('demod', [status(thm)], ['241', '242'])).
% 12.23/12.44  thf('244', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 12.23/12.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 12.23/12.44  thf('245', plain,
% 12.23/12.44      (((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44          (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44         (k6_partfun1 @ sk_A)))),
% 12.23/12.44      inference('demod', [status(thm)], ['231', '243', '244'])).
% 12.23/12.44  thf('246', plain,
% 12.23/12.44      (~
% 12.23/12.44       ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ 
% 12.23/12.44          (k2_funct_2 @ sk_A @ sk_B_2)) @ 
% 12.23/12.44         (k6_partfun1 @ sk_A))) | 
% 12.23/12.44       ~
% 12.23/12.44       ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 12.23/12.44          (k2_funct_2 @ sk_A @ sk_B_2) @ sk_B_2) @ 
% 12.23/12.44         (k6_partfun1 @ sk_A)))),
% 12.23/12.44      inference('split', [status(esa)], ['0'])).
% 12.23/12.44  thf('247', plain,
% 12.23/12.44      (~
% 12.23/12.44       ((r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ 
% 12.23/12.44          (k2_funct_2 @ sk_A @ sk_B_2)) @ 
% 12.23/12.44         (k6_partfun1 @ sk_A)))),
% 12.23/12.44      inference('sat_resolution*', [status(thm)], ['245', '246'])).
% 12.23/12.44  thf('248', plain,
% 12.23/12.44      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ 
% 12.23/12.44           (k2_funct_1 @ sk_B_2)) @ 
% 12.23/12.44          (k6_relat_1 @ sk_A))),
% 12.23/12.44      inference('simpl_trail', [status(thm)], ['11', '247'])).
% 12.23/12.44  thf('249', plain,
% 12.23/12.44      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B_2) @ 
% 12.23/12.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 12.23/12.44  thf('250', plain, (((k2_funct_2 @ sk_A @ sk_B_2) = (k2_funct_1 @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 12.23/12.44  thf('251', plain,
% 12.23/12.44      ((m1_subset_1 @ (k2_funct_1 @ sk_B_2) @ 
% 12.23/12.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('demod', [status(thm)], ['249', '250'])).
% 12.23/12.44  thf('252', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('253', plain,
% 12.23/12.44      (![X70 : $i, X71 : $i, X72 : $i, X73 : $i, X74 : $i, X75 : $i]:
% 12.23/12.44         (~ (m1_subset_1 @ X70 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X71 @ X72)))
% 12.23/12.44          | ~ (v1_funct_1 @ X70)
% 12.23/12.44          | ~ (v1_funct_1 @ X73)
% 12.23/12.44          | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X74 @ X75)))
% 12.23/12.44          | ((k1_partfun1 @ X71 @ X72 @ X74 @ X75 @ X70 @ X73)
% 12.23/12.44              = (k5_relat_1 @ X70 @ X73)))),
% 12.23/12.44      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 12.23/12.44  thf('254', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.23/12.44         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_2 @ X0)
% 12.23/12.44            = (k5_relat_1 @ sk_B_2 @ X0))
% 12.23/12.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 12.23/12.44          | ~ (v1_funct_1 @ X0)
% 12.23/12.44          | ~ (v1_funct_1 @ sk_B_2))),
% 12.23/12.44      inference('sup-', [status(thm)], ['252', '253'])).
% 12.23/12.44  thf('255', plain, ((v1_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('256', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.23/12.44         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_2 @ X0)
% 12.23/12.44            = (k5_relat_1 @ sk_B_2 @ X0))
% 12.23/12.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 12.23/12.44          | ~ (v1_funct_1 @ X0))),
% 12.23/12.44      inference('demod', [status(thm)], ['254', '255'])).
% 12.23/12.44  thf('257', plain,
% 12.23/12.44      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_2))
% 12.23/12.44        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ 
% 12.23/12.44            (k2_funct_1 @ sk_B_2))
% 12.23/12.44            = (k5_relat_1 @ sk_B_2 @ (k2_funct_1 @ sk_B_2))))),
% 12.23/12.44      inference('sup-', [status(thm)], ['251', '256'])).
% 12.23/12.44  thf('258', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['95', '96', '97', '98'])).
% 12.23/12.44  thf('259', plain, (((k2_funct_2 @ sk_A @ sk_B_2) = (k2_funct_1 @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 12.23/12.44  thf('260', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['258', '259'])).
% 12.23/12.44  thf('261', plain,
% 12.23/12.44      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ 
% 12.23/12.44         (k2_funct_1 @ sk_B_2)) = (k5_relat_1 @ sk_B_2 @ (k2_funct_1 @ sk_B_2)))),
% 12.23/12.44      inference('demod', [status(thm)], ['257', '260'])).
% 12.23/12.44  thf('262', plain,
% 12.23/12.44      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44          (k5_relat_1 @ sk_B_2 @ (k2_funct_1 @ sk_B_2)) @ (k6_relat_1 @ sk_A))),
% 12.23/12.44      inference('demod', [status(thm)], ['248', '261'])).
% 12.23/12.44  thf('263', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('264', plain,
% 12.23/12.44      (![X79 : $i, X80 : $i, X81 : $i]:
% 12.23/12.44         (((X79) = (k1_xboole_0))
% 12.23/12.44          | ~ (v1_funct_1 @ X80)
% 12.23/12.44          | ~ (v1_funct_2 @ X80 @ X81 @ X79)
% 12.23/12.44          | ~ (m1_subset_1 @ X80 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X81 @ X79)))
% 12.23/12.44          | ((k5_relat_1 @ X80 @ (k2_funct_1 @ X80)) = (k6_partfun1 @ X81))
% 12.23/12.44          | ~ (v2_funct_1 @ X80)
% 12.23/12.44          | ((k2_relset_1 @ X81 @ X79 @ X80) != (X79)))),
% 12.23/12.44      inference('cnf', [status(esa)], [t35_funct_2])).
% 12.23/12.44  thf('265', plain, (![X78 : $i]: ((k6_partfun1 @ X78) = (k6_relat_1 @ X78))),
% 12.23/12.44      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 12.23/12.44  thf('266', plain,
% 12.23/12.44      (![X79 : $i, X80 : $i, X81 : $i]:
% 12.23/12.44         (((X79) = (k1_xboole_0))
% 12.23/12.44          | ~ (v1_funct_1 @ X80)
% 12.23/12.44          | ~ (v1_funct_2 @ X80 @ X81 @ X79)
% 12.23/12.44          | ~ (m1_subset_1 @ X80 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X81 @ X79)))
% 12.23/12.44          | ((k5_relat_1 @ X80 @ (k2_funct_1 @ X80)) = (k6_relat_1 @ X81))
% 12.23/12.44          | ~ (v2_funct_1 @ X80)
% 12.23/12.44          | ((k2_relset_1 @ X81 @ X79 @ X80) != (X79)))),
% 12.23/12.44      inference('demod', [status(thm)], ['264', '265'])).
% 12.23/12.44  thf('267', plain,
% 12.23/12.44      ((((k2_relset_1 @ sk_A @ sk_A @ sk_B_2) != (sk_A))
% 12.23/12.44        | ~ (v2_funct_1 @ sk_B_2)
% 12.23/12.44        | ((k5_relat_1 @ sk_B_2 @ (k2_funct_1 @ sk_B_2)) = (k6_relat_1 @ sk_A))
% 12.23/12.44        | ~ (v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)
% 12.23/12.44        | ~ (v1_funct_1 @ sk_B_2)
% 12.23/12.44        | ((sk_A) = (k1_xboole_0)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['263', '266'])).
% 12.23/12.44  thf('268', plain,
% 12.23/12.44      (((k9_relat_1 @ sk_B_2 @ sk_A) = (k2_relset_1 @ sk_A @ sk_A @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['159', '162'])).
% 12.23/12.44  thf('269', plain, ((v2_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('demod', [status(thm)], ['177', '178', '179'])).
% 12.23/12.44  thf('270', plain, ((v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('271', plain, ((v1_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('272', plain,
% 12.23/12.44      ((((k9_relat_1 @ sk_B_2 @ sk_A) != (sk_A))
% 12.23/12.44        | ((k5_relat_1 @ sk_B_2 @ (k2_funct_1 @ sk_B_2)) = (k6_relat_1 @ sk_A))
% 12.23/12.44        | ((sk_A) = (k1_xboole_0)))),
% 12.23/12.44      inference('demod', [status(thm)], ['267', '268', '269', '270', '271'])).
% 12.23/12.44  thf('273', plain, (((k9_relat_1 @ sk_B_2 @ sk_A) = (sk_A))),
% 12.23/12.44      inference('demod', [status(thm)], ['183', '196', '197'])).
% 12.23/12.44  thf('274', plain,
% 12.23/12.44      ((((sk_A) != (sk_A))
% 12.23/12.44        | ((k5_relat_1 @ sk_B_2 @ (k2_funct_1 @ sk_B_2)) = (k6_relat_1 @ sk_A))
% 12.23/12.44        | ((sk_A) = (k1_xboole_0)))),
% 12.23/12.44      inference('demod', [status(thm)], ['272', '273'])).
% 12.23/12.44  thf('275', plain,
% 12.23/12.44      ((((sk_A) = (k1_xboole_0))
% 12.23/12.44        | ((k5_relat_1 @ sk_B_2 @ (k2_funct_1 @ sk_B_2)) = (k6_relat_1 @ sk_A)))),
% 12.23/12.44      inference('simplify', [status(thm)], ['274'])).
% 12.23/12.44  thf('276', plain,
% 12.23/12.44      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 12.23/12.44          (k5_relat_1 @ sk_B_2 @ (k2_funct_1 @ sk_B_2)) @ (k6_relat_1 @ sk_A))),
% 12.23/12.44      inference('demod', [status(thm)], ['248', '261'])).
% 12.23/12.44  thf('277', plain,
% 12.23/12.44      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 12.23/12.44           (k6_relat_1 @ sk_A))
% 12.23/12.44        | ((sk_A) = (k1_xboole_0)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['275', '276'])).
% 12.23/12.44  thf('278', plain,
% 12.23/12.44      (![X0 : $i]:
% 12.23/12.44         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['220', '221'])).
% 12.23/12.44  thf('279', plain, (((sk_A) = (k1_xboole_0))),
% 12.23/12.44      inference('demod', [status(thm)], ['277', '278'])).
% 12.23/12.44  thf('280', plain, (((sk_A) = (k1_xboole_0))),
% 12.23/12.44      inference('demod', [status(thm)], ['277', '278'])).
% 12.23/12.44  thf('281', plain, (((sk_A) = (k1_xboole_0))),
% 12.23/12.44      inference('demod', [status(thm)], ['277', '278'])).
% 12.23/12.44  thf('282', plain,
% 12.23/12.44      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 12.23/12.44      inference('sup+', [status(thm)], ['62', '63'])).
% 12.23/12.44  thf('283', plain,
% 12.23/12.44      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 12.23/12.44      inference('simplify', [status(thm)], ['61'])).
% 12.23/12.44  thf(cc4_relset_1, axiom,
% 12.23/12.44    (![A:$i,B:$i]:
% 12.23/12.44     ( ( v1_xboole_0 @ A ) =>
% 12.23/12.44       ( ![C:$i]:
% 12.23/12.44         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 12.23/12.44           ( v1_xboole_0 @ C ) ) ) ))).
% 12.23/12.44  thf('284', plain,
% 12.23/12.44      (![X34 : $i, X35 : $i, X36 : $i]:
% 12.23/12.44         (~ (v1_xboole_0 @ X34)
% 12.23/12.44          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 12.23/12.44          | (v1_xboole_0 @ X35))),
% 12.23/12.44      inference('cnf', [status(esa)], [cc4_relset_1])).
% 12.23/12.44  thf('285', plain,
% 12.23/12.44      (![X1 : $i]:
% 12.23/12.44         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 12.23/12.44          | (v1_xboole_0 @ X1)
% 12.23/12.44          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['283', '284'])).
% 12.23/12.44  thf('286', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 12.23/12.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 12.23/12.44  thf('287', plain,
% 12.23/12.44      (![X1 : $i]:
% 12.23/12.44         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 12.23/12.44          | (v1_xboole_0 @ X1))),
% 12.23/12.44      inference('demod', [status(thm)], ['285', '286'])).
% 12.23/12.44  thf('288', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['282', '287'])).
% 12.23/12.44  thf('289', plain,
% 12.23/12.44      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['13', '14'])).
% 12.23/12.44  thf('290', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['288', '289'])).
% 12.23/12.44  thf('291', plain,
% 12.23/12.44      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 12.23/12.44          (k5_relat_1 @ sk_B_2 @ (k2_funct_1 @ sk_B_2)) @ k1_xboole_0)),
% 12.23/12.44      inference('demod', [status(thm)], ['262', '279', '280', '281', '290'])).
% 12.23/12.44  thf('292', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0)))),
% 12.23/12.44      inference('demod', [status(thm)], ['226', '227'])).
% 12.23/12.44  thf('293', plain, (((sk_A) = (k1_xboole_0))),
% 12.23/12.44      inference('demod', [status(thm)], ['277', '278'])).
% 12.23/12.44  thf('294', plain,
% 12.23/12.44      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0)))),
% 12.23/12.44      inference('demod', [status(thm)], ['292', '293'])).
% 12.23/12.44  thf('295', plain, (((sk_B_2) = (k1_xboole_0))),
% 12.23/12.44      inference('simplify', [status(thm)], ['294'])).
% 12.23/12.44  thf('296', plain, (((sk_B_2) = (k1_xboole_0))),
% 12.23/12.44      inference('simplify', [status(thm)], ['294'])).
% 12.23/12.44  thf('297', plain,
% 12.23/12.44      ((((sk_A) != (k1_xboole_0)) | ((k2_funct_1 @ sk_B_2) = (k1_xboole_0)))),
% 12.23/12.44      inference('demod', [status(thm)], ['237', '238'])).
% 12.23/12.44  thf('298', plain, (((sk_A) = (k1_xboole_0))),
% 12.23/12.44      inference('demod', [status(thm)], ['277', '278'])).
% 12.23/12.44  thf('299', plain,
% 12.23/12.44      ((((k1_xboole_0) != (k1_xboole_0))
% 12.23/12.44        | ((k2_funct_1 @ sk_B_2) = (k1_xboole_0)))),
% 12.23/12.44      inference('demod', [status(thm)], ['297', '298'])).
% 12.23/12.44  thf('300', plain, (((k2_funct_1 @ sk_B_2) = (k1_xboole_0))),
% 12.23/12.44      inference('simplify', [status(thm)], ['299'])).
% 12.23/12.44  thf('301', plain, (((sk_B_2) = (k1_xboole_0))),
% 12.23/12.44      inference('simplify', [status(thm)], ['294'])).
% 12.23/12.44  thf('302', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 12.23/12.44      inference('demod', [status(thm)], ['300', '301'])).
% 12.23/12.44  thf('303', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('304', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.23/12.44         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_2 @ X0)
% 12.23/12.44            = (k5_relat_1 @ sk_B_2 @ X0))
% 12.23/12.44          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 12.23/12.44          | ~ (v1_funct_1 @ X0))),
% 12.23/12.44      inference('demod', [status(thm)], ['254', '255'])).
% 12.23/12.44  thf('305', plain,
% 12.23/12.44      ((~ (v1_funct_1 @ sk_B_2)
% 12.23/12.44        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ sk_B_2)
% 12.23/12.44            = (k5_relat_1 @ sk_B_2 @ sk_B_2)))),
% 12.23/12.44      inference('sup-', [status(thm)], ['303', '304'])).
% 12.23/12.44  thf('306', plain, ((v1_funct_1 @ sk_B_2)),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('307', plain,
% 12.23/12.44      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_2 @ sk_B_2)
% 12.23/12.44         = (k5_relat_1 @ sk_B_2 @ sk_B_2))),
% 12.23/12.44      inference('demod', [status(thm)], ['305', '306'])).
% 12.23/12.44  thf('308', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.23/12.44         (((k1_partfun1 @ X2 @ X1 @ sk_A @ sk_A @ X0 @ sk_B_2) = (k1_xboole_0))
% 12.23/12.44          | ~ (v1_xboole_0 @ X2)
% 12.23/12.44          | ~ (v1_xboole_0 @ X0))),
% 12.23/12.44      inference('sup-', [status(thm)], ['12', '51'])).
% 12.23/12.44  thf('309', plain,
% 12.23/12.44      ((((k5_relat_1 @ sk_B_2 @ sk_B_2) = (k1_xboole_0))
% 12.23/12.44        | ~ (v1_xboole_0 @ sk_B_2)
% 12.23/12.44        | ~ (v1_xboole_0 @ sk_A))),
% 12.23/12.44      inference('sup+', [status(thm)], ['307', '308'])).
% 12.23/12.44  thf('310', plain,
% 12.23/12.44      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 12.23/12.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.23/12.44  thf('311', plain,
% 12.23/12.44      (![X34 : $i, X35 : $i, X36 : $i]:
% 12.23/12.44         (~ (v1_xboole_0 @ X34)
% 12.23/12.44          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 12.23/12.44          | (v1_xboole_0 @ X35))),
% 12.23/12.44      inference('cnf', [status(esa)], [cc4_relset_1])).
% 12.23/12.44  thf('312', plain, (((v1_xboole_0 @ sk_B_2) | ~ (v1_xboole_0 @ sk_A))),
% 12.23/12.44      inference('sup-', [status(thm)], ['310', '311'])).
% 12.23/12.44  thf('313', plain,
% 12.23/12.44      ((~ (v1_xboole_0 @ sk_A)
% 12.23/12.44        | ((k5_relat_1 @ sk_B_2 @ sk_B_2) = (k1_xboole_0)))),
% 12.23/12.44      inference('clc', [status(thm)], ['309', '312'])).
% 12.23/12.44  thf('314', plain, (((sk_A) = (k1_xboole_0))),
% 12.23/12.44      inference('demod', [status(thm)], ['277', '278'])).
% 12.23/12.44  thf('315', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 12.23/12.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 12.23/12.44  thf('316', plain, (((k5_relat_1 @ sk_B_2 @ sk_B_2) = (k1_xboole_0))),
% 12.23/12.44      inference('demod', [status(thm)], ['313', '314', '315'])).
% 12.23/12.44  thf('317', plain, (((sk_B_2) = (k1_xboole_0))),
% 12.23/12.44      inference('simplify', [status(thm)], ['294'])).
% 12.23/12.44  thf('318', plain, (((sk_B_2) = (k1_xboole_0))),
% 12.23/12.44      inference('simplify', [status(thm)], ['294'])).
% 12.23/12.44  thf('319', plain,
% 12.23/12.44      (((k5_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 12.23/12.44      inference('demod', [status(thm)], ['316', '317', '318'])).
% 12.23/12.44  thf('320', plain,
% 12.23/12.44      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 12.23/12.44      inference('sup-', [status(thm)], ['71', '73'])).
% 12.23/12.44  thf('321', plain, ($false),
% 12.23/12.44      inference('demod', [status(thm)],
% 12.23/12.44                ['291', '295', '296', '302', '319', '320'])).
% 12.23/12.44  
% 12.23/12.44  % SZS output end Refutation
% 12.23/12.44  
% 12.23/12.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
