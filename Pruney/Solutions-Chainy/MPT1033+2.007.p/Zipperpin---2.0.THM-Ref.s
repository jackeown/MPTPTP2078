%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KbBEDx6AVL

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:05 EST 2020

% Result     : Theorem 3.89s
% Output     : Refutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 270 expanded)
%              Number of leaves         :   29 (  89 expanded)
%              Depth                    :   19
%              Number of atoms          :  776 (3664 expanded)
%              Number of equality atoms :   65 ( 272 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(t142_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_3 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('3',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( X49 = X46 )
      | ~ ( r1_partfun1 @ X49 @ X46 )
      | ~ ( v1_partfun1 @ X46 @ X47 )
      | ~ ( v1_partfun1 @ X49 @ X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( v1_partfun1 @ X35 @ X36 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X35 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_3 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('11',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_2 @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B_3 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_B_3 != k1_xboole_0 )
   <= ( sk_B_3 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_3 ) )
   <= ( sk_B_3 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_3 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_3 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ sk_B_3 )
   <= ( sk_B_3 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('23',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_3 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_3 @ sk_C_1 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_2 @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_3 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_2 @ sk_C_1 ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('40',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_3 @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','40'])).

thf('42',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_2 @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('43',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_3 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( sk_D = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_2 @ sk_D ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,
    ( ( ( sk_D = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('57',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('58',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['41','56','60'])).

thf('62',plain,
    ( ( sk_B_3 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('63',plain,(
    sk_B_3 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v1_xboole_0 @ sk_B_3 ) ),
    inference(simpl_trail,[status(thm)],['21','63'])).

thf('65',plain,(
    v1_partfun1 @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['10','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['4','65','66'])).

thf('68',plain,
    ( ( sk_C_1 = sk_D )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','67'])).

thf('69',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( v1_partfun1 @ X35 @ X36 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X35 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('72',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_3 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ sk_B_3 ) ),
    inference(simpl_trail,[status(thm)],['21','63'])).

thf('77',plain,(
    v1_partfun1 @ sk_C_1 @ sk_A ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    sk_C_1 = sk_D ),
    inference(demod,[status(thm)],['68','69','77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['58'])).

thf('82',plain,(
    r2_relset_1 @ sk_A @ sk_B_3 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KbBEDx6AVL
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.89/4.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.89/4.09  % Solved by: fo/fo7.sh
% 3.89/4.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.89/4.09  % done 3615 iterations in 3.630s
% 3.89/4.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.89/4.09  % SZS output start Refutation
% 3.89/4.09  thf(sk_D_type, type, sk_D: $i).
% 3.89/4.09  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.89/4.09  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.89/4.09  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.89/4.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.89/4.09  thf(sk_B_3_type, type, sk_B_3: $i).
% 3.89/4.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.89/4.09  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.89/4.09  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.89/4.09  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.89/4.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.89/4.09  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 3.89/4.09  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.89/4.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.89/4.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.89/4.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.89/4.09  thf(sk_A_type, type, sk_A: $i).
% 3.89/4.09  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 3.89/4.09  thf(t142_funct_2, conjecture,
% 3.89/4.09    (![A:$i,B:$i,C:$i]:
% 3.89/4.09     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.89/4.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.89/4.09       ( ![D:$i]:
% 3.89/4.09         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.89/4.09             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.89/4.09           ( ( r1_partfun1 @ C @ D ) =>
% 3.89/4.09             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 3.89/4.09               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 3.89/4.09  thf(zf_stmt_0, negated_conjecture,
% 3.89/4.09    (~( ![A:$i,B:$i,C:$i]:
% 3.89/4.09        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.89/4.09            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.89/4.09          ( ![D:$i]:
% 3.89/4.09            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.89/4.09                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.89/4.09              ( ( r1_partfun1 @ C @ D ) =>
% 3.89/4.09                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 3.89/4.09                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 3.89/4.09    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 3.89/4.09  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_3 @ sk_C_1 @ sk_D)),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf('1', plain,
% 3.89/4.09      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf('2', plain,
% 3.89/4.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf(t148_partfun1, axiom,
% 3.89/4.09    (![A:$i,B:$i,C:$i]:
% 3.89/4.09     ( ( ( v1_funct_1 @ C ) & 
% 3.89/4.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.89/4.09       ( ![D:$i]:
% 3.89/4.09         ( ( ( v1_funct_1 @ D ) & 
% 3.89/4.09             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.89/4.09           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 3.89/4.09               ( r1_partfun1 @ C @ D ) ) =>
% 3.89/4.09             ( ( C ) = ( D ) ) ) ) ) ))).
% 3.89/4.09  thf('3', plain,
% 3.89/4.09      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 3.89/4.09         (~ (v1_funct_1 @ X46)
% 3.89/4.09          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 3.89/4.09          | ((X49) = (X46))
% 3.89/4.09          | ~ (r1_partfun1 @ X49 @ X46)
% 3.89/4.09          | ~ (v1_partfun1 @ X46 @ X47)
% 3.89/4.09          | ~ (v1_partfun1 @ X49 @ X47)
% 3.89/4.09          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 3.89/4.09          | ~ (v1_funct_1 @ X49))),
% 3.89/4.09      inference('cnf', [status(esa)], [t148_partfun1])).
% 3.89/4.09  thf('4', plain,
% 3.89/4.09      (![X0 : $i]:
% 3.89/4.09         (~ (v1_funct_1 @ X0)
% 3.89/4.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))
% 3.89/4.09          | ~ (v1_partfun1 @ X0 @ sk_A)
% 3.89/4.09          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 3.89/4.09          | ~ (r1_partfun1 @ X0 @ sk_D)
% 3.89/4.09          | ((X0) = (sk_D))
% 3.89/4.09          | ~ (v1_funct_1 @ sk_D))),
% 3.89/4.09      inference('sup-', [status(thm)], ['2', '3'])).
% 3.89/4.09  thf('5', plain,
% 3.89/4.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf(cc5_funct_2, axiom,
% 3.89/4.09    (![A:$i,B:$i]:
% 3.89/4.09     ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.89/4.09       ( ![C:$i]:
% 3.89/4.09         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.89/4.09           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 3.89/4.09             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 3.89/4.09  thf('6', plain,
% 3.89/4.09      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.89/4.09         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 3.89/4.09          | (v1_partfun1 @ X35 @ X36)
% 3.89/4.09          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 3.89/4.09          | ~ (v1_funct_1 @ X35)
% 3.89/4.09          | (v1_xboole_0 @ X37))),
% 3.89/4.09      inference('cnf', [status(esa)], [cc5_funct_2])).
% 3.89/4.09  thf('7', plain,
% 3.89/4.09      (((v1_xboole_0 @ sk_B_3)
% 3.89/4.09        | ~ (v1_funct_1 @ sk_D)
% 3.89/4.09        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_3)
% 3.89/4.09        | (v1_partfun1 @ sk_D @ sk_A))),
% 3.89/4.09      inference('sup-', [status(thm)], ['5', '6'])).
% 3.89/4.09  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_3)),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf('10', plain, (((v1_xboole_0 @ sk_B_3) | (v1_partfun1 @ sk_D @ sk_A))),
% 3.89/4.09      inference('demod', [status(thm)], ['7', '8', '9'])).
% 3.89/4.09  thf(t9_mcart_1, axiom,
% 3.89/4.09    (![A:$i]:
% 3.89/4.09     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.89/4.09          ( ![B:$i]:
% 3.89/4.09            ( ~( ( r2_hidden @ B @ A ) & 
% 3.89/4.09                 ( ![C:$i,D:$i]:
% 3.89/4.09                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 3.89/4.09                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 3.89/4.09  thf('11', plain,
% 3.89/4.09      (![X32 : $i]:
% 3.89/4.09         (((X32) = (k1_xboole_0)) | (r2_hidden @ (sk_B_2 @ X32) @ X32))),
% 3.89/4.09      inference('cnf', [status(esa)], [t9_mcart_1])).
% 3.89/4.09  thf(d1_xboole_0, axiom,
% 3.89/4.09    (![A:$i]:
% 3.89/4.09     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.89/4.09  thf('12', plain,
% 3.89/4.09      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.89/4.09      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.89/4.09  thf('13', plain,
% 3.89/4.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.89/4.09      inference('sup-', [status(thm)], ['11', '12'])).
% 3.89/4.09  thf('14', plain,
% 3.89/4.09      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.89/4.09      inference('sup-', [status(thm)], ['11', '12'])).
% 3.89/4.09  thf('15', plain,
% 3.89/4.09      (![X0 : $i, X1 : $i]:
% 3.89/4.09         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 3.89/4.09      inference('sup+', [status(thm)], ['13', '14'])).
% 3.89/4.09  thf('16', plain, ((((sk_B_3) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf('17', plain,
% 3.89/4.09      ((((sk_B_3) != (k1_xboole_0))) <= (~ (((sk_B_3) = (k1_xboole_0))))),
% 3.89/4.09      inference('split', [status(esa)], ['16'])).
% 3.89/4.09  thf('18', plain,
% 3.89/4.09      ((![X0 : $i]:
% 3.89/4.09          (((X0) != (k1_xboole_0))
% 3.89/4.09           | ~ (v1_xboole_0 @ X0)
% 3.89/4.09           | ~ (v1_xboole_0 @ sk_B_3)))
% 3.89/4.09         <= (~ (((sk_B_3) = (k1_xboole_0))))),
% 3.89/4.09      inference('sup-', [status(thm)], ['15', '17'])).
% 3.89/4.09  thf('19', plain,
% 3.89/4.09      (((~ (v1_xboole_0 @ sk_B_3) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 3.89/4.09         <= (~ (((sk_B_3) = (k1_xboole_0))))),
% 3.89/4.09      inference('simplify', [status(thm)], ['18'])).
% 3.89/4.09  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.89/4.09  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.89/4.09      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.89/4.09  thf('21', plain,
% 3.89/4.09      ((~ (v1_xboole_0 @ sk_B_3)) <= (~ (((sk_B_3) = (k1_xboole_0))))),
% 3.89/4.09      inference('simplify_reflect+', [status(thm)], ['19', '20'])).
% 3.89/4.09  thf('22', plain,
% 3.89/4.09      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('split', [status(esa)], ['16'])).
% 3.89/4.09  thf('23', plain, (~ (r2_relset_1 @ sk_A @ sk_B_3 @ sk_C_1 @ sk_D)),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf('24', plain,
% 3.89/4.09      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_3 @ sk_C_1 @ sk_D))
% 3.89/4.09         <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('sup-', [status(thm)], ['22', '23'])).
% 3.89/4.09  thf('25', plain,
% 3.89/4.09      (![X32 : $i]:
% 3.89/4.09         (((X32) = (k1_xboole_0)) | (r2_hidden @ (sk_B_2 @ X32) @ X32))),
% 3.89/4.09      inference('cnf', [status(esa)], [t9_mcart_1])).
% 3.89/4.09  thf(t113_zfmisc_1, axiom,
% 3.89/4.09    (![A:$i,B:$i]:
% 3.89/4.09     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.89/4.09       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.89/4.09  thf('26', plain,
% 3.89/4.09      (![X8 : $i, X9 : $i]:
% 3.89/4.09         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 3.89/4.09      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.89/4.09  thf('27', plain,
% 3.89/4.09      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 3.89/4.09      inference('simplify', [status(thm)], ['26'])).
% 3.89/4.09  thf('28', plain,
% 3.89/4.09      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('split', [status(esa)], ['16'])).
% 3.89/4.09  thf('29', plain,
% 3.89/4.09      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf('30', plain,
% 3.89/4.09      (((m1_subset_1 @ sk_C_1 @ 
% 3.89/4.09         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_3))))
% 3.89/4.09         <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('sup+', [status(thm)], ['28', '29'])).
% 3.89/4.09  thf('31', plain,
% 3.89/4.09      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 3.89/4.09         <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('sup+', [status(thm)], ['27', '30'])).
% 3.89/4.09  thf(t3_subset, axiom,
% 3.89/4.09    (![A:$i,B:$i]:
% 3.89/4.09     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.89/4.09  thf('32', plain,
% 3.89/4.09      (![X12 : $i, X13 : $i]:
% 3.89/4.09         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 3.89/4.09      inference('cnf', [status(esa)], [t3_subset])).
% 3.89/4.09  thf('33', plain,
% 3.89/4.09      (((r1_tarski @ sk_C_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('sup-', [status(thm)], ['31', '32'])).
% 3.89/4.09  thf(d3_tarski, axiom,
% 3.89/4.09    (![A:$i,B:$i]:
% 3.89/4.09     ( ( r1_tarski @ A @ B ) <=>
% 3.89/4.09       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.89/4.09  thf('34', plain,
% 3.89/4.09      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.89/4.09         (~ (r2_hidden @ X3 @ X4)
% 3.89/4.09          | (r2_hidden @ X3 @ X5)
% 3.89/4.09          | ~ (r1_tarski @ X4 @ X5))),
% 3.89/4.09      inference('cnf', [status(esa)], [d3_tarski])).
% 3.89/4.09  thf('35', plain,
% 3.89/4.09      ((![X0 : $i]:
% 3.89/4.09          ((r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C_1)))
% 3.89/4.09         <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('sup-', [status(thm)], ['33', '34'])).
% 3.89/4.09  thf('36', plain,
% 3.89/4.09      (((((sk_C_1) = (k1_xboole_0))
% 3.89/4.09         | (r2_hidden @ (sk_B_2 @ sk_C_1) @ k1_xboole_0)))
% 3.89/4.09         <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('sup-', [status(thm)], ['25', '35'])).
% 3.89/4.09  thf('37', plain,
% 3.89/4.09      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.89/4.09      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.89/4.09  thf('38', plain,
% 3.89/4.09      (((((sk_C_1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 3.89/4.09         <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('sup-', [status(thm)], ['36', '37'])).
% 3.89/4.09  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.89/4.09      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.89/4.09  thf('40', plain,
% 3.89/4.09      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('demod', [status(thm)], ['38', '39'])).
% 3.89/4.09  thf('41', plain,
% 3.89/4.09      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_3 @ k1_xboole_0 @ sk_D))
% 3.89/4.09         <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('demod', [status(thm)], ['24', '40'])).
% 3.89/4.09  thf('42', plain,
% 3.89/4.09      (![X32 : $i]:
% 3.89/4.09         (((X32) = (k1_xboole_0)) | (r2_hidden @ (sk_B_2 @ X32) @ X32))),
% 3.89/4.09      inference('cnf', [status(esa)], [t9_mcart_1])).
% 3.89/4.09  thf('43', plain,
% 3.89/4.09      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 3.89/4.09      inference('simplify', [status(thm)], ['26'])).
% 3.89/4.09  thf('44', plain,
% 3.89/4.09      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('split', [status(esa)], ['16'])).
% 3.89/4.09  thf('45', plain,
% 3.89/4.09      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf('46', plain,
% 3.89/4.09      (((m1_subset_1 @ sk_D @ 
% 3.89/4.09         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_3))))
% 3.89/4.09         <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('sup+', [status(thm)], ['44', '45'])).
% 3.89/4.09  thf('47', plain,
% 3.89/4.09      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 3.89/4.09         <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('sup+', [status(thm)], ['43', '46'])).
% 3.89/4.09  thf('48', plain,
% 3.89/4.09      (![X12 : $i, X13 : $i]:
% 3.89/4.09         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 3.89/4.09      inference('cnf', [status(esa)], [t3_subset])).
% 3.89/4.09  thf('49', plain,
% 3.89/4.09      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('sup-', [status(thm)], ['47', '48'])).
% 3.89/4.09  thf('50', plain,
% 3.89/4.09      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.89/4.09         (~ (r2_hidden @ X3 @ X4)
% 3.89/4.09          | (r2_hidden @ X3 @ X5)
% 3.89/4.09          | ~ (r1_tarski @ X4 @ X5))),
% 3.89/4.09      inference('cnf', [status(esa)], [d3_tarski])).
% 3.89/4.09  thf('51', plain,
% 3.89/4.09      ((![X0 : $i]:
% 3.89/4.09          ((r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 3.89/4.09         <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('sup-', [status(thm)], ['49', '50'])).
% 3.89/4.09  thf('52', plain,
% 3.89/4.09      (((((sk_D) = (k1_xboole_0)) | (r2_hidden @ (sk_B_2 @ sk_D) @ k1_xboole_0)))
% 3.89/4.09         <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('sup-', [status(thm)], ['42', '51'])).
% 3.89/4.09  thf('53', plain,
% 3.89/4.09      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.89/4.09      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.89/4.09  thf('54', plain,
% 3.89/4.09      (((((sk_D) = (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 3.89/4.09         <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('sup-', [status(thm)], ['52', '53'])).
% 3.89/4.09  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.89/4.09      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.89/4.09  thf('56', plain,
% 3.89/4.09      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.89/4.09      inference('demod', [status(thm)], ['54', '55'])).
% 3.89/4.09  thf(t4_subset_1, axiom,
% 3.89/4.09    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.89/4.09  thf('57', plain,
% 3.89/4.09      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 3.89/4.09      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.89/4.09  thf(reflexivity_r2_relset_1, axiom,
% 3.89/4.09    (![A:$i,B:$i,C:$i,D:$i]:
% 3.89/4.09     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.89/4.09         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.89/4.09       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 3.89/4.09  thf('58', plain,
% 3.89/4.09      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.89/4.09         ((r2_relset_1 @ X24 @ X25 @ X26 @ X26)
% 3.89/4.09          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 3.89/4.09          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 3.89/4.09      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 3.89/4.09  thf('59', plain,
% 3.89/4.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.09         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 3.89/4.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.89/4.09      inference('condensation', [status(thm)], ['58'])).
% 3.89/4.09  thf('60', plain,
% 3.89/4.09      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 3.89/4.09      inference('sup-', [status(thm)], ['57', '59'])).
% 3.89/4.09  thf('61', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 3.89/4.09      inference('demod', [status(thm)], ['41', '56', '60'])).
% 3.89/4.09  thf('62', plain,
% 3.89/4.09      (~ (((sk_B_3) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 3.89/4.09      inference('split', [status(esa)], ['16'])).
% 3.89/4.09  thf('63', plain, (~ (((sk_B_3) = (k1_xboole_0)))),
% 3.89/4.09      inference('sat_resolution*', [status(thm)], ['61', '62'])).
% 3.89/4.09  thf('64', plain, (~ (v1_xboole_0 @ sk_B_3)),
% 3.89/4.09      inference('simpl_trail', [status(thm)], ['21', '63'])).
% 3.89/4.09  thf('65', plain, ((v1_partfun1 @ sk_D @ sk_A)),
% 3.89/4.09      inference('clc', [status(thm)], ['10', '64'])).
% 3.89/4.09  thf('66', plain, ((v1_funct_1 @ sk_D)),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf('67', plain,
% 3.89/4.09      (![X0 : $i]:
% 3.89/4.09         (~ (v1_funct_1 @ X0)
% 3.89/4.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))
% 3.89/4.09          | ~ (v1_partfun1 @ X0 @ sk_A)
% 3.89/4.09          | ~ (r1_partfun1 @ X0 @ sk_D)
% 3.89/4.09          | ((X0) = (sk_D)))),
% 3.89/4.09      inference('demod', [status(thm)], ['4', '65', '66'])).
% 3.89/4.09  thf('68', plain,
% 3.89/4.09      ((((sk_C_1) = (sk_D))
% 3.89/4.09        | ~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 3.89/4.09        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 3.89/4.09        | ~ (v1_funct_1 @ sk_C_1))),
% 3.89/4.09      inference('sup-', [status(thm)], ['1', '67'])).
% 3.89/4.09  thf('69', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf('70', plain,
% 3.89/4.09      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf('71', plain,
% 3.89/4.09      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.89/4.09         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 3.89/4.09          | (v1_partfun1 @ X35 @ X36)
% 3.89/4.09          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 3.89/4.09          | ~ (v1_funct_1 @ X35)
% 3.89/4.09          | (v1_xboole_0 @ X37))),
% 3.89/4.09      inference('cnf', [status(esa)], [cc5_funct_2])).
% 3.89/4.09  thf('72', plain,
% 3.89/4.09      (((v1_xboole_0 @ sk_B_3)
% 3.89/4.09        | ~ (v1_funct_1 @ sk_C_1)
% 3.89/4.09        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_3)
% 3.89/4.09        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 3.89/4.09      inference('sup-', [status(thm)], ['70', '71'])).
% 3.89/4.09  thf('73', plain, ((v1_funct_1 @ sk_C_1)),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf('74', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_3)),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf('75', plain, (((v1_xboole_0 @ sk_B_3) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 3.89/4.09      inference('demod', [status(thm)], ['72', '73', '74'])).
% 3.89/4.09  thf('76', plain, (~ (v1_xboole_0 @ sk_B_3)),
% 3.89/4.09      inference('simpl_trail', [status(thm)], ['21', '63'])).
% 3.89/4.09  thf('77', plain, ((v1_partfun1 @ sk_C_1 @ sk_A)),
% 3.89/4.09      inference('clc', [status(thm)], ['75', '76'])).
% 3.89/4.09  thf('78', plain, ((v1_funct_1 @ sk_C_1)),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf('79', plain, (((sk_C_1) = (sk_D))),
% 3.89/4.09      inference('demod', [status(thm)], ['68', '69', '77', '78'])).
% 3.89/4.09  thf('80', plain,
% 3.89/4.09      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 3.89/4.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.89/4.09  thf('81', plain,
% 3.89/4.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.89/4.09         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 3.89/4.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 3.89/4.09      inference('condensation', [status(thm)], ['58'])).
% 3.89/4.09  thf('82', plain, ((r2_relset_1 @ sk_A @ sk_B_3 @ sk_C_1 @ sk_C_1)),
% 3.89/4.09      inference('sup-', [status(thm)], ['80', '81'])).
% 3.89/4.09  thf('83', plain, ($false),
% 3.89/4.09      inference('demod', [status(thm)], ['0', '79', '82'])).
% 3.89/4.09  
% 3.89/4.09  % SZS output end Refutation
% 3.89/4.09  
% 3.89/4.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
