%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AG3M7RR1Gh

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 575 expanded)
%              Number of leaves         :   26 ( 180 expanded)
%              Depth                    :   20
%              Number of atoms          :  991 (10278 expanded)
%              Number of equality atoms :   43 ( 330 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t146_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r1_partfun1 @ B @ C )
          <=> ! [D: $i] :
                ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) )
               => ( ( k1_funct_1 @ B @ D )
                  = ( k1_funct_1 @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r1_partfun1 @ B @ C )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) )
                 => ( ( k1_funct_1 @ B @ D )
                    = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_2])).

thf('0',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X21: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
      | ( ( k1_funct_1 @ sk_B @ X21 )
        = ( k1_funct_1 @ sk_C_2 @ X21 ) )
      | ( r1_partfun1 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C_2 )
    | ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = ( k1_funct_1 @ sk_C_2 @ X21 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X10 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('11',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X19 @ X20 )
        = X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C_2 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(demod,[status(thm)],['22','23','24','27'])).

thf(t132_partfun1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( r1_partfun1 @ A @ B )
            <=> ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X17 ) @ ( k1_relat_1 @ X17 ) )
      | ( r1_partfun1 @ X17 @ X16 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_partfun1 @ X0 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_partfun1 @ X0 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['30','31','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_partfun1 @ sk_B @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
    | ( r1_partfun1 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['36','37','40'])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('43',plain,
    ( ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = ( k1_funct_1 @ sk_C_2 @ X21 ) ) )
   <= ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = ( k1_funct_1 @ sk_C_2 @ X21 ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X0 )
          = ( k1_funct_1 @ sk_C_2 @ X0 ) ) )
   <= ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = ( k1_funct_1 @ sk_C_2 @ X21 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( r1_partfun1 @ sk_B @ sk_C_2 )
      | ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_C_2 @ sk_B ) )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) ) ) )
   <= ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = ( k1_funct_1 @ sk_C_2 @ X21 ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k1_funct_1 @ X17 @ ( sk_C_1 @ X16 @ X17 ) )
       != ( k1_funct_1 @ X16 @ ( sk_C_1 @ X16 @ X17 ) ) )
      | ( r1_partfun1 @ X17 @ X16 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('47',plain,
    ( ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) )
       != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) ) )
      | ( r1_partfun1 @ sk_B @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( r1_partfun1 @ sk_B @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) )
   <= ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = ( k1_funct_1 @ sk_C_2 @ X21 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('49',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(demod,[status(thm)],['22','23','24','27'])).

thf('51',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['18'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('54',plain,
    ( ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) )
       != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_C_2 @ sk_B ) ) )
      | ( r1_partfun1 @ sk_B @ sk_C_2 )
      | ( r1_partfun1 @ sk_B @ sk_C_2 ) )
   <= ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = ( k1_funct_1 @ sk_C_2 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51','52','53'])).

thf('55',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C_2 )
   <= ! [X21: $i] :
        ( ~ ( r2_hidden @ X21 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X21 )
          = ( k1_funct_1 @ sk_C_2 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_2 @ sk_D ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ~ ( r1_partfun1 @ sk_B @ sk_C_2 )
   <= ~ ( r1_partfun1 @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,
    ( ~ ! [X21: $i] :
          ( ~ ( r2_hidden @ X21 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X21 )
            = ( k1_funct_1 @ sk_C_2 @ X21 ) ) )
    | ( r1_partfun1 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,(
    r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['7','58','59'])).

thf('61',plain,(
    r2_hidden @ sk_D @ ( k1_relat_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['5','60'])).

thf('62',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['18'])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(demod,[status(thm)],['22','23','24','27'])).

thf('64',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r1_partfun1 @ X17 @ X16 )
      | ( ( k1_funct_1 @ X17 @ X18 )
        = ( k1_funct_1 @ X16 @ X18 ) )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X17 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_C_2 @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_C_2 @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_B @ sk_C_2 )
      | ( ( k1_funct_1 @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_C_2 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C_2 )
   <= ( r1_partfun1 @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('71',plain,(
    r1_partfun1 @ sk_B @ sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['7','58'])).

thf('72',plain,(
    r1_partfun1 @ sk_B @ sk_C_2 ),
    inference(simpl_trail,[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_C_2 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['69','72','73','74'])).

thf('76',plain,
    ( ( k1_funct_1 @ sk_B @ sk_D )
    = ( k1_funct_1 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['61','75'])).

thf('77',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_2 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_2 @ sk_D ) ) ),
    inference(split,[status(esa)],['56'])).

thf('78',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C_2 @ sk_D ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['56'])).

thf('79',plain,(
    ( k1_funct_1 @ sk_B @ sk_D )
 != ( k1_funct_1 @ sk_C_2 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['7','58','78'])).

thf('80',plain,(
    ( k1_funct_1 @ sk_B @ sk_D )
 != ( k1_funct_1 @ sk_C_2 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['77','79'])).

thf('81',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AG3M7RR1Gh
% 0.13/0.33  % Computer   : n007.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:41:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 98 iterations in 0.025s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.20/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.48  thf(t146_funct_2, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_funct_1 @ B ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.48             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.48           ( ( r1_partfun1 @ B @ C ) <=>
% 0.20/0.48             ( ![D:$i]:
% 0.20/0.48               ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) ) =>
% 0.20/0.48                 ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( ( v1_funct_1 @ B ) & 
% 0.20/0.48            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.48          ( ![C:$i]:
% 0.20/0.48            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.48                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.48              ( ( r1_partfun1 @ B @ C ) <=>
% 0.20/0.48                ( ![D:$i]:
% 0.20/0.48                  ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) ) =>
% 0.20/0.48                    ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t146_funct_2])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.48        | ~ (r1_partfun1 @ sk_B @ sk_C_2))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B)))
% 0.20/0.48         <= (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.48         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.48  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (((r2_hidden @ sk_D @ (k1_relat_1 @ sk_B)))
% 0.20/0.48         <= (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['1', '4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X21 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X21 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.48          | ((k1_funct_1 @ sk_B @ X21) = (k1_funct_1 @ sk_C_2 @ X21))
% 0.20/0.48          | (r1_partfun1 @ sk_B @ sk_C_2))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (((r1_partfun1 @ sk_B @ sk_C_2)) | 
% 0.20/0.48       (![X21 : $i]:
% 0.20/0.48          (~ (r2_hidden @ X21 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.48           | ((k1_funct_1 @ sk_B @ X21) = (k1_funct_1 @ sk_C_2 @ X21))))),
% 0.20/0.48      inference('split', [status(esa)], ['6'])).
% 0.20/0.48  thf(d3_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]:
% 0.20/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k1_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (k1_relset_1 @ X10 @ X11 @ X12) @ (k1_zfmisc_1 @ X10))
% 0.20/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf(l3_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X4 @ X5)
% 0.20/0.48          | (r2_hidden @ X4 @ X6)
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ X0 @ sk_A)
% 0.20/0.48          | ~ (r2_hidden @ X0 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r1_tarski @ (k1_relat_1 @ sk_B) @ X0)
% 0.20/0.48          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_B)) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]:
% 0.20/0.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.20/0.48        | (r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.20/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t67_funct_2, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.48       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X19 : $i, X20 : $i]:
% 0.20/0.48         (((k1_relset_1 @ X19 @ X19 @ X20) = (X19))
% 0.20/0.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.20/0.48          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.20/0.48          | ~ (v1_funct_1 @ X20))),
% 0.20/0.48      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((~ (v1_funct_1 @ sk_C_2)
% 0.20/0.48        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_A)
% 0.20/0.48        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C_2) = (sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain, ((v1_funct_1 @ sk_C_2)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('24', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.48         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.20/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (((k1_relset_1 @ sk_A @ sk_A @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['22', '23', '24', '27'])).
% 0.20/0.48  thf(t132_partfun1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.48           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.48             ( ( r1_partfun1 @ A @ B ) <=>
% 0.20/0.48               ( ![C:$i]:
% 0.20/0.48                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.48                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X16)
% 0.20/0.48          | ~ (v1_funct_1 @ X16)
% 0.20/0.48          | (r2_hidden @ (sk_C_1 @ X16 @ X17) @ (k1_relat_1 @ X17))
% 0.20/0.48          | (r1_partfun1 @ X17 @ X16)
% 0.20/0.48          | ~ (r1_tarski @ (k1_relat_1 @ X17) @ (k1_relat_1 @ X16))
% 0.20/0.48          | ~ (v1_funct_1 @ X17)
% 0.20/0.48          | ~ (v1_relat_1 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [t132_partfun1])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_funct_1 @ X0)
% 0.20/0.48          | (r1_partfun1 @ X0 @ sk_C_2)
% 0.20/0.48          | (r2_hidden @ (sk_C_1 @ sk_C_2 @ X0) @ (k1_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_funct_1 @ sk_C_2)
% 0.20/0.48          | ~ (v1_relat_1 @ sk_C_2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain, ((v1_funct_1 @ sk_C_2)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc1_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( v1_relat_1 @ C ) ))).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         ((v1_relat_1 @ X7)
% 0.20/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.48  thf('34', plain, ((v1_relat_1 @ sk_C_2)),
% 0.20/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_funct_1 @ X0)
% 0.20/0.48          | (r1_partfun1 @ X0 @ sk_C_2)
% 0.20/0.48          | (r2_hidden @ (sk_C_1 @ sk_C_2 @ X0) @ (k1_relat_1 @ X0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['30', '31', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.20/0.48        | (r1_partfun1 @ sk_B @ sk_C_2)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '35'])).
% 0.20/0.48  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         ((v1_relat_1 @ X7)
% 0.20/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.49  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (((r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.20/0.49        | (r1_partfun1 @ sk_B @ sk_C_2))),
% 0.20/0.49      inference('demod', [status(thm)], ['36', '37', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      ((![X21 : $i]:
% 0.20/0.49          (~ (r2_hidden @ X21 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49           | ((k1_funct_1 @ sk_B @ X21) = (k1_funct_1 @ sk_C_2 @ X21))))
% 0.20/0.49         <= ((![X21 : $i]:
% 0.20/0.49                (~ (r2_hidden @ X21 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49                 | ((k1_funct_1 @ sk_B @ X21) = (k1_funct_1 @ sk_C_2 @ X21)))))),
% 0.20/0.49      inference('split', [status(esa)], ['6'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.20/0.49           | ((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C_2 @ X0))))
% 0.20/0.49         <= ((![X21 : $i]:
% 0.20/0.49                (~ (r2_hidden @ X21 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49                 | ((k1_funct_1 @ sk_B @ X21) = (k1_funct_1 @ sk_C_2 @ X21)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      ((((r1_partfun1 @ sk_B @ sk_C_2)
% 0.20/0.49         | ((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_C_2 @ sk_B))
% 0.20/0.49             = (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_B)))))
% 0.20/0.49         <= ((![X21 : $i]:
% 0.20/0.49                (~ (r2_hidden @ X21 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49                 | ((k1_funct_1 @ sk_B @ X21) = (k1_funct_1 @ sk_C_2 @ X21)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['41', '44'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X16)
% 0.20/0.49          | ~ (v1_funct_1 @ X16)
% 0.20/0.49          | ((k1_funct_1 @ X17 @ (sk_C_1 @ X16 @ X17))
% 0.20/0.49              != (k1_funct_1 @ X16 @ (sk_C_1 @ X16 @ X17)))
% 0.20/0.49          | (r1_partfun1 @ X17 @ X16)
% 0.20/0.49          | ~ (r1_tarski @ (k1_relat_1 @ X17) @ (k1_relat_1 @ X16))
% 0.20/0.49          | ~ (v1_funct_1 @ X17)
% 0.20/0.49          | ~ (v1_relat_1 @ X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [t132_partfun1])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_B))
% 0.20/0.49           != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_B)))
% 0.20/0.49         | (r1_partfun1 @ sk_B @ sk_C_2)
% 0.20/0.49         | ~ (v1_relat_1 @ sk_B)
% 0.20/0.49         | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49         | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_C_2))
% 0.20/0.49         | (r1_partfun1 @ sk_B @ sk_C_2)
% 0.20/0.49         | ~ (v1_funct_1 @ sk_C_2)
% 0.20/0.49         | ~ (v1_relat_1 @ sk_C_2)))
% 0.20/0.49         <= ((![X21 : $i]:
% 0.20/0.49                (~ (r2_hidden @ X21 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49                 | ((k1_funct_1 @ sk_B @ X21) = (k1_funct_1 @ sk_C_2 @ X21)))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('48', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('50', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['22', '23', '24', '27'])).
% 0.20/0.49  thf('51', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.20/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.49  thf('52', plain, ((v1_funct_1 @ sk_C_2)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('53', plain, ((v1_relat_1 @ sk_C_2)),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      (((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_B))
% 0.20/0.49           != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_C_2 @ sk_B)))
% 0.20/0.49         | (r1_partfun1 @ sk_B @ sk_C_2)
% 0.20/0.49         | (r1_partfun1 @ sk_B @ sk_C_2)))
% 0.20/0.49         <= ((![X21 : $i]:
% 0.20/0.49                (~ (r2_hidden @ X21 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49                 | ((k1_funct_1 @ sk_B @ X21) = (k1_funct_1 @ sk_C_2 @ X21)))))),
% 0.20/0.49      inference('demod', [status(thm)],
% 0.20/0.49                ['47', '48', '49', '50', '51', '52', '53'])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      (((r1_partfun1 @ sk_B @ sk_C_2))
% 0.20/0.49         <= ((![X21 : $i]:
% 0.20/0.49                (~ (r2_hidden @ X21 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49                 | ((k1_funct_1 @ sk_B @ X21) = (k1_funct_1 @ sk_C_2 @ X21)))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.49  thf('56', plain,
% 0.20/0.49      ((((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C_2 @ sk_D))
% 0.20/0.49        | ~ (r1_partfun1 @ sk_B @ sk_C_2))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      ((~ (r1_partfun1 @ sk_B @ sk_C_2)) <= (~ ((r1_partfun1 @ sk_B @ sk_C_2)))),
% 0.20/0.49      inference('split', [status(esa)], ['56'])).
% 0.20/0.49  thf('58', plain,
% 0.20/0.49      (~
% 0.20/0.49       (![X21 : $i]:
% 0.20/0.49          (~ (r2_hidden @ X21 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.49           | ((k1_funct_1 @ sk_B @ X21) = (k1_funct_1 @ sk_C_2 @ X21)))) | 
% 0.20/0.49       ((r1_partfun1 @ sk_B @ sk_C_2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['55', '57'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))) | 
% 0.20/0.49       ~ ((r1_partfun1 @ sk_B @ sk_C_2))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('60', plain, (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['7', '58', '59'])).
% 0.20/0.49  thf('61', plain, ((r2_hidden @ sk_D @ (k1_relat_1 @ sk_B))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['5', '60'])).
% 0.20/0.49  thf('62', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.20/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.49  thf('63', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['22', '23', '24', '27'])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X16)
% 0.20/0.49          | ~ (v1_funct_1 @ X16)
% 0.20/0.49          | ~ (r1_partfun1 @ X17 @ X16)
% 0.20/0.49          | ((k1_funct_1 @ X17 @ X18) = (k1_funct_1 @ X16 @ X18))
% 0.20/0.49          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ X17))
% 0.20/0.49          | ~ (r1_tarski @ (k1_relat_1 @ X17) @ (k1_relat_1 @ X16))
% 0.20/0.49          | ~ (v1_funct_1 @ X17)
% 0.20/0.49          | ~ (v1_relat_1 @ X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [t132_partfun1])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.20/0.49          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_C_2 @ X1))
% 0.20/0.49          | ~ (r1_partfun1 @ X0 @ sk_C_2)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_C_2)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_C_2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.49  thf('66', plain, ((v1_funct_1 @ sk_C_2)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('67', plain, ((v1_relat_1 @ sk_C_2)),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('68', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.20/0.49          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_C_2 @ X1))
% 0.20/0.49          | ~ (r1_partfun1 @ X0 @ sk_C_2))),
% 0.20/0.49      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.20/0.49  thf('69', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r1_partfun1 @ sk_B @ sk_C_2)
% 0.20/0.49          | ((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C_2 @ X0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.20/0.49          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['62', '68'])).
% 0.20/0.49  thf('70', plain,
% 0.20/0.49      (((r1_partfun1 @ sk_B @ sk_C_2)) <= (((r1_partfun1 @ sk_B @ sk_C_2)))),
% 0.20/0.49      inference('split', [status(esa)], ['6'])).
% 0.20/0.49  thf('71', plain, (((r1_partfun1 @ sk_B @ sk_C_2))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['7', '58'])).
% 0.20/0.49  thf('72', plain, ((r1_partfun1 @ sk_B @ sk_C_2)),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['70', '71'])).
% 0.20/0.49  thf('73', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('74', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('75', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C_2 @ X0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.20/0.49      inference('demod', [status(thm)], ['69', '72', '73', '74'])).
% 0.20/0.49  thf('76', plain,
% 0.20/0.49      (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_2 @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['61', '75'])).
% 0.20/0.49  thf('77', plain,
% 0.20/0.49      ((((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C_2 @ sk_D)))
% 0.20/0.49         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_2 @ sk_D))))),
% 0.20/0.49      inference('split', [status(esa)], ['56'])).
% 0.20/0.49  thf('78', plain,
% 0.20/0.49      (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_2 @ sk_D))) | 
% 0.20/0.49       ~ ((r1_partfun1 @ sk_B @ sk_C_2))),
% 0.20/0.49      inference('split', [status(esa)], ['56'])).
% 0.20/0.49  thf('79', plain,
% 0.20/0.49      (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C_2 @ sk_D)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['7', '58', '78'])).
% 0.20/0.49  thf('80', plain,
% 0.20/0.49      (((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C_2 @ sk_D))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['77', '79'])).
% 0.20/0.49  thf('81', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['76', '80'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
