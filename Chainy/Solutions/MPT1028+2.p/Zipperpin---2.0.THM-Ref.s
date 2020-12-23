%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1028+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qK71AIJ7lo

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:05 EST 2020

% Result     : Theorem 54.54s
% Output     : Refutation 54.54s
% Verified   : 
% Statistics : Number of formulae       :   30 (  49 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  175 ( 579 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_99_type,type,(
    sk_B_99: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_110_type,type,(
    sk_C_110: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_16_type,type,(
    sk_A_16: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t131_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) )
     => ( ( v1_partfun1 @ ( C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ ( C @ ( A @ B ) ) )
          & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) )
       => ( ( v1_partfun1 @ ( C @ A ) )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ ( C @ ( A @ B ) ) )
            & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t131_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_C_110 )
    | ~ ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) )
    | ~ ( m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) )
   <= ~ ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_C_110 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_C_110 )
   <= ~ ( v1_funct_1 @ sk_C_110 ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_C_110 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) )
    | ~ ( m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) )
    | ~ ( v1_funct_1 @ sk_C_110 ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,(
    ~ ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['4','7','8'])).

thf('10',plain,(
    ~ ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','9'])).

thf('11',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_16 @ sk_B_99 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ ( C @ A ) ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ ( C @ ( A @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X4632: $i,X4633: $i,X4634: $i] :
      ( ~ ( v1_funct_1 @ X4632 )
      | ~ ( v1_partfun1 @ ( X4632 @ X4633 ) )
      | ( v1_funct_2 @ ( X4632 @ ( X4633 @ X4634 ) ) )
      | ~ ( m1_subset_1 @ ( X4632 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X4633 @ X4634 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('13',plain,
    ( ( v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) )
    | ~ ( v1_partfun1 @ ( sk_C_110 @ sk_A_16 ) )
    | ~ ( v1_funct_1 @ sk_C_110 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_partfun1 @ ( sk_C_110 @ sk_A_16 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_C_110 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ ( sk_C_110 @ ( sk_A_16 @ sk_B_99 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['10','16'])).

%------------------------------------------------------------------------------
