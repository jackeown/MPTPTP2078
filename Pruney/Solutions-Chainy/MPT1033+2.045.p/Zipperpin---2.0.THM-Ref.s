%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iiEX2448kI

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 297 expanded)
%              Number of leaves         :   17 (  84 expanded)
%              Depth                    :   18
%              Number of atoms          :  842 (6150 expanded)
%              Number of equality atoms :   70 ( 410 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ( v1_partfun1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X5 @ X6 @ X4 )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('3',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_2 @ X5 @ X6 @ X4 )
      | ( v1_partfun1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_funct_2 @ X5 @ X6 @ X4 )
      | ( v1_partfun1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_partfun1 @ sk_D @ sk_A )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( X10 = X7 )
      | ~ ( r1_partfun1 @ X10 @ X7 )
      | ~ ( v1_partfun1 @ X7 @ X8 )
      | ~ ( v1_partfun1 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('24',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( X10 = X7 )
      | ~ ( r1_partfun1 @ X10 @ X7 )
      | ~ ( v1_partfun1 @ X7 @ X8 )
      | ~ ( v1_partfun1 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( v1_partfun1 @ X0 @ k1_xboole_0 )
        | ~ ( v1_partfun1 @ sk_D @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ X0 @ sk_D )
        | ( X0 = sk_D )
        | ~ ( v1_funct_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('35',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X6 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ( v1_partfun1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X5 @ X6 @ X4 )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_funct_2 @ X5 @ k1_xboole_0 @ X4 )
      | ( v1_partfun1 @ X5 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ~ ( v1_funct_1 @ sk_D )
      | ( v1_partfun1 @ sk_D @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('40',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_partfun1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( v1_partfun1 @ X0 @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ X0 @ sk_D )
        | ( X0 = sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','42','43'])).

thf('45',plain,
    ( ( ( sk_C = sk_D )
      | ~ ( r1_partfun1 @ sk_C @ sk_D )
      | ~ ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','44'])).

thf('46',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_funct_2 @ X5 @ k1_xboole_0 @ X4 )
      | ( v1_partfun1 @ X5 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('49',plain,
    ( ( ~ ( v1_funct_1 @ sk_C )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( sk_C = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46','54','55'])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( r2_relset_1 @ X1 @ X2 @ X0 @ X3 )
      | ( X0 != X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('59',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X1 @ X2 @ X3 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['25','56','60'])).

thf('62',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('63',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['22','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','64'])).

thf('66',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['8','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ( sk_C = sk_D ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = sk_D ) ),
    inference('sup-',[status(thm)],['7','69'])).

thf('71',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['22','63'])).

thf('72',plain,(
    sk_C = sk_D ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X1 @ X2 @ X3 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('75',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['0','72','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iiEX2448kI
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:24:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 72 iterations in 0.030s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(t142_funct_2, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49       ( ![D:$i]:
% 0.21/0.49         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.49             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49           ( ( r1_partfun1 @ C @ D ) =>
% 0.21/0.49             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.21/0.49               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49          ( ![D:$i]:
% 0.21/0.49            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.49                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49              ( ( r1_partfun1 @ C @ D ) =>
% 0.21/0.49                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.21/0.49                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.21/0.49  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t132_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.21/0.49           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (((X4) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_funct_1 @ X5)
% 0.21/0.49          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.21/0.49          | (v1_partfun1 @ X5 @ X6)
% 0.21/0.49          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.21/0.49          | ~ (v1_funct_2 @ X5 @ X6 @ X4)
% 0.21/0.49          | ~ (v1_funct_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (v1_funct_2 @ X5 @ X6 @ X4)
% 0.21/0.49          | (v1_partfun1 @ X5 @ X6)
% 0.21/0.49          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.21/0.49          | ~ (v1_funct_1 @ X5)
% 0.21/0.49          | ((X4) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      ((((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.49        | (v1_partfun1 @ sk_C @ sk_A)
% 0.21/0.49        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '3'])).
% 0.21/0.49  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain, ((((sk_B) = (k1_xboole_0)) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (v1_funct_2 @ X5 @ X6 @ X4)
% 0.21/0.49          | (v1_partfun1 @ X5 @ X6)
% 0.21/0.49          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.21/0.49          | ~ (v1_funct_1 @ X5)
% 0.21/0.49          | ((X4) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ~ (v1_funct_1 @ sk_D)
% 0.21/0.49        | (v1_partfun1 @ sk_D @ sk_A)
% 0.21/0.49        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('13', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain, ((((sk_B) = (k1_xboole_0)) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t148_partfun1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49       ( ![D:$i]:
% 0.21/0.49         ( ( ( v1_funct_1 @ D ) & 
% 0.21/0.49             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.21/0.49               ( r1_partfun1 @ C @ D ) ) =>
% 0.21/0.49             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ X7)
% 0.21/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.21/0.49          | ((X10) = (X7))
% 0.21/0.49          | ~ (r1_partfun1 @ X10 @ X7)
% 0.21/0.49          | ~ (v1_partfun1 @ X7 @ X8)
% 0.21/0.49          | ~ (v1_partfun1 @ X10 @ X8)
% 0.21/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.21/0.49          | ~ (v1_funct_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.21/0.49          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.49          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.21/0.49          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.21/0.49          | ((X0) = (sk_D))
% 0.21/0.49          | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.21/0.49          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.49          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.21/0.49          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.21/0.49          | ((X0) = (sk_D)))),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_B) = (k1_xboole_0))
% 0.21/0.49          | ((X0) = (sk_D))
% 0.21/0.49          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.21/0.49          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.21/0.49          | ~ (v1_funct_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '19'])).
% 0.21/0.49  thf('21', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.21/0.49      inference('split', [status(esa)], ['21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('split', [status(esa)], ['21'])).
% 0.21/0.49  thf('24', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D))
% 0.21/0.49         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('split', [status(esa)], ['21'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (((m1_subset_1 @ sk_C @ 
% 0.21/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.21/0.49         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('split', [status(esa)], ['21'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((m1_subset_1 @ sk_D @ 
% 0.21/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.21/0.49         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ X7)
% 0.21/0.49          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.21/0.49          | ((X10) = (X7))
% 0.21/0.49          | ~ (r1_partfun1 @ X10 @ X7)
% 0.21/0.49          | ~ (v1_partfun1 @ X7 @ X8)
% 0.21/0.49          | ~ (v1_partfun1 @ X10 @ X8)
% 0.21/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.21/0.49          | ~ (v1_funct_1 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (~ (v1_funct_1 @ X0)
% 0.21/0.49           | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.49                (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B)))
% 0.21/0.49           | ~ (v1_partfun1 @ X0 @ k1_xboole_0)
% 0.21/0.49           | ~ (v1_partfun1 @ sk_D @ k1_xboole_0)
% 0.21/0.49           | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.21/0.49           | ((X0) = (sk_D))
% 0.21/0.49           | ~ (v1_funct_1 @ sk_D)))
% 0.21/0.49         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (((m1_subset_1 @ sk_D @ 
% 0.21/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.21/0.49         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (((X6) != (k1_xboole_0))
% 0.21/0.49          | ~ (v1_funct_1 @ X5)
% 0.21/0.49          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.21/0.49          | (v1_partfun1 @ X5 @ X6)
% 0.21/0.49          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X4)))
% 0.21/0.49          | ~ (v1_funct_2 @ X5 @ X6 @ X4)
% 0.21/0.49          | ~ (v1_funct_1 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (v1_funct_2 @ X5 @ k1_xboole_0 @ X4)
% 0.21/0.49          | (v1_partfun1 @ X5 @ k1_xboole_0)
% 0.21/0.49          | ~ (m1_subset_1 @ X5 @ 
% 0.21/0.49               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X4)))
% 0.21/0.49          | ~ (v1_funct_1 @ X5))),
% 0.21/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (((~ (v1_funct_1 @ sk_D)
% 0.21/0.49         | (v1_partfun1 @ sk_D @ k1_xboole_0)
% 0.21/0.49         | ~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B)))
% 0.21/0.49         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '36'])).
% 0.21/0.49  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('split', [status(esa)], ['21'])).
% 0.21/0.49  thf('40', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.21/0.49         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (((v1_partfun1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['37', '38', '41'])).
% 0.21/0.49  thf('43', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (~ (v1_funct_1 @ X0)
% 0.21/0.49           | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.49                (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B)))
% 0.21/0.49           | ~ (v1_partfun1 @ X0 @ k1_xboole_0)
% 0.21/0.49           | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.21/0.49           | ((X0) = (sk_D))))
% 0.21/0.49         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['33', '42', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (((((sk_C) = (sk_D))
% 0.21/0.49         | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.21/0.49         | ~ (v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.21/0.49         | ~ (v1_funct_1 @ sk_C))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '44'])).
% 0.21/0.49  thf('46', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (((m1_subset_1 @ sk_C @ 
% 0.21/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.21/0.49         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (v1_funct_2 @ X5 @ k1_xboole_0 @ X4)
% 0.21/0.49          | (v1_partfun1 @ X5 @ k1_xboole_0)
% 0.21/0.49          | ~ (m1_subset_1 @ X5 @ 
% 0.21/0.49               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X4)))
% 0.21/0.49          | ~ (v1_funct_1 @ X5))),
% 0.21/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (((~ (v1_funct_1 @ sk_C)
% 0.21/0.49         | (v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.21/0.49         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B)))
% 0.21/0.49         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('split', [status(esa)], ['21'])).
% 0.21/0.49  thf('52', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ sk_B))
% 0.21/0.49         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['51', '52'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (((v1_partfun1 @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['49', '50', '53'])).
% 0.21/0.49  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('56', plain, ((((sk_C) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['45', '46', '54', '55'])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (((m1_subset_1 @ sk_C @ 
% 0.21/0.49         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.21/0.49         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf(redefinition_r2_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.21/0.49          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.21/0.49          | (r2_relset_1 @ X1 @ X2 @ X0 @ X3)
% 0.21/0.49          | ((X0) != (X3)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((r2_relset_1 @ X1 @ X2 @ X3 @ X3)
% 0.21/0.49          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['58'])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (((r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C @ sk_C))
% 0.21/0.49         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['57', '59'])).
% 0.21/0.49  thf('61', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '56', '60'])).
% 0.21/0.49  thf('62', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('split', [status(esa)], ['21'])).
% 0.21/0.49  thf('63', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['61', '62'])).
% 0.21/0.49  thf('64', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['22', '63'])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((X0) = (sk_D))
% 0.21/0.49          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.21/0.49          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.21/0.49          | ~ (v1_funct_1 @ X0))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['20', '64'])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      ((~ (v1_funct_1 @ sk_C)
% 0.21/0.49        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.21/0.49        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.21/0.49        | ((sk_C) = (sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '65'])).
% 0.21/0.49  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('68', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('69', plain, ((~ (v1_partfun1 @ sk_C @ sk_A) | ((sk_C) = (sk_D)))),
% 0.21/0.49      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.21/0.49  thf('70', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '69'])).
% 0.21/0.49  thf('71', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['22', '63'])).
% 0.21/0.49  thf('72', plain, (((sk_C) = (sk_D))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.49         ((r2_relset_1 @ X1 @ X2 @ X3 @ X3)
% 0.21/0.49          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['58'])).
% 0.21/0.49  thf('75', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.21/0.49      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.49  thf('76', plain, ($false),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '72', '75'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
