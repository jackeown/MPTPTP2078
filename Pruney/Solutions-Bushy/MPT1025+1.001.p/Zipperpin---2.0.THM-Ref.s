%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1025+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cwKeBtfPTv

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  74 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :  406 (1186 expanded)
%              Number of equality atoms :   10 (  36 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t115_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ~ ( ( r2_hidden @ F @ A )
                  & ( r2_hidden @ F @ C )
                  & ( E
                    = ( k1_funct_1 @ D @ F ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X1 @ X2 @ X3 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ X3 @ X4 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X1 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t115_funct_2])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    r2_hidden @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X7: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D @ X7 ) )
      | ~ ( r2_hidden @ X7 @ sk_C )
      | ~ ( m1_subset_1 @ X7 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X1 @ X2 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ X3 @ X4 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X1 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t115_funct_2])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    r2_hidden @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['10','16'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('19',plain,(
    m1_subset_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0
        = ( k1_funct_1 @ X1 @ ( sk_F @ X0 @ X1 @ X2 @ X3 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ X3 @ X4 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X1 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t115_funct_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( X1
        = ( k1_funct_1 @ sk_D @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( X1
        = ( k1_funct_1 @ sk_D @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['9','19','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).


%------------------------------------------------------------------------------
