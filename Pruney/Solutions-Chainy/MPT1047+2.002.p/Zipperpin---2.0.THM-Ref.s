%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bfstS4122r

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:21 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 799 expanded)
%              Number of leaves         :   38 ( 232 expanded)
%              Depth                    :   22
%              Number of atoms          : 1832 (15600 expanded)
%              Number of equality atoms :  124 ( 707 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t164_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C )
            = ( k1_tarski @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
           => ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C )
              = ( k1_tarski @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_2])).

thf('0',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 )
      | ( X11
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t158_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) )
         => ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X51 @ ( k5_partfun1 @ X52 @ X53 @ X54 ) )
      | ( v1_funct_1 @ X51 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 )
      | ( X11
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X51 @ ( k5_partfun1 @ X52 @ X53 @ X54 ) )
      | ( v1_funct_2 @ X51 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X12 @ X11 ) @ X11 )
      | ( X11
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ X51 @ ( k5_partfun1 @ X52 @ X53 @ X54 ) )
      | ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t66_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) )).

thf('23',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X56 @ ( k1_tarski @ X57 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ ( k1_tarski @ X57 ) ) ) )
      | ( r2_relset_1 @ X56 @ ( k1_tarski @ X57 ) @ X58 @ X55 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ ( k1_tarski @ X57 ) ) ) )
      | ~ ( v1_funct_2 @ X58 @ X56 @ ( k1_tarski @ X57 ) )
      | ~ ( v1_funct_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_D )
      | ~ ( v1_funct_2 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_D )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_D )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ sk_D )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('34',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( X25 = X28 )
      | ~ ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) @ X1 )
      | ( ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
        = sk_D )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
        = sk_D )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
        = sk_D )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( ( sk_C @ X12 @ X11 )
       != X12 )
      | ( X11
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( sk_D != X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
      = ( k1_tarski @ sk_D ) )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('45',plain,(
    k1_xboole_0
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['0','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t143_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( r1_partfun1 @ C @ D ) ) ) )).

thf('53',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( v1_funct_1 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ ( k1_tarski @ X49 ) ) ) )
      | ( r1_partfun1 @ X50 @ X47 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ ( k1_tarski @ X49 ) ) ) )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t143_partfun1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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

thf('61',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ( v1_partfun1 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('62',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X46 @ X44 )
      | ( v1_partfun1 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_partfun1 @ sk_D @ sk_A )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ C ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( ( v1_funct_1 @ F )
                  & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                  & ( F = E )
                  & ( v1_partfun1 @ F @ A )
                  & ( r1_partfun1 @ C @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B @ A )
    <=> ( ( r1_partfun1 @ C @ F )
        & ( v1_partfun1 @ F @ A )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F ) ) ) )).

thf('68',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 @ X29 @ X32 @ X34 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X32 ) ) )
      | ( X30 != X31 )
      | ~ ( v1_partfun1 @ X30 @ X34 )
      | ~ ( r1_partfun1 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('69',plain,(
    ! [X29: $i,X31: $i,X32: $i,X34: $i] :
      ( ~ ( r1_partfun1 @ X29 @ X31 )
      | ~ ( v1_partfun1 @ X31 @ X34 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( zip_tseitin_0 @ X31 @ X31 @ X29 @ X32 @ X34 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_D @ sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) )).

thf('76',plain,(
    ! [X36: $i,X37: $i,X38: $i,X40: $i,X42: $i,X43: $i] :
      ( ( X40
       != ( k5_partfun1 @ X38 @ X37 @ X36 ) )
      | ( r2_hidden @ X42 @ X40 )
      | ~ ( zip_tseitin_0 @ X43 @ X42 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('77',plain,(
    ! [X36: $i,X37: $i,X38: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( zip_tseitin_0 @ X43 @ X42 @ X36 @ X37 @ X38 )
      | ( r2_hidden @ X42 @ ( k5_partfun1 @ X38 @ X37 @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('83',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X18 @ X20 ) @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r2_hidden @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_D ) @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_tarski @ ( k2_tarski @ sk_D @ sk_D ) @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('86',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('87',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('90',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ ( k1_tarski @ sk_D ) )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('94',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('95',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['92','93','94'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('96',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('97',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('99',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('100',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['96'])).

thf('101',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['50','95','97','98','99','100'])).

thf('102',plain,(
    k1_xboole_0
 != ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','101'])).

thf('103',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['92','93','94'])).

thf(t130_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf('104',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( k1_tarski @ X17 ) @ X16 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t130_zfmisc_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('107',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['105','107'])).

thf('109',plain,(
    ! [X0: $i] : ( X0 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['102','109'])).

thf('111',plain,(
    $false ),
    inference(simplify,[status(thm)],['110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bfstS4122r
% 0.13/0.36  % Computer   : n019.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 14:40:52 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 1.21/1.41  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.21/1.41  % Solved by: fo/fo7.sh
% 1.21/1.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.21/1.41  % done 1808 iterations in 0.946s
% 1.21/1.41  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.21/1.41  % SZS output start Refutation
% 1.21/1.41  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 1.21/1.41  thf(sk_B_type, type, sk_B: $i).
% 1.21/1.41  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.21/1.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.21/1.41  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 1.21/1.41  thf(sk_D_type, type, sk_D: $i).
% 1.21/1.41  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.21/1.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.21/1.41  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.21/1.41  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.21/1.41  thf(sk_A_type, type, sk_A: $i).
% 1.21/1.41  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 1.21/1.41  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.21/1.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.21/1.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.21/1.41  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.21/1.41  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.21/1.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.21/1.41  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.21/1.41  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.21/1.41  thf(t164_funct_2, conjecture,
% 1.21/1.41    (![A:$i,B:$i,C:$i]:
% 1.21/1.41     ( ( ( v1_funct_1 @ C ) & 
% 1.21/1.41         ( m1_subset_1 @
% 1.21/1.41           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 1.21/1.41       ( ![D:$i]:
% 1.21/1.41         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 1.21/1.41             ( m1_subset_1 @
% 1.21/1.41               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 1.21/1.41           ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C ) = ( k1_tarski @ D ) ) ) ) ))).
% 1.21/1.41  thf(zf_stmt_0, negated_conjecture,
% 1.21/1.41    (~( ![A:$i,B:$i,C:$i]:
% 1.21/1.41        ( ( ( v1_funct_1 @ C ) & 
% 1.21/1.41            ( m1_subset_1 @
% 1.21/1.41              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 1.21/1.41          ( ![D:$i]:
% 1.21/1.41            ( ( ( v1_funct_1 @ D ) & 
% 1.21/1.41                ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 1.21/1.41                ( m1_subset_1 @
% 1.21/1.41                  D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 1.21/1.41              ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C ) = ( k1_tarski @ D ) ) ) ) ) )),
% 1.21/1.41    inference('cnf.neg', [status(esa)], [t164_funct_2])).
% 1.21/1.41  thf('0', plain,
% 1.21/1.41      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41         != (k1_tarski @ sk_D))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf(l44_zfmisc_1, axiom,
% 1.21/1.41    (![A:$i,B:$i]:
% 1.21/1.41     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.21/1.41          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 1.21/1.41  thf('1', plain,
% 1.21/1.41      (![X11 : $i, X12 : $i]:
% 1.21/1.41         (((X11) = (k1_xboole_0))
% 1.21/1.41          | (r2_hidden @ (sk_C @ X12 @ X11) @ X11)
% 1.21/1.41          | ((X11) = (k1_tarski @ X12)))),
% 1.21/1.41      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 1.21/1.41  thf('2', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_C_1 @ 
% 1.21/1.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf(t158_funct_2, axiom,
% 1.21/1.41    (![A:$i,B:$i,C:$i]:
% 1.21/1.41     ( ( ( v1_funct_1 @ C ) & 
% 1.21/1.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.21/1.41       ( ![D:$i]:
% 1.21/1.41         ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) =>
% 1.21/1.41           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.21/1.41             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ))).
% 1.21/1.41  thf('3', plain,
% 1.21/1.41      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.21/1.41         (~ (r2_hidden @ X51 @ (k5_partfun1 @ X52 @ X53 @ X54))
% 1.21/1.41          | (v1_funct_1 @ X51)
% 1.21/1.41          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 1.21/1.41          | ~ (v1_funct_1 @ X54))),
% 1.21/1.41      inference('cnf', [status(esa)], [t158_funct_2])).
% 1.21/1.41  thf('4', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (v1_funct_1 @ sk_C_1)
% 1.21/1.41          | (v1_funct_1 @ X0)
% 1.21/1.41          | ~ (r2_hidden @ X0 @ 
% 1.21/1.41               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['2', '3'])).
% 1.21/1.41  thf('5', plain, ((v1_funct_1 @ sk_C_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('6', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((v1_funct_1 @ X0)
% 1.21/1.41          | ~ (r2_hidden @ X0 @ 
% 1.21/1.41               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 1.21/1.41      inference('demod', [status(thm)], ['4', '5'])).
% 1.21/1.41  thf('7', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41            = (k1_tarski @ X0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 1.21/1.41          | (v1_funct_1 @ 
% 1.21/1.41             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 1.21/1.41      inference('sup-', [status(thm)], ['1', '6'])).
% 1.21/1.41  thf('8', plain,
% 1.21/1.41      (![X11 : $i, X12 : $i]:
% 1.21/1.41         (((X11) = (k1_xboole_0))
% 1.21/1.41          | (r2_hidden @ (sk_C @ X12 @ X11) @ X11)
% 1.21/1.41          | ((X11) = (k1_tarski @ X12)))),
% 1.21/1.41      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 1.21/1.41  thf('9', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_C_1 @ 
% 1.21/1.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('10', plain,
% 1.21/1.41      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.21/1.41         (~ (r2_hidden @ X51 @ (k5_partfun1 @ X52 @ X53 @ X54))
% 1.21/1.41          | (v1_funct_2 @ X51 @ X52 @ X53)
% 1.21/1.41          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 1.21/1.41          | ~ (v1_funct_1 @ X54))),
% 1.21/1.41      inference('cnf', [status(esa)], [t158_funct_2])).
% 1.21/1.41  thf('11', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (v1_funct_1 @ sk_C_1)
% 1.21/1.41          | (v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 1.21/1.41          | ~ (r2_hidden @ X0 @ 
% 1.21/1.41               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['9', '10'])).
% 1.21/1.41  thf('12', plain, ((v1_funct_1 @ sk_C_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('13', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 1.21/1.41          | ~ (r2_hidden @ X0 @ 
% 1.21/1.41               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 1.21/1.41      inference('demod', [status(thm)], ['11', '12'])).
% 1.21/1.41  thf('14', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41            = (k1_tarski @ X0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 1.21/1.41          | (v1_funct_2 @ 
% 1.21/1.41             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 1.21/1.41             sk_A @ (k1_tarski @ sk_B)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['8', '13'])).
% 1.21/1.41  thf('15', plain,
% 1.21/1.41      (![X11 : $i, X12 : $i]:
% 1.21/1.41         (((X11) = (k1_xboole_0))
% 1.21/1.41          | (r2_hidden @ (sk_C @ X12 @ X11) @ X11)
% 1.21/1.41          | ((X11) = (k1_tarski @ X12)))),
% 1.21/1.41      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 1.21/1.41  thf('16', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_C_1 @ 
% 1.21/1.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('17', plain,
% 1.21/1.41      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 1.21/1.41         (~ (r2_hidden @ X51 @ (k5_partfun1 @ X52 @ X53 @ X54))
% 1.21/1.41          | (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 1.21/1.41          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 1.21/1.41          | ~ (v1_funct_1 @ X54))),
% 1.21/1.41      inference('cnf', [status(esa)], [t158_funct_2])).
% 1.21/1.41  thf('18', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (v1_funct_1 @ sk_C_1)
% 1.21/1.41          | (m1_subset_1 @ X0 @ 
% 1.21/1.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 1.21/1.41          | ~ (r2_hidden @ X0 @ 
% 1.21/1.41               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['16', '17'])).
% 1.21/1.41  thf('19', plain, ((v1_funct_1 @ sk_C_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('20', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((m1_subset_1 @ X0 @ 
% 1.21/1.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 1.21/1.41          | ~ (r2_hidden @ X0 @ 
% 1.21/1.41               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 1.21/1.41      inference('demod', [status(thm)], ['18', '19'])).
% 1.21/1.41  thf('21', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41            = (k1_tarski @ X0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 1.21/1.41          | (m1_subset_1 @ 
% 1.21/1.41             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 1.21/1.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 1.21/1.41      inference('sup-', [status(thm)], ['15', '20'])).
% 1.21/1.41  thf('22', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_D @ 
% 1.21/1.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf(t66_funct_2, axiom,
% 1.21/1.41    (![A:$i,B:$i,C:$i]:
% 1.21/1.41     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) ) & 
% 1.21/1.41         ( m1_subset_1 @
% 1.21/1.41           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 1.21/1.41       ( ![D:$i]:
% 1.21/1.41         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 1.21/1.41             ( m1_subset_1 @
% 1.21/1.41               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 1.21/1.41           ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) ))).
% 1.21/1.41  thf('23', plain,
% 1.21/1.41      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 1.21/1.41         (~ (v1_funct_1 @ X55)
% 1.21/1.41          | ~ (v1_funct_2 @ X55 @ X56 @ (k1_tarski @ X57))
% 1.21/1.41          | ~ (m1_subset_1 @ X55 @ 
% 1.21/1.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ (k1_tarski @ X57))))
% 1.21/1.41          | (r2_relset_1 @ X56 @ (k1_tarski @ X57) @ X58 @ X55)
% 1.21/1.41          | ~ (m1_subset_1 @ X58 @ 
% 1.21/1.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ (k1_tarski @ X57))))
% 1.21/1.41          | ~ (v1_funct_2 @ X58 @ X56 @ (k1_tarski @ X57))
% 1.21/1.41          | ~ (v1_funct_1 @ X58))),
% 1.21/1.41      inference('cnf', [status(esa)], [t66_funct_2])).
% 1.21/1.41  thf('24', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (v1_funct_1 @ X0)
% 1.21/1.41          | ~ (v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 1.21/1.41          | ~ (m1_subset_1 @ X0 @ 
% 1.21/1.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 1.21/1.41          | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ X0 @ sk_D)
% 1.21/1.41          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 1.21/1.41          | ~ (v1_funct_1 @ sk_D))),
% 1.21/1.41      inference('sup-', [status(thm)], ['22', '23'])).
% 1.21/1.41  thf('25', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('27', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (v1_funct_1 @ X0)
% 1.21/1.41          | ~ (v1_funct_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 1.21/1.41          | ~ (m1_subset_1 @ X0 @ 
% 1.21/1.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 1.21/1.41          | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ X0 @ sk_D))),
% 1.21/1.41      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.21/1.41  thf('28', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41              = (k1_tarski @ X0))
% 1.21/1.41          | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ 
% 1.21/1.41             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 1.21/1.41             sk_D)
% 1.21/1.41          | ~ (v1_funct_2 @ 
% 1.21/1.41               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 1.21/1.41               sk_A @ (k1_tarski @ sk_B))
% 1.21/1.41          | ~ (v1_funct_1 @ 
% 1.21/1.41               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))))),
% 1.21/1.41      inference('sup-', [status(thm)], ['21', '27'])).
% 1.21/1.41  thf('29', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41              = (k1_tarski @ X0))
% 1.21/1.41          | ~ (v1_funct_1 @ 
% 1.21/1.41               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 1.21/1.41          | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ 
% 1.21/1.41             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 1.21/1.41             sk_D)
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41              = (k1_tarski @ X0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['14', '28'])).
% 1.21/1.41  thf('30', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ 
% 1.21/1.41           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 1.21/1.41           sk_D)
% 1.21/1.41          | ~ (v1_funct_1 @ 
% 1.21/1.41               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41              = (k1_tarski @ X0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 1.21/1.41      inference('simplify', [status(thm)], ['29'])).
% 1.21/1.41  thf('31', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41              = (k1_tarski @ X0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41              = (k1_tarski @ X0))
% 1.21/1.41          | (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ 
% 1.21/1.41             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 1.21/1.41             sk_D))),
% 1.21/1.41      inference('sup-', [status(thm)], ['7', '30'])).
% 1.21/1.41  thf('32', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ 
% 1.21/1.41           (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 1.21/1.41           sk_D)
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41              = (k1_tarski @ X0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 1.21/1.41      inference('simplify', [status(thm)], ['31'])).
% 1.21/1.41  thf('33', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41            = (k1_tarski @ X0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 1.21/1.41          | (m1_subset_1 @ 
% 1.21/1.41             (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 1.21/1.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 1.21/1.41      inference('sup-', [status(thm)], ['15', '20'])).
% 1.21/1.41  thf(redefinition_r2_relset_1, axiom,
% 1.21/1.41    (![A:$i,B:$i,C:$i,D:$i]:
% 1.21/1.41     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.21/1.41         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.21/1.41       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.21/1.41  thf('34', plain,
% 1.21/1.41      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.21/1.41         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.21/1.41          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.21/1.41          | ((X25) = (X28))
% 1.21/1.41          | ~ (r2_relset_1 @ X26 @ X27 @ X25 @ X28))),
% 1.21/1.41      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.21/1.41  thf('35', plain,
% 1.21/1.41      (![X0 : $i, X1 : $i]:
% 1.21/1.41         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41              = (k1_tarski @ X0))
% 1.21/1.41          | ~ (r2_relset_1 @ sk_A @ (k1_tarski @ sk_B) @ 
% 1.21/1.41               (sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)) @ 
% 1.21/1.41               X1)
% 1.21/1.41          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 1.21/1.41              = (X1))
% 1.21/1.41          | ~ (m1_subset_1 @ X1 @ 
% 1.21/1.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))))),
% 1.21/1.41      inference('sup-', [status(thm)], ['33', '34'])).
% 1.21/1.41  thf('36', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41              = (k1_tarski @ X0))
% 1.21/1.41          | ~ (m1_subset_1 @ sk_D @ 
% 1.21/1.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 1.21/1.41          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 1.21/1.41              = (sk_D))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41              = (k1_tarski @ X0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['32', '35'])).
% 1.21/1.41  thf('37', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_D @ 
% 1.21/1.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('38', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41              = (k1_tarski @ X0))
% 1.21/1.41          | ((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 1.21/1.41              = (sk_D))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41              = (k1_tarski @ X0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 1.21/1.41      inference('demod', [status(thm)], ['36', '37'])).
% 1.21/1.41  thf('39', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (((sk_C @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 1.21/1.41            = (sk_D))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41              = (k1_tarski @ X0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 1.21/1.41      inference('simplify', [status(thm)], ['38'])).
% 1.21/1.41  thf('40', plain,
% 1.21/1.41      (![X11 : $i, X12 : $i]:
% 1.21/1.41         (((X11) = (k1_xboole_0))
% 1.21/1.41          | ((sk_C @ X12 @ X11) != (X12))
% 1.21/1.41          | ((X11) = (k1_tarski @ X12)))),
% 1.21/1.41      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 1.21/1.41  thf('41', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (((sk_D) != (X0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41              = (k1_tarski @ X0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41              = (k1_tarski @ X0))
% 1.21/1.41          | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['39', '40'])).
% 1.21/1.41  thf('42', plain,
% 1.21/1.41      ((((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41          = (k1_tarski @ sk_D))
% 1.21/1.41        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 1.21/1.41      inference('simplify', [status(thm)], ['41'])).
% 1.21/1.41  thf('43', plain,
% 1.21/1.41      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.41         != (k1_tarski @ sk_D))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('44', plain,
% 1.21/1.41      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 1.21/1.41      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 1.21/1.41  thf('45', plain, (((k1_xboole_0) != (k1_tarski @ sk_D))),
% 1.21/1.41      inference('demod', [status(thm)], ['0', '44'])).
% 1.21/1.41  thf('46', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_D @ 
% 1.21/1.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf(t3_subset, axiom,
% 1.21/1.41    (![A:$i,B:$i]:
% 1.21/1.41     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.21/1.41  thf('47', plain,
% 1.21/1.41      (![X22 : $i, X23 : $i]:
% 1.21/1.41         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 1.21/1.41      inference('cnf', [status(esa)], [t3_subset])).
% 1.21/1.41  thf('48', plain,
% 1.21/1.41      ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['46', '47'])).
% 1.21/1.41  thf(d10_xboole_0, axiom,
% 1.21/1.41    (![A:$i,B:$i]:
% 1.21/1.41     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.21/1.41  thf('49', plain,
% 1.21/1.41      (![X0 : $i, X2 : $i]:
% 1.21/1.41         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.21/1.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.21/1.41  thf('50', plain,
% 1.21/1.41      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) @ sk_D)
% 1.21/1.41        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (sk_D)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['48', '49'])).
% 1.21/1.41  thf('51', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_C_1 @ 
% 1.21/1.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('52', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_D @ 
% 1.21/1.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf(t143_partfun1, axiom,
% 1.21/1.41    (![A:$i,B:$i,C:$i]:
% 1.21/1.41     ( ( ( v1_funct_1 @ C ) & 
% 1.21/1.41         ( m1_subset_1 @
% 1.21/1.41           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 1.21/1.41       ( ![D:$i]:
% 1.21/1.41         ( ( ( v1_funct_1 @ D ) & 
% 1.21/1.41             ( m1_subset_1 @
% 1.21/1.41               D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 1.21/1.41           ( r1_partfun1 @ C @ D ) ) ) ))).
% 1.21/1.41  thf('53', plain,
% 1.21/1.41      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 1.21/1.41         (~ (v1_funct_1 @ X47)
% 1.21/1.41          | ~ (m1_subset_1 @ X47 @ 
% 1.21/1.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ (k1_tarski @ X49))))
% 1.21/1.41          | (r1_partfun1 @ X50 @ X47)
% 1.21/1.41          | ~ (m1_subset_1 @ X50 @ 
% 1.21/1.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ (k1_tarski @ X49))))
% 1.21/1.41          | ~ (v1_funct_1 @ X50))),
% 1.21/1.41      inference('cnf', [status(esa)], [t143_partfun1])).
% 1.21/1.41  thf('54', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (v1_funct_1 @ X0)
% 1.21/1.41          | ~ (m1_subset_1 @ X0 @ 
% 1.21/1.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 1.21/1.41          | (r1_partfun1 @ X0 @ sk_D)
% 1.21/1.41          | ~ (v1_funct_1 @ sk_D))),
% 1.21/1.41      inference('sup-', [status(thm)], ['52', '53'])).
% 1.21/1.41  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('56', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         (~ (v1_funct_1 @ X0)
% 1.21/1.41          | ~ (m1_subset_1 @ X0 @ 
% 1.21/1.41               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))
% 1.21/1.41          | (r1_partfun1 @ X0 @ sk_D))),
% 1.21/1.41      inference('demod', [status(thm)], ['54', '55'])).
% 1.21/1.41  thf('57', plain, (((r1_partfun1 @ sk_C_1 @ sk_D) | ~ (v1_funct_1 @ sk_C_1))),
% 1.21/1.41      inference('sup-', [status(thm)], ['51', '56'])).
% 1.21/1.41  thf('58', plain, ((v1_funct_1 @ sk_C_1)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('59', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 1.21/1.41      inference('demod', [status(thm)], ['57', '58'])).
% 1.21/1.41  thf('60', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_D @ 
% 1.21/1.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf(t132_funct_2, axiom,
% 1.21/1.41    (![A:$i,B:$i,C:$i]:
% 1.21/1.41     ( ( ( v1_funct_1 @ C ) & 
% 1.21/1.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.21/1.41       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.21/1.41           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.21/1.41         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.21/1.41           ( v1_partfun1 @ C @ A ) ) ) ))).
% 1.21/1.41  thf('61', plain,
% 1.21/1.41      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.21/1.41         (((X44) = (k1_xboole_0))
% 1.21/1.41          | ~ (v1_funct_1 @ X45)
% 1.21/1.41          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 1.21/1.41          | (v1_partfun1 @ X45 @ X46)
% 1.21/1.41          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 1.21/1.41          | ~ (v1_funct_2 @ X45 @ X46 @ X44)
% 1.21/1.41          | ~ (v1_funct_1 @ X45))),
% 1.21/1.41      inference('cnf', [status(esa)], [t132_funct_2])).
% 1.21/1.41  thf('62', plain,
% 1.21/1.41      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.21/1.41         (~ (v1_funct_2 @ X45 @ X46 @ X44)
% 1.21/1.41          | (v1_partfun1 @ X45 @ X46)
% 1.21/1.41          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X44)))
% 1.21/1.41          | ~ (v1_funct_1 @ X45)
% 1.21/1.41          | ((X44) = (k1_xboole_0)))),
% 1.21/1.41      inference('simplify', [status(thm)], ['61'])).
% 1.21/1.41  thf('63', plain,
% 1.21/1.41      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 1.21/1.41        | ~ (v1_funct_1 @ sk_D)
% 1.21/1.41        | (v1_partfun1 @ sk_D @ sk_A)
% 1.21/1.41        | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B)))),
% 1.21/1.41      inference('sup-', [status(thm)], ['60', '62'])).
% 1.21/1.41  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('65', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('66', plain,
% 1.21/1.41      ((((k1_tarski @ sk_B) = (k1_xboole_0)) | (v1_partfun1 @ sk_D @ sk_A))),
% 1.21/1.41      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.21/1.41  thf('67', plain,
% 1.21/1.41      ((m1_subset_1 @ sk_D @ 
% 1.21/1.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf(d7_partfun1, axiom,
% 1.21/1.41    (![A:$i,B:$i,C:$i]:
% 1.21/1.41     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.21/1.41         ( v1_funct_1 @ C ) ) =>
% 1.21/1.41       ( ![D:$i]:
% 1.21/1.41         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 1.21/1.41           ( ![E:$i]:
% 1.21/1.41             ( ( r2_hidden @ E @ D ) <=>
% 1.21/1.41               ( ?[F:$i]:
% 1.21/1.41                 ( ( v1_funct_1 @ F ) & 
% 1.21/1.41                   ( m1_subset_1 @
% 1.21/1.41                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.21/1.41                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 1.21/1.41                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 1.21/1.41  thf(zf_stmt_1, axiom,
% 1.21/1.41    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 1.21/1.41     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 1.21/1.41       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 1.21/1.41         ( ( F ) = ( E ) ) & 
% 1.21/1.41         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.21/1.41         ( v1_funct_1 @ F ) ) ))).
% 1.21/1.41  thf('68', plain,
% 1.21/1.41      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X34 : $i]:
% 1.21/1.41         ((zip_tseitin_0 @ X30 @ X31 @ X29 @ X32 @ X34)
% 1.21/1.41          | ~ (v1_funct_1 @ X30)
% 1.21/1.41          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X32)))
% 1.21/1.41          | ((X30) != (X31))
% 1.21/1.41          | ~ (v1_partfun1 @ X30 @ X34)
% 1.21/1.41          | ~ (r1_partfun1 @ X29 @ X30))),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.21/1.41  thf('69', plain,
% 1.21/1.41      (![X29 : $i, X31 : $i, X32 : $i, X34 : $i]:
% 1.21/1.41         (~ (r1_partfun1 @ X29 @ X31)
% 1.21/1.41          | ~ (v1_partfun1 @ X31 @ X34)
% 1.21/1.41          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X32)))
% 1.21/1.41          | ~ (v1_funct_1 @ X31)
% 1.21/1.41          | (zip_tseitin_0 @ X31 @ X31 @ X29 @ X32 @ X34))),
% 1.21/1.41      inference('simplify', [status(thm)], ['68'])).
% 1.21/1.41  thf('70', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ (k1_tarski @ sk_B) @ sk_A)
% 1.21/1.41          | ~ (v1_funct_1 @ sk_D)
% 1.21/1.41          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 1.21/1.41          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 1.21/1.41      inference('sup-', [status(thm)], ['67', '69'])).
% 1.21/1.41  thf('71', plain, ((v1_funct_1 @ sk_D)),
% 1.21/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.41  thf('72', plain,
% 1.21/1.41      (![X0 : $i]:
% 1.21/1.41         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ (k1_tarski @ sk_B) @ sk_A)
% 1.21/1.41          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 1.21/1.41          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 1.21/1.41      inference('demod', [status(thm)], ['70', '71'])).
% 1.21/1.42  thf('73', plain,
% 1.21/1.42      (![X0 : $i]:
% 1.21/1.42         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 1.21/1.42          | ~ (r1_partfun1 @ X0 @ sk_D)
% 1.21/1.42          | (zip_tseitin_0 @ sk_D @ sk_D @ X0 @ (k1_tarski @ sk_B) @ sk_A))),
% 1.21/1.42      inference('sup-', [status(thm)], ['66', '72'])).
% 1.21/1.42  thf('74', plain,
% 1.21/1.42      (((zip_tseitin_0 @ sk_D @ sk_D @ sk_C_1 @ (k1_tarski @ sk_B) @ sk_A)
% 1.21/1.42        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 1.21/1.42      inference('sup-', [status(thm)], ['59', '73'])).
% 1.21/1.42  thf('75', plain,
% 1.21/1.42      ((m1_subset_1 @ sk_C_1 @ 
% 1.21/1.42        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 1.21/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.42  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 1.21/1.42  thf(zf_stmt_3, axiom,
% 1.21/1.42    (![A:$i,B:$i,C:$i]:
% 1.21/1.42     ( ( ( v1_funct_1 @ C ) & 
% 1.21/1.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.21/1.42       ( ![D:$i]:
% 1.21/1.42         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 1.21/1.42           ( ![E:$i]:
% 1.21/1.42             ( ( r2_hidden @ E @ D ) <=>
% 1.21/1.42               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 1.21/1.42  thf('76', plain,
% 1.21/1.42      (![X36 : $i, X37 : $i, X38 : $i, X40 : $i, X42 : $i, X43 : $i]:
% 1.21/1.42         (((X40) != (k5_partfun1 @ X38 @ X37 @ X36))
% 1.21/1.42          | (r2_hidden @ X42 @ X40)
% 1.21/1.42          | ~ (zip_tseitin_0 @ X43 @ X42 @ X36 @ X37 @ X38)
% 1.21/1.42          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 1.21/1.42          | ~ (v1_funct_1 @ X36))),
% 1.21/1.42      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.21/1.42  thf('77', plain,
% 1.21/1.42      (![X36 : $i, X37 : $i, X38 : $i, X42 : $i, X43 : $i]:
% 1.21/1.42         (~ (v1_funct_1 @ X36)
% 1.21/1.42          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 1.21/1.42          | ~ (zip_tseitin_0 @ X43 @ X42 @ X36 @ X37 @ X38)
% 1.21/1.42          | (r2_hidden @ X42 @ (k5_partfun1 @ X38 @ X37 @ X36)))),
% 1.21/1.42      inference('simplify', [status(thm)], ['76'])).
% 1.21/1.42  thf('78', plain,
% 1.21/1.42      (![X0 : $i, X1 : $i]:
% 1.21/1.42         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 1.21/1.42          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ (k1_tarski @ sk_B) @ sk_A)
% 1.21/1.42          | ~ (v1_funct_1 @ sk_C_1))),
% 1.21/1.42      inference('sup-', [status(thm)], ['75', '77'])).
% 1.21/1.42  thf('79', plain, ((v1_funct_1 @ sk_C_1)),
% 1.21/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.42  thf('80', plain,
% 1.21/1.42      (![X0 : $i, X1 : $i]:
% 1.21/1.42         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 1.21/1.42          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 1.21/1.42      inference('demod', [status(thm)], ['78', '79'])).
% 1.21/1.42  thf('81', plain,
% 1.21/1.42      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 1.21/1.42        | (r2_hidden @ sk_D @ 
% 1.21/1.42           (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 1.21/1.42      inference('sup-', [status(thm)], ['74', '80'])).
% 1.21/1.42  thf('82', plain,
% 1.21/1.42      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 1.21/1.42        | (r2_hidden @ sk_D @ 
% 1.21/1.42           (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 1.21/1.42      inference('sup-', [status(thm)], ['74', '80'])).
% 1.21/1.42  thf(t38_zfmisc_1, axiom,
% 1.21/1.42    (![A:$i,B:$i,C:$i]:
% 1.21/1.42     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.21/1.42       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.21/1.42  thf('83', plain,
% 1.21/1.42      (![X18 : $i, X20 : $i, X21 : $i]:
% 1.21/1.42         ((r1_tarski @ (k2_tarski @ X18 @ X20) @ X21)
% 1.21/1.42          | ~ (r2_hidden @ X20 @ X21)
% 1.21/1.42          | ~ (r2_hidden @ X18 @ X21))),
% 1.21/1.42      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.21/1.42  thf('84', plain,
% 1.21/1.42      (![X0 : $i]:
% 1.21/1.42         (((k1_tarski @ sk_B) = (k1_xboole_0))
% 1.21/1.42          | ~ (r2_hidden @ X0 @ 
% 1.21/1.42               (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 1.21/1.42          | (r1_tarski @ (k2_tarski @ X0 @ sk_D) @ 
% 1.21/1.42             (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)))),
% 1.21/1.42      inference('sup-', [status(thm)], ['82', '83'])).
% 1.21/1.42  thf('85', plain,
% 1.21/1.42      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 1.21/1.42        | (r1_tarski @ (k2_tarski @ sk_D @ sk_D) @ 
% 1.21/1.42           (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 1.21/1.42        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 1.21/1.42      inference('sup-', [status(thm)], ['81', '84'])).
% 1.21/1.42  thf(t69_enumset1, axiom,
% 1.21/1.42    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.21/1.42  thf('86', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 1.21/1.42      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.21/1.42  thf('87', plain,
% 1.21/1.42      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 1.21/1.42        | (r1_tarski @ (k1_tarski @ sk_D) @ 
% 1.21/1.42           (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 1.21/1.42        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 1.21/1.42      inference('demod', [status(thm)], ['85', '86'])).
% 1.21/1.42  thf('88', plain,
% 1.21/1.42      (((r1_tarski @ (k1_tarski @ sk_D) @ 
% 1.21/1.42         (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1))
% 1.21/1.42        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 1.21/1.42      inference('simplify', [status(thm)], ['87'])).
% 1.21/1.42  thf('89', plain,
% 1.21/1.42      (![X0 : $i, X2 : $i]:
% 1.21/1.42         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.21/1.42      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.21/1.42  thf('90', plain,
% 1.21/1.42      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 1.21/1.42        | ~ (r1_tarski @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) @ 
% 1.21/1.42             (k1_tarski @ sk_D))
% 1.21/1.42        | ((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.42            = (k1_tarski @ sk_D)))),
% 1.21/1.42      inference('sup-', [status(thm)], ['88', '89'])).
% 1.21/1.42  thf('91', plain,
% 1.21/1.42      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1)
% 1.21/1.42         != (k1_tarski @ sk_D))),
% 1.21/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.21/1.42  thf('92', plain,
% 1.21/1.42      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 1.21/1.42        | ~ (r1_tarski @ (k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) @ 
% 1.21/1.42             (k1_tarski @ sk_D)))),
% 1.21/1.42      inference('simplify_reflect-', [status(thm)], ['90', '91'])).
% 1.21/1.42  thf('93', plain,
% 1.21/1.42      (((k5_partfun1 @ sk_A @ (k1_tarski @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 1.21/1.42      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 1.21/1.42  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.21/1.42  thf('94', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.21/1.42      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.21/1.42  thf('95', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 1.21/1.42      inference('demod', [status(thm)], ['92', '93', '94'])).
% 1.21/1.42  thf(t113_zfmisc_1, axiom,
% 1.21/1.42    (![A:$i,B:$i]:
% 1.21/1.42     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.21/1.42       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.21/1.42  thf('96', plain,
% 1.21/1.42      (![X14 : $i, X15 : $i]:
% 1.21/1.42         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 1.21/1.42          | ((X15) != (k1_xboole_0)))),
% 1.21/1.42      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.21/1.42  thf('97', plain,
% 1.21/1.42      (![X14 : $i]: ((k2_zfmisc_1 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.42      inference('simplify', [status(thm)], ['96'])).
% 1.21/1.42  thf('98', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.21/1.42      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.21/1.42  thf('99', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 1.21/1.42      inference('demod', [status(thm)], ['92', '93', '94'])).
% 1.21/1.42  thf('100', plain,
% 1.21/1.42      (![X14 : $i]: ((k2_zfmisc_1 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 1.21/1.42      inference('simplify', [status(thm)], ['96'])).
% 1.21/1.42  thf('101', plain, (((k1_xboole_0) = (sk_D))),
% 1.21/1.42      inference('demod', [status(thm)], ['50', '95', '97', '98', '99', '100'])).
% 1.21/1.42  thf('102', plain, (((k1_xboole_0) != (k1_tarski @ k1_xboole_0))),
% 1.21/1.42      inference('demod', [status(thm)], ['45', '101'])).
% 1.21/1.42  thf('103', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 1.21/1.42      inference('demod', [status(thm)], ['92', '93', '94'])).
% 1.21/1.42  thf(t130_zfmisc_1, axiom,
% 1.21/1.42    (![A:$i,B:$i]:
% 1.21/1.42     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 1.21/1.42       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 1.21/1.42         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 1.21/1.42  thf('104', plain,
% 1.21/1.42      (![X16 : $i, X17 : $i]:
% 1.21/1.42         (((X16) = (k1_xboole_0))
% 1.21/1.42          | ((k2_zfmisc_1 @ (k1_tarski @ X17) @ X16) != (k1_xboole_0)))),
% 1.21/1.42      inference('cnf', [status(esa)], [t130_zfmisc_1])).
% 1.21/1.42  thf('105', plain,
% 1.21/1.42      (![X0 : $i]:
% 1.21/1.42         (((k2_zfmisc_1 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 1.21/1.42          | ((X0) = (k1_xboole_0)))),
% 1.21/1.42      inference('sup-', [status(thm)], ['103', '104'])).
% 1.21/1.42  thf('106', plain,
% 1.21/1.42      (![X14 : $i, X15 : $i]:
% 1.21/1.42         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 1.21/1.42          | ((X14) != (k1_xboole_0)))),
% 1.21/1.42      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.21/1.42  thf('107', plain,
% 1.21/1.42      (![X15 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 1.21/1.42      inference('simplify', [status(thm)], ['106'])).
% 1.21/1.42  thf('108', plain,
% 1.21/1.42      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 1.21/1.42      inference('demod', [status(thm)], ['105', '107'])).
% 1.21/1.42  thf('109', plain, (![X0 : $i]: ((X0) = (k1_xboole_0))),
% 1.21/1.42      inference('simplify', [status(thm)], ['108'])).
% 1.21/1.42  thf('110', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.21/1.42      inference('demod', [status(thm)], ['102', '109'])).
% 1.21/1.42  thf('111', plain, ($false), inference('simplify', [status(thm)], ['110'])).
% 1.21/1.42  
% 1.21/1.42  % SZS output end Refutation
% 1.21/1.42  
% 1.21/1.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
