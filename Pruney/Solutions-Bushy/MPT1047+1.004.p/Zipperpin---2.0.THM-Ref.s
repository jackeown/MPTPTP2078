%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1047+1.004 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dlxQisZY3Q

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:58 EST 2020

% Result     : Theorem 25.04s
% Output     : Refutation 25.04s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 282 expanded)
%              Number of leaves         :   34 (  92 expanded)
%              Depth                    :   20
%              Number of atoms          : 1644 (5295 expanded)
%              Number of equality atoms :   77 ( 225 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X7: $i] :
      ( ( X7
        = ( k1_tarski @ X3 ) )
      | ( ( sk_C @ X7 @ X3 )
        = X3 )
      | ( r2_hidden @ ( sk_C @ X7 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

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

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k5_partfun1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( v1_funct_1 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X3: $i,X7: $i] :
      ( ( X7
        = ( k1_tarski @ X3 ) )
      | ( ( sk_C @ X7 @ X3 )
        = X3 )
      | ( r2_hidden @ ( sk_C @ X7 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k5_partfun1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( v1_funct_2 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 ) @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X3: $i,X7: $i] :
      ( ( X7
        = ( k1_tarski @ X3 ) )
      | ( ( sk_C @ X7 @ X3 )
        = X3 )
      | ( r2_hidden @ ( sk_C @ X7 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k5_partfun1 @ X33 @ X34 @ X35 ) )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( m1_subset_1 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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

thf('22',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ ( k1_tarski @ X43 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ ( k1_tarski @ X43 ) ) ) )
      | ( r2_relset_1 @ X42 @ ( k1_tarski @ X43 ) @ X44 @ X41 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ ( k1_tarski @ X43 ) ) ) )
      | ~ ( v1_funct_2 @ X44 @ X42 @ ( k1_tarski @ X43 ) )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 ) @ sk_D )
      | ~ ( v1_funct_2 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 ) @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ~ ( v1_funct_1 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 ) )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 ) @ sk_D )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 ) @ sk_D )
      | ~ ( v1_funct_1 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 ) @ sk_D )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( m1_subset_1 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ~ ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 ) @ X1 )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = sk_D )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = sk_D )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = sk_D )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_D )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ X0 )
        = sk_D ) ) ),
    inference(eq_fact,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ sk_D )
      = sk_D )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
      = ( k1_tarski @ sk_D ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ sk_D )
    = sk_D ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i,X7: $i] :
      ( ( X7
        = ( k1_tarski @ X3 ) )
      | ( ( sk_C @ X7 @ X3 )
       != X3 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) )
    | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ sk_D )
     != sk_D )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t143_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( r1_partfun1 @ C @ D ) ) ) )).

thf('47',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ ( k1_tarski @ X30 ) ) ) )
      | ( r1_partfun1 @ X31 @ X28 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ ( k1_tarski @ X30 ) ) ) )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t143_partfun1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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

thf('55',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X8 @ X11 @ X13 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ( X9 != X10 )
      | ~ ( v1_partfun1 @ X9 @ X13 )
      | ~ ( r1_partfun1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,(
    ! [X8: $i,X10: $i,X11: $i,X13: $i] :
      ( ~ ( r1_partfun1 @ X8 @ X10 )
      | ~ ( v1_partfun1 @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ( zip_tseitin_0 @ X10 @ X10 @ X8 @ X11 @ X13 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( v1_partfun1 @ X0 @ X1 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('66',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('67',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( sk_B @ X23 ) @ X23 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('68',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r2_hidden @ X36 @ X37 )
      | ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( sk_B @ X23 ) @ X23 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('71',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ~ ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('74',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( v1_xboole_0 @ X45 )
      | ~ ( v1_xboole_0 @ X46 )
      | ( X45 = X46 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_B @ ( k1_zfmisc_1 @ X0 ) )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','79'])).

thf('81',plain,(
    v1_partfun1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['64','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['57','58','81'])).

thf('83',plain,(
    zip_tseitin_0 @ sk_D @ sk_D @ sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['53','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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

thf('85',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i,X21: $i,X22: $i] :
      ( ( X19
       != ( k5_partfun1 @ X17 @ X16 @ X15 ) )
      | ( r2_hidden @ X21 @ X19 )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('86',plain,(
    ! [X15: $i,X16: $i,X17: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X21 @ ( k5_partfun1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['83','89'])).

thf('91',plain,
    ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 ) @ sk_D )
    = sk_D ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('92',plain,
    ( ( sk_D != sk_D )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
      = ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['44','90','91'])).

thf('93',plain,
    ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
    = ( k1_tarski @ sk_D ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).


%------------------------------------------------------------------------------
