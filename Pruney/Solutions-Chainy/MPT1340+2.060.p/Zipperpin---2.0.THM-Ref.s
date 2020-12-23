%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2x64xYy2FI

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:16 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  289 (3935 expanded)
%              Number of leaves         :   44 (1165 expanded)
%              Depth                    :   48
%              Number of atoms          : 2905 (82254 expanded)
%              Number of equality atoms :  175 (2725 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t64_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_tops_2])).

thf('2',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','21','24'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('26',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('27',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('34',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('39',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('40',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','37','38','39'])).

thf('41',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('50',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X33 @ X35 )
       != X33 )
      | ~ ( v2_funct_1 @ X35 )
      | ( ( k2_tops_2 @ X34 @ X33 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['63','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52','61','62','71'])).

thf('73',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['40','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t31_funct_2,axiom,(
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

thf('76',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('77',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('80',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('81',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X33 @ X35 )
       != X33 )
      | ~ ( v2_funct_1 @ X35 )
      | ( ( k2_tops_2 @ X34 @ X33 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('85',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('87',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('88',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('91',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('92',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('96',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X28 ) @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('97',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('100',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('101',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101'])).

thf('103',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['102'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('104',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('105',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('106',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('107',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('108',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('109',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('110',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('112',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('122',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('123',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('124',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('125',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('127',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('128',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('129',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( ( k5_relat_1 @ X12 @ X11 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['127','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['126','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['125','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['124','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['123','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['122','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['121','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('148',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['146','147','148','149'])).

thf('151',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['120','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['151','152','153','154'])).

thf('156',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('157',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['151','152','153','154'])).

thf('158',plain,
    ( ( ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('160',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('161',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['158','163','164','165','166'])).

thf('168',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['155','167'])).

thf('169',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( ( k5_relat_1 @ X12 @ X11 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X11 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('170',plain,
    ( ( ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['158','163','164','165','166'])).

thf('172',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('173',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('174',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('175',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['151','152','153','154'])).

thf('176',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('177',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('179',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('180',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('182',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('183',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['177','178','179','180','181','182'])).

thf('184',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['174','183'])).

thf('185',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('186',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['173','187'])).

thf('189',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('190',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['188','189','190','191','192'])).

thf('194',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('196',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('198',plain,
    ( ( ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) )
     != ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['170','171','172','194','195','196','197'])).

thf('199',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['198'])).

thf('200',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['105','199'])).

thf('201',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['200','201','202'])).

thf('204',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['104','203'])).

thf('205',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('206',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('207',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['204','205','206','207','208'])).

thf('210',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['193'])).

thf('212',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','94','103','210','211'])).

thf('213',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('214',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('215',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('217',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('218',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('219',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('221',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('222',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['193'])).

thf('223',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['219','220','221','222'])).

thf('224',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['216','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('226',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['224','225','226'])).

thf('228',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['215','227'])).

thf('229',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['212','228'])).

thf('230',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['74','230'])).

thf('232',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('233',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('234',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_funct_2 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('235',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['235','236','237'])).

thf('239',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['232','238'])).

thf('240',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('242',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['239','240','241'])).

thf('243',plain,(
    $false ),
    inference(demod,[status(thm)],['231','242'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2x64xYy2FI
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:58:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 401 iterations in 0.168s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.62  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.38/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.38/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.62  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.38/0.62  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.38/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.38/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.62  thf(d3_struct_0, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      (![X31 : $i]:
% 0.38/0.62         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (![X31 : $i]:
% 0.38/0.62         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.62  thf(t64_tops_2, conjecture,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( l1_struct_0 @ A ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.38/0.62           ( ![C:$i]:
% 0.38/0.62             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.62                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.62                 ( m1_subset_1 @
% 0.38/0.62                   C @ 
% 0.38/0.62                   ( k1_zfmisc_1 @
% 0.38/0.62                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.62               ( ( ( ( k2_relset_1 @
% 0.38/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.38/0.62                     ( k2_struct_0 @ B ) ) & 
% 0.38/0.62                   ( v2_funct_1 @ C ) ) =>
% 0.38/0.62                 ( r2_funct_2 @
% 0.38/0.62                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.38/0.62                   ( k2_tops_2 @
% 0.38/0.62                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.38/0.62                     ( k2_tops_2 @
% 0.38/0.62                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.38/0.62                   C ) ) ) ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i]:
% 0.38/0.62        ( ( l1_struct_0 @ A ) =>
% 0.38/0.62          ( ![B:$i]:
% 0.38/0.62            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.38/0.62              ( ![C:$i]:
% 0.38/0.62                ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.62                    ( v1_funct_2 @
% 0.38/0.62                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.62                    ( m1_subset_1 @
% 0.38/0.62                      C @ 
% 0.38/0.62                      ( k1_zfmisc_1 @
% 0.38/0.62                        ( k2_zfmisc_1 @
% 0.38/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.62                  ( ( ( ( k2_relset_1 @
% 0.38/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.38/0.62                        ( k2_struct_0 @ B ) ) & 
% 0.38/0.62                      ( v2_funct_1 @ C ) ) =>
% 0.38/0.62                    ( r2_funct_2 @
% 0.38/0.62                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.38/0.62                      ( k2_tops_2 @
% 0.38/0.62                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.38/0.62                        ( k2_tops_2 @
% 0.38/0.62                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.38/0.62                      C ) ) ) ) ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.38/0.62          sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.38/0.62           sk_C)
% 0.38/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.62  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.38/0.62          sk_C)),
% 0.38/0.62      inference('demod', [status(thm)], ['3', '4'])).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.38/0.62           sk_C)
% 0.38/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['0', '5'])).
% 0.38/0.62  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.62           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.38/0.62          sk_C)),
% 0.38/0.62      inference('demod', [status(thm)], ['6', '7'])).
% 0.38/0.62  thf('9', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ 
% 0.38/0.62        (k1_zfmisc_1 @ 
% 0.38/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(cc5_funct_2, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.38/0.62       ( ![C:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.38/0.62             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.38/0.62          | (v1_partfun1 @ X19 @ X20)
% 0.38/0.62          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.38/0.62          | ~ (v1_funct_1 @ X19)
% 0.38/0.62          | (v1_xboole_0 @ X21))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.62        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.62        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.62  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('14', plain,
% 0.38/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.62        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.38/0.62  thf(d4_partfun1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.38/0.62       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.38/0.62  thf('15', plain,
% 0.38/0.62      (![X22 : $i, X23 : $i]:
% 0.38/0.62         (~ (v1_partfun1 @ X23 @ X22)
% 0.38/0.62          | ((k1_relat_1 @ X23) = (X22))
% 0.38/0.62          | ~ (v4_relat_1 @ X23 @ X22)
% 0.38/0.62          | ~ (v1_relat_1 @ X23))),
% 0.38/0.62      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.62        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.38/0.62        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ 
% 0.38/0.62        (k1_zfmisc_1 @ 
% 0.38/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(cc2_relat_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ A ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.62  thf('18', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.38/0.62          | (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      ((~ (v1_relat_1 @ 
% 0.38/0.62           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.38/0.62        | (v1_relat_1 @ sk_C))),
% 0.38/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.62  thf(fc6_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.62  thf('20', plain,
% 0.38/0.62      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.62  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.62      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ 
% 0.38/0.62        (k1_zfmisc_1 @ 
% 0.38/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(cc2_relset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.62         ((v4_relat_1 @ X13 @ X14)
% 0.38/0.62          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.38/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.62  thf('24', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.62        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['16', '21', '24'])).
% 0.38/0.62  thf(fc2_struct_0, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.62       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      (![X32 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 0.38/0.62          | ~ (l1_struct_0 @ X32)
% 0.38/0.62          | (v2_struct_0 @ X32))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.62  thf('27', plain,
% 0.38/0.62      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.38/0.62        | (v2_struct_0 @ sk_B)
% 0.38/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.62  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.62  thf('30', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('31', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['29', '30'])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      (![X31 : $i]:
% 0.38/0.62         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.62  thf('33', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('clc', [status(thm)], ['29', '30'])).
% 0.38/0.62  thf('34', plain,
% 0.38/0.62      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup+', [status(thm)], ['32', '33'])).
% 0.38/0.62  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('36', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.62  thf('37', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['31', '36'])).
% 0.38/0.62  thf('38', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['31', '36'])).
% 0.38/0.62  thf('39', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['31', '36'])).
% 0.38/0.62  thf('40', plain,
% 0.38/0.62      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.62           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.38/0.62          sk_C)),
% 0.38/0.62      inference('demod', [status(thm)], ['8', '37', '38', '39'])).
% 0.38/0.62  thf('41', plain,
% 0.38/0.62      (![X31 : $i]:
% 0.38/0.62         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.62  thf('42', plain,
% 0.38/0.62      (![X31 : $i]:
% 0.38/0.62         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.62  thf('43', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ 
% 0.38/0.62        (k1_zfmisc_1 @ 
% 0.38/0.62         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('44', plain,
% 0.38/0.62      (((m1_subset_1 @ sk_C @ 
% 0.38/0.62         (k1_zfmisc_1 @ 
% 0.38/0.62          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.38/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup+', [status(thm)], ['42', '43'])).
% 0.38/0.62  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('46', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ 
% 0.38/0.62        (k1_zfmisc_1 @ 
% 0.38/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.38/0.62  thf('47', plain,
% 0.38/0.62      (((m1_subset_1 @ sk_C @ 
% 0.38/0.62         (k1_zfmisc_1 @ 
% 0.38/0.62          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.38/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.62      inference('sup+', [status(thm)], ['41', '46'])).
% 0.38/0.62  thf('48', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('49', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ 
% 0.38/0.62        (k1_zfmisc_1 @ 
% 0.38/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.38/0.62      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.62  thf(d4_tops_2, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.62       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.38/0.62         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.38/0.62  thf('50', plain,
% 0.38/0.62      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.62         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.38/0.62          | ~ (v2_funct_1 @ X35)
% 0.38/0.62          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.38/0.62          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.38/0.62          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.38/0.62          | ~ (v1_funct_1 @ X35))),
% 0.38/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.38/0.62  thf('51', plain,
% 0.38/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.62        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.38/0.62        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.62            = (k2_funct_1 @ sk_C))
% 0.38/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.62        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.62            != (k2_struct_0 @ sk_B)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.62  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('53', plain,
% 0.38/0.62      (![X31 : $i]:
% 0.38/0.62         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.62  thf('54', plain,
% 0.38/0.62      (![X31 : $i]:
% 0.38/0.62         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.62  thf('55', plain,
% 0.38/0.62      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('56', plain,
% 0.38/0.62      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup+', [status(thm)], ['54', '55'])).
% 0.38/0.62  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('58', plain,
% 0.38/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['56', '57'])).
% 0.38/0.62  thf('59', plain,
% 0.38/0.62      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.38/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.62      inference('sup+', [status(thm)], ['53', '58'])).
% 0.38/0.62  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('61', plain,
% 0.38/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['59', '60'])).
% 0.38/0.62  thf('62', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('63', plain,
% 0.38/0.62      (![X31 : $i]:
% 0.38/0.62         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.62  thf('64', plain,
% 0.38/0.62      (![X31 : $i]:
% 0.38/0.62         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.38/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.62  thf('65', plain,
% 0.38/0.62      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.62         = (k2_struct_0 @ sk_B))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('66', plain,
% 0.38/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.62          = (k2_struct_0 @ sk_B))
% 0.38/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.62      inference('sup+', [status(thm)], ['64', '65'])).
% 0.38/0.62  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('68', plain,
% 0.38/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.62         = (k2_struct_0 @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['66', '67'])).
% 0.38/0.62  thf('69', plain,
% 0.38/0.62      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.62          = (k2_struct_0 @ sk_B))
% 0.38/0.62        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.62      inference('sup+', [status(thm)], ['63', '68'])).
% 0.38/0.62  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('71', plain,
% 0.38/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.62         = (k2_struct_0 @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['69', '70'])).
% 0.38/0.62  thf('72', plain,
% 0.38/0.62      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.62          = (k2_funct_1 @ sk_C))
% 0.38/0.62        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.38/0.62      inference('demod', [status(thm)], ['51', '52', '61', '62', '71'])).
% 0.38/0.62  thf('73', plain,
% 0.38/0.62      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.62         = (k2_funct_1 @ sk_C))),
% 0.38/0.62      inference('simplify', [status(thm)], ['72'])).
% 0.38/0.62  thf('74', plain,
% 0.38/0.62      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.62          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.62           (k2_funct_1 @ sk_C)) @ 
% 0.38/0.62          sk_C)),
% 0.38/0.62      inference('demod', [status(thm)], ['40', '73'])).
% 0.38/0.62  thf('75', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ 
% 0.38/0.62        (k1_zfmisc_1 @ 
% 0.38/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.38/0.62      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.62  thf(t31_funct_2, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.62       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.38/0.62         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.38/0.62           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.38/0.62           ( m1_subset_1 @
% 0.38/0.62             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.38/0.62  thf('76', plain,
% 0.38/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.62         (~ (v2_funct_1 @ X28)
% 0.38/0.62          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.38/0.62          | (m1_subset_1 @ (k2_funct_1 @ X28) @ 
% 0.38/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.38/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.38/0.62          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.38/0.62          | ~ (v1_funct_1 @ X28))),
% 0.38/0.62      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.38/0.62  thf('77', plain,
% 0.38/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.62        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.38/0.62        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.62           (k1_zfmisc_1 @ 
% 0.38/0.62            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.38/0.62        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.62            != (k2_struct_0 @ sk_B))
% 0.38/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.62      inference('sup-', [status(thm)], ['75', '76'])).
% 0.38/0.62  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('79', plain,
% 0.38/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['59', '60'])).
% 0.38/0.62  thf('80', plain,
% 0.38/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.62         = (k2_struct_0 @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['69', '70'])).
% 0.38/0.62  thf('81', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('82', plain,
% 0.38/0.62      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.62         (k1_zfmisc_1 @ 
% 0.38/0.62          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.38/0.62        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.38/0.62      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 0.38/0.62  thf('83', plain,
% 0.38/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.62        (k1_zfmisc_1 @ 
% 0.38/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.38/0.62      inference('simplify', [status(thm)], ['82'])).
% 0.38/0.62  thf('84', plain,
% 0.38/0.62      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.62         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.38/0.62          | ~ (v2_funct_1 @ X35)
% 0.38/0.62          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.38/0.62          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.38/0.62          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.38/0.62          | ~ (v1_funct_1 @ X35))),
% 0.38/0.62      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.38/0.62  thf('85', plain,
% 0.38/0.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.62        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.38/0.62             (k2_struct_0 @ sk_A))
% 0.38/0.62        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.62            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.38/0.62        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.62        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.62            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['83', '84'])).
% 0.38/0.62  thf('86', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ 
% 0.38/0.62        (k1_zfmisc_1 @ 
% 0.38/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.38/0.62      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.62  thf('87', plain,
% 0.38/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.62         (~ (v2_funct_1 @ X28)
% 0.38/0.62          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.38/0.62          | (v1_funct_1 @ (k2_funct_1 @ X28))
% 0.38/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.38/0.62          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.38/0.62          | ~ (v1_funct_1 @ X28))),
% 0.38/0.62      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.38/0.62  thf('88', plain,
% 0.38/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.62        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.38/0.62        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.62        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.62            != (k2_struct_0 @ sk_B))
% 0.38/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.62      inference('sup-', [status(thm)], ['86', '87'])).
% 0.38/0.62  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('90', plain,
% 0.38/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['59', '60'])).
% 0.38/0.62  thf('91', plain,
% 0.38/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.62         = (k2_struct_0 @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['69', '70'])).
% 0.38/0.62  thf('92', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('93', plain,
% 0.38/0.62      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.62        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.38/0.62      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.38/0.62  thf('94', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.62      inference('simplify', [status(thm)], ['93'])).
% 0.38/0.62  thf('95', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_C @ 
% 0.38/0.62        (k1_zfmisc_1 @ 
% 0.38/0.62         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.38/0.62      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.62  thf('96', plain,
% 0.38/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.62         (~ (v2_funct_1 @ X28)
% 0.38/0.62          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.38/0.62          | (v1_funct_2 @ (k2_funct_1 @ X28) @ X29 @ X30)
% 0.38/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.38/0.62          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.38/0.62          | ~ (v1_funct_1 @ X28))),
% 0.38/0.62      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.38/0.62  thf('97', plain,
% 0.38/0.62      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.62        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.38/0.62        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.38/0.62           (k2_struct_0 @ sk_A))
% 0.38/0.62        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.62            != (k2_struct_0 @ sk_B))
% 0.38/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.62      inference('sup-', [status(thm)], ['95', '96'])).
% 0.38/0.62  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('99', plain,
% 0.38/0.62      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['59', '60'])).
% 0.38/0.62  thf('100', plain,
% 0.38/0.62      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.62         = (k2_struct_0 @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['69', '70'])).
% 0.38/0.62  thf('101', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('102', plain,
% 0.38/0.62      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.38/0.62         (k2_struct_0 @ sk_A))
% 0.38/0.62        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.38/0.62      inference('demod', [status(thm)], ['97', '98', '99', '100', '101'])).
% 0.38/0.62  thf('103', plain,
% 0.38/0.62      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.38/0.62        (k2_struct_0 @ sk_A))),
% 0.38/0.62      inference('simplify', [status(thm)], ['102'])).
% 0.38/0.62  thf(t55_funct_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.62       ( ( v2_funct_1 @ A ) =>
% 0.38/0.62         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.38/0.62           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.38/0.62  thf('104', plain,
% 0.38/0.62      (![X9 : $i]:
% 0.38/0.62         (~ (v2_funct_1 @ X9)
% 0.38/0.62          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.38/0.62          | ~ (v1_funct_1 @ X9)
% 0.38/0.62          | ~ (v1_relat_1 @ X9))),
% 0.38/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.62  thf(dt_k2_funct_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.62       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.38/0.62         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.38/0.62  thf('105', plain,
% 0.38/0.62      (![X4 : $i]:
% 0.38/0.62         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.38/0.62          | ~ (v1_funct_1 @ X4)
% 0.38/0.62          | ~ (v1_relat_1 @ X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.62  thf('106', plain,
% 0.38/0.62      (![X9 : $i]:
% 0.38/0.62         (~ (v2_funct_1 @ X9)
% 0.38/0.62          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.38/0.62          | ~ (v1_funct_1 @ X9)
% 0.38/0.62          | ~ (v1_relat_1 @ X9))),
% 0.38/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.62  thf('107', plain,
% 0.38/0.62      (![X4 : $i]:
% 0.38/0.62         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.38/0.62          | ~ (v1_funct_1 @ X4)
% 0.38/0.62          | ~ (v1_relat_1 @ X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.62  thf('108', plain,
% 0.38/0.62      (![X4 : $i]:
% 0.38/0.62         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.38/0.62          | ~ (v1_funct_1 @ X4)
% 0.38/0.62          | ~ (v1_relat_1 @ X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.62  thf(t61_funct_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.62       ( ( v2_funct_1 @ A ) =>
% 0.38/0.62         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.38/0.62             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.38/0.62           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.38/0.62             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.38/0.62  thf('109', plain,
% 0.38/0.62      (![X10 : $i]:
% 0.38/0.62         (~ (v2_funct_1 @ X10)
% 0.38/0.62          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 0.38/0.62              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 0.38/0.62          | ~ (v1_funct_1 @ X10)
% 0.38/0.62          | ~ (v1_relat_1 @ X10))),
% 0.38/0.62      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.38/0.62  thf(t48_funct_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.62           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.38/0.62               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.38/0.62             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.38/0.62  thf('110', plain,
% 0.38/0.62      (![X7 : $i, X8 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X7)
% 0.38/0.62          | ~ (v1_funct_1 @ X7)
% 0.38/0.62          | (v2_funct_1 @ X7)
% 0.38/0.62          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.38/0.62          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.38/0.62          | ~ (v1_funct_1 @ X8)
% 0.38/0.62          | ~ (v1_relat_1 @ X8))),
% 0.38/0.62      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.38/0.62  thf('111', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['109', '110'])).
% 0.38/0.62  thf(fc4_funct_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.38/0.62       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.38/0.62  thf('112', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.38/0.62  thf('113', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['111', '112'])).
% 0.38/0.62  thf('114', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['113'])).
% 0.38/0.62  thf('115', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['108', '114'])).
% 0.38/0.62  thf('116', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['115'])).
% 0.38/0.62  thf('117', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['107', '116'])).
% 0.38/0.62  thf('118', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['117'])).
% 0.38/0.62  thf('119', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['106', '118'])).
% 0.38/0.62  thf('120', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['119'])).
% 0.38/0.62  thf('121', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.62      inference('simplify', [status(thm)], ['93'])).
% 0.38/0.62  thf('122', plain,
% 0.38/0.62      (![X4 : $i]:
% 0.38/0.62         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.38/0.62          | ~ (v1_funct_1 @ X4)
% 0.38/0.62          | ~ (v1_relat_1 @ X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.62  thf('123', plain,
% 0.38/0.62      (![X9 : $i]:
% 0.38/0.62         (~ (v2_funct_1 @ X9)
% 0.38/0.62          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.38/0.62          | ~ (v1_funct_1 @ X9)
% 0.38/0.62          | ~ (v1_relat_1 @ X9))),
% 0.38/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.62  thf('124', plain,
% 0.38/0.62      (![X4 : $i]:
% 0.38/0.62         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.38/0.62          | ~ (v1_funct_1 @ X4)
% 0.38/0.62          | ~ (v1_relat_1 @ X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.62  thf('125', plain,
% 0.38/0.62      (![X4 : $i]:
% 0.38/0.62         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.38/0.62          | ~ (v1_funct_1 @ X4)
% 0.38/0.62          | ~ (v1_relat_1 @ X4))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.62  thf('126', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['119'])).
% 0.38/0.62  thf('127', plain,
% 0.38/0.62      (![X9 : $i]:
% 0.38/0.62         (~ (v2_funct_1 @ X9)
% 0.38/0.62          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 0.38/0.62          | ~ (v1_funct_1 @ X9)
% 0.38/0.62          | ~ (v1_relat_1 @ X9))),
% 0.38/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.62  thf('128', plain,
% 0.38/0.62      (![X10 : $i]:
% 0.38/0.62         (~ (v2_funct_1 @ X10)
% 0.38/0.62          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 0.38/0.62              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 0.38/0.62          | ~ (v1_funct_1 @ X10)
% 0.38/0.62          | ~ (v1_relat_1 @ X10))),
% 0.38/0.62      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.38/0.62  thf(t63_funct_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.62           ( ( ( v2_funct_1 @ A ) & 
% 0.38/0.62               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.38/0.62               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.38/0.62             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.38/0.62  thf('129', plain,
% 0.38/0.62      (![X11 : $i, X12 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X11)
% 0.38/0.62          | ~ (v1_funct_1 @ X11)
% 0.38/0.62          | ((X11) = (k2_funct_1 @ X12))
% 0.38/0.62          | ((k5_relat_1 @ X12 @ X11) != (k6_relat_1 @ (k1_relat_1 @ X12)))
% 0.38/0.62          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X11))
% 0.38/0.62          | ~ (v2_funct_1 @ X12)
% 0.38/0.62          | ~ (v1_funct_1 @ X12)
% 0.38/0.62          | ~ (v1_relat_1 @ X12))),
% 0.38/0.62      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.38/0.62  thf('130', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k6_relat_1 @ (k2_relat_1 @ X0))
% 0.38/0.62            != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['128', '129'])).
% 0.38/0.62  thf('131', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ((k6_relat_1 @ (k2_relat_1 @ X0))
% 0.38/0.62              != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.38/0.62      inference('simplify', [status(thm)], ['130'])).
% 0.38/0.62  thf('132', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((k6_relat_1 @ (k2_relat_1 @ X0)) != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['127', '131'])).
% 0.38/0.62  thf('133', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['132'])).
% 0.38/0.62  thf('134', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['126', '133'])).
% 0.38/0.62  thf('135', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['134'])).
% 0.38/0.62  thf('136', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['125', '135'])).
% 0.38/0.62  thf('137', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['136'])).
% 0.38/0.62  thf('138', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_funct_1 @ X0)
% 0.38/0.62          | ~ (v2_funct_1 @ X0)
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.62          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['124', '137'])).
% 0.38/0.62  thf('139', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.62          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.63          | ~ (v2_funct_1 @ X0)
% 0.38/0.63          | ~ (v1_funct_1 @ X0)
% 0.38/0.63          | ~ (v1_relat_1 @ X0))),
% 0.38/0.63      inference('simplify', [status(thm)], ['138'])).
% 0.38/0.63  thf('140', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.38/0.63          | ~ (v1_relat_1 @ X0)
% 0.38/0.63          | ~ (v1_funct_1 @ X0)
% 0.38/0.63          | ~ (v2_funct_1 @ X0)
% 0.38/0.63          | ~ (v1_relat_1 @ X0)
% 0.38/0.63          | ~ (v1_funct_1 @ X0)
% 0.38/0.63          | ~ (v2_funct_1 @ X0)
% 0.38/0.63          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['123', '139'])).
% 0.38/0.63  thf('141', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.63          | ~ (v2_funct_1 @ X0)
% 0.38/0.63          | ~ (v1_funct_1 @ X0)
% 0.38/0.63          | ~ (v1_relat_1 @ X0))),
% 0.38/0.63      inference('simplify', [status(thm)], ['140'])).
% 0.38/0.63  thf('142', plain,
% 0.38/0.63      (![X10 : $i]:
% 0.38/0.63         (~ (v2_funct_1 @ X10)
% 0.38/0.63          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 0.38/0.63              = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 0.38/0.63          | ~ (v1_funct_1 @ X10)
% 0.38/0.63          | ~ (v1_relat_1 @ X10))),
% 0.38/0.63      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.38/0.63  thf('143', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.38/0.63            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.38/0.63          | ~ (v1_relat_1 @ X0)
% 0.38/0.63          | ~ (v1_funct_1 @ X0)
% 0.38/0.63          | ~ (v2_funct_1 @ X0)
% 0.38/0.63          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.63          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.63          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.38/0.63      inference('sup+', [status(thm)], ['141', '142'])).
% 0.38/0.63  thf('144', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (~ (v1_relat_1 @ X0)
% 0.38/0.63          | ~ (v1_funct_1 @ X0)
% 0.38/0.63          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.63          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.63          | ~ (v2_funct_1 @ X0)
% 0.38/0.63          | ~ (v1_funct_1 @ X0)
% 0.38/0.63          | ~ (v1_relat_1 @ X0)
% 0.38/0.63          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.38/0.63              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['122', '143'])).
% 0.38/0.63  thf('145', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.38/0.63            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.38/0.63          | ~ (v2_funct_1 @ X0)
% 0.38/0.63          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.63          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.63          | ~ (v1_funct_1 @ X0)
% 0.38/0.63          | ~ (v1_relat_1 @ X0))),
% 0.38/0.63      inference('simplify', [status(thm)], ['144'])).
% 0.38/0.63  thf('146', plain,
% 0.38/0.63      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.63        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.63        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.38/0.63            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['121', '145'])).
% 0.38/0.63  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.63  thf('148', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('149', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('150', plain,
% 0.38/0.63      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.63        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.38/0.63            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.38/0.63      inference('demod', [status(thm)], ['146', '147', '148', '149'])).
% 0.38/0.63  thf('151', plain,
% 0.38/0.63      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.63        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.38/0.63            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['120', '150'])).
% 0.38/0.63  thf('152', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.63  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('154', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('155', plain,
% 0.38/0.63      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.38/0.63         = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.63      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 0.38/0.63  thf('156', plain,
% 0.38/0.63      (![X10 : $i]:
% 0.38/0.63         (~ (v2_funct_1 @ X10)
% 0.38/0.63          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 0.38/0.63              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 0.38/0.63          | ~ (v1_funct_1 @ X10)
% 0.38/0.63          | ~ (v1_relat_1 @ X10))),
% 0.38/0.63      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.38/0.63  thf('157', plain,
% 0.38/0.63      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.38/0.63         = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.63      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 0.38/0.63  thf('158', plain,
% 0.38/0.63      ((((k6_relat_1 @ (k2_relat_1 @ sk_C))
% 0.38/0.63          = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.38/0.63        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.63        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.63      inference('sup+', [status(thm)], ['156', '157'])).
% 0.38/0.63  thf('159', plain,
% 0.38/0.63      ((m1_subset_1 @ sk_C @ 
% 0.38/0.63        (k1_zfmisc_1 @ 
% 0.38/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i]:
% 0.38/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.63  thf('160', plain,
% 0.38/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.63         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.38/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.38/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.63  thf('161', plain,
% 0.38/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.63         = (k2_relat_1 @ sk_C))),
% 0.38/0.63      inference('sup-', [status(thm)], ['159', '160'])).
% 0.38/0.63  thf('162', plain,
% 0.38/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.63         = (k2_struct_0 @ sk_B))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('163', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.63      inference('sup+', [status(thm)], ['161', '162'])).
% 0.38/0.63  thf('164', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.63  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('166', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('167', plain,
% 0.38/0.63      (((k6_relat_1 @ (k2_struct_0 @ sk_B))
% 0.38/0.63         = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.63      inference('demod', [status(thm)], ['158', '163', '164', '165', '166'])).
% 0.38/0.63  thf('168', plain,
% 0.38/0.63      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.38/0.63         = (k6_relat_1 @ (k2_struct_0 @ sk_B)))),
% 0.38/0.63      inference('demod', [status(thm)], ['155', '167'])).
% 0.38/0.63  thf('169', plain,
% 0.38/0.63      (![X11 : $i, X12 : $i]:
% 0.38/0.63         (~ (v1_relat_1 @ X11)
% 0.38/0.63          | ~ (v1_funct_1 @ X11)
% 0.38/0.63          | ((X11) = (k2_funct_1 @ X12))
% 0.38/0.63          | ((k5_relat_1 @ X12 @ X11) != (k6_relat_1 @ (k1_relat_1 @ X12)))
% 0.38/0.63          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X11))
% 0.38/0.63          | ~ (v2_funct_1 @ X12)
% 0.38/0.63          | ~ (v1_funct_1 @ X12)
% 0.38/0.63          | ~ (v1_relat_1 @ X12))),
% 0.38/0.63      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.38/0.63  thf('170', plain,
% 0.38/0.63      ((((k6_relat_1 @ (k2_struct_0 @ sk_B))
% 0.38/0.63          != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.38/0.63        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.63        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.63        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.63        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.38/0.63        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.38/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.63        | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.63      inference('sup-', [status(thm)], ['168', '169'])).
% 0.38/0.63  thf('171', plain,
% 0.38/0.63      (((k6_relat_1 @ (k2_struct_0 @ sk_B))
% 0.38/0.63         = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.63      inference('demod', [status(thm)], ['158', '163', '164', '165', '166'])).
% 0.38/0.63  thf('172', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.63      inference('simplify', [status(thm)], ['93'])).
% 0.38/0.63  thf('173', plain,
% 0.38/0.63      (![X9 : $i]:
% 0.38/0.63         (~ (v2_funct_1 @ X9)
% 0.38/0.63          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.38/0.63          | ~ (v1_funct_1 @ X9)
% 0.38/0.63          | ~ (v1_relat_1 @ X9))),
% 0.38/0.63      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.63  thf('174', plain,
% 0.38/0.63      (![X4 : $i]:
% 0.38/0.63         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.38/0.63          | ~ (v1_funct_1 @ X4)
% 0.38/0.63          | ~ (v1_relat_1 @ X4))),
% 0.38/0.63      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.63  thf('175', plain,
% 0.38/0.63      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.38/0.63         = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.63      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 0.38/0.63  thf('176', plain,
% 0.38/0.63      (![X7 : $i, X8 : $i]:
% 0.38/0.63         (~ (v1_relat_1 @ X7)
% 0.38/0.63          | ~ (v1_funct_1 @ X7)
% 0.38/0.63          | (v2_funct_1 @ X7)
% 0.38/0.63          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.38/0.63          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.38/0.63          | ~ (v1_funct_1 @ X8)
% 0.38/0.63          | ~ (v1_relat_1 @ X8))),
% 0.38/0.63      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.38/0.63  thf('177', plain,
% 0.38/0.63      ((~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.38/0.63        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.63        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.38/0.63        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.63        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.63        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['175', '176'])).
% 0.38/0.63  thf('178', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 0.38/0.63      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.38/0.63  thf('179', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.63  thf('180', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('181', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.63  thf('182', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.63      inference('simplify', [status(thm)], ['93'])).
% 0.38/0.63  thf('183', plain,
% 0.38/0.63      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.38/0.63        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.63        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.63      inference('demod', [status(thm)],
% 0.38/0.63                ['177', '178', '179', '180', '181', '182'])).
% 0.38/0.63  thf('184', plain,
% 0.38/0.63      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.63        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.63        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['174', '183'])).
% 0.38/0.63  thf('185', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.63  thf('186', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('187', plain,
% 0.38/0.63      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.63        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.38/0.63      inference('demod', [status(thm)], ['184', '185', '186'])).
% 0.38/0.63  thf('188', plain,
% 0.38/0.63      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.38/0.63        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.63        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['173', '187'])).
% 0.38/0.63  thf('189', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.63  thf('190', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.63  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('192', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('193', plain,
% 0.38/0.63      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.38/0.63        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.63      inference('demod', [status(thm)], ['188', '189', '190', '191', '192'])).
% 0.38/0.63  thf('194', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.63      inference('simplify', [status(thm)], ['193'])).
% 0.38/0.63  thf('195', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.63  thf('196', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('197', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.63  thf('198', plain,
% 0.38/0.63      ((((k6_relat_1 @ (k2_struct_0 @ sk_B))
% 0.38/0.63          != (k6_relat_1 @ (k2_struct_0 @ sk_B)))
% 0.38/0.63        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.63        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.38/0.63        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.63      inference('demod', [status(thm)],
% 0.38/0.63                ['170', '171', '172', '194', '195', '196', '197'])).
% 0.38/0.63  thf('199', plain,
% 0.38/0.63      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.38/0.63        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.38/0.63        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.63      inference('simplify', [status(thm)], ['198'])).
% 0.38/0.63  thf('200', plain,
% 0.38/0.63      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.63        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.38/0.63        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['105', '199'])).
% 0.38/0.63  thf('201', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.63  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('203', plain,
% 0.38/0.63      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.38/0.63        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.63      inference('demod', [status(thm)], ['200', '201', '202'])).
% 0.38/0.63  thf('204', plain,
% 0.38/0.63      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.38/0.63        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.63        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.63      inference('sup-', [status(thm)], ['104', '203'])).
% 0.38/0.63  thf('205', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.63  thf('206', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.63  thf('207', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('208', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('209', plain,
% 0.38/0.63      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.38/0.63        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.63      inference('demod', [status(thm)], ['204', '205', '206', '207', '208'])).
% 0.38/0.63  thf('210', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.63      inference('simplify', [status(thm)], ['209'])).
% 0.38/0.63  thf('211', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.63      inference('simplify', [status(thm)], ['193'])).
% 0.38/0.63  thf('212', plain,
% 0.38/0.63      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.63          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.38/0.63        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.63            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.38/0.63      inference('demod', [status(thm)], ['85', '94', '103', '210', '211'])).
% 0.38/0.63  thf('213', plain,
% 0.38/0.63      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.63        (k1_zfmisc_1 @ 
% 0.38/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.38/0.63      inference('simplify', [status(thm)], ['82'])).
% 0.38/0.63  thf('214', plain,
% 0.38/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.63         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.38/0.63          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.38/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.63  thf('215', plain,
% 0.38/0.63      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.63         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['213', '214'])).
% 0.38/0.63  thf('216', plain,
% 0.38/0.63      (![X4 : $i]:
% 0.38/0.63         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.38/0.63          | ~ (v1_funct_1 @ X4)
% 0.38/0.63          | ~ (v1_relat_1 @ X4))),
% 0.38/0.63      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.63  thf('217', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.63      inference('simplify', [status(thm)], ['209'])).
% 0.38/0.63  thf('218', plain,
% 0.38/0.63      (![X9 : $i]:
% 0.38/0.63         (~ (v2_funct_1 @ X9)
% 0.38/0.63          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 0.38/0.63          | ~ (v1_funct_1 @ X9)
% 0.38/0.63          | ~ (v1_relat_1 @ X9))),
% 0.38/0.63      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.63  thf('219', plain,
% 0.38/0.63      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.38/0.63        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.63        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.63        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.63      inference('sup+', [status(thm)], ['217', '218'])).
% 0.38/0.63  thf('220', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.63  thf('221', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.63      inference('simplify', [status(thm)], ['93'])).
% 0.38/0.63  thf('222', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.63      inference('simplify', [status(thm)], ['193'])).
% 0.38/0.63  thf('223', plain,
% 0.38/0.63      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.38/0.63        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.63      inference('demod', [status(thm)], ['219', '220', '221', '222'])).
% 0.38/0.63  thf('224', plain,
% 0.38/0.63      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.63        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['216', '223'])).
% 0.38/0.63  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.63      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.63  thf('226', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('227', plain,
% 0.38/0.63      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['224', '225', '226'])).
% 0.38/0.63  thf('228', plain,
% 0.38/0.63      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.63         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.38/0.63      inference('demod', [status(thm)], ['215', '227'])).
% 0.38/0.63  thf('229', plain,
% 0.38/0.63      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.63          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.38/0.63        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.38/0.63      inference('demod', [status(thm)], ['212', '228'])).
% 0.38/0.63  thf('230', plain,
% 0.38/0.63      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.63         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.38/0.63      inference('simplify', [status(thm)], ['229'])).
% 0.38/0.63  thf('231', plain,
% 0.38/0.63      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.63          sk_C)),
% 0.38/0.63      inference('demod', [status(thm)], ['74', '230'])).
% 0.38/0.63  thf('232', plain,
% 0.38/0.63      ((m1_subset_1 @ sk_C @ 
% 0.38/0.63        (k1_zfmisc_1 @ 
% 0.38/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.63      inference('demod', [status(thm)], ['44', '45'])).
% 0.38/0.63  thf('233', plain,
% 0.38/0.63      ((m1_subset_1 @ sk_C @ 
% 0.38/0.63        (k1_zfmisc_1 @ 
% 0.38/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.63      inference('demod', [status(thm)], ['44', '45'])).
% 0.38/0.63  thf(reflexivity_r2_funct_2, axiom,
% 0.38/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.63         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.63       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.38/0.63  thf('234', plain,
% 0.38/0.63      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.63         ((r2_funct_2 @ X24 @ X25 @ X26 @ X26)
% 0.38/0.63          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.38/0.63          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.38/0.63          | ~ (v1_funct_1 @ X26)
% 0.38/0.63          | ~ (v1_funct_1 @ X27)
% 0.38/0.63          | ~ (v1_funct_2 @ X27 @ X24 @ X25)
% 0.38/0.63          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.38/0.63      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.38/0.63  thf('235', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (~ (m1_subset_1 @ X0 @ 
% 0.38/0.63             (k1_zfmisc_1 @ 
% 0.38/0.63              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.38/0.63          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.63          | ~ (v1_funct_1 @ X0)
% 0.38/0.63          | ~ (v1_funct_1 @ sk_C)
% 0.38/0.63          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.63          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.63             sk_C))),
% 0.38/0.63      inference('sup-', [status(thm)], ['233', '234'])).
% 0.38/0.63  thf('236', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('237', plain,
% 0.38/0.63      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.63      inference('demod', [status(thm)], ['56', '57'])).
% 0.38/0.63  thf('238', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (~ (m1_subset_1 @ X0 @ 
% 0.38/0.63             (k1_zfmisc_1 @ 
% 0.38/0.63              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.38/0.63          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.63          | ~ (v1_funct_1 @ X0)
% 0.38/0.63          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.63             sk_C))),
% 0.38/0.63      inference('demod', [status(thm)], ['235', '236', '237'])).
% 0.38/0.63  thf('239', plain,
% 0.38/0.63      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.38/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.63        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['232', '238'])).
% 0.38/0.63  thf('240', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('241', plain,
% 0.38/0.63      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.63      inference('demod', [status(thm)], ['56', '57'])).
% 0.38/0.63  thf('242', plain,
% 0.38/0.63      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.38/0.63      inference('demod', [status(thm)], ['239', '240', '241'])).
% 0.38/0.63  thf('243', plain, ($false), inference('demod', [status(thm)], ['231', '242'])).
% 0.38/0.63  
% 0.38/0.63  % SZS output end Refutation
% 0.38/0.63  
% 0.48/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
