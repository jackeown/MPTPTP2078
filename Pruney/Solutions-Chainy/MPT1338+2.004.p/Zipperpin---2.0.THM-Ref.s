%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qP5vcUhH9s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:46 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :  354 (44740 expanded)
%              Number of leaves         :   65 (12916 expanded)
%              Depth                    :   47
%              Number of atoms          : 2892 (1148739 expanded)
%              Number of equality atoms :  230 (57694 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t62_tops_2,conjecture,(
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
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

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
                 => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ B ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('0',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X69: $i] :
      ( ( ( k2_struct_0 @ X69 )
        = ( u1_struct_0 @ X69 ) )
      | ~ ( l1_struct_0 @ X69 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X69: $i] :
      ( ( ( k2_struct_0 @ X69 )
        = ( u1_struct_0 @ X69 ) )
      | ~ ( l1_struct_0 @ X69 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( ( k2_relset_1 @ X56 @ X57 @ X55 )
        = ( k2_relat_1 @ X55 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('11',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) )
      | ( v1_partfun1 @ X61 @ X62 )
      | ~ ( v1_funct_2 @ X61 @ X62 @ X63 )
      | ~ ( v1_funct_1 @ X61 )
      | ( v1_xboole_0 @ X63 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X69: $i] :
      ( ( ( k2_struct_0 @ X69 )
        = ( u1_struct_0 @ X69 ) )
      | ~ ( l1_struct_0 @ X69 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('19',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('24',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','24'])).

thf('26',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('27',plain,(
    ! [X70: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X70 ) )
      | ~ ( l1_struct_0 @ X70 )
      | ( v2_struct_0 @ X70 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('28',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','32'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('34',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v1_partfun1 @ X65 @ X64 )
      | ( ( k1_relat_1 @ X65 )
        = X64 )
      | ~ ( v4_relat_1 @ X65 @ X64 )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( v1_relat_1 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X36: $i,X37: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( v4_relat_1 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v4_relat_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','44'])).

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

thf('46',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ~ ( v2_funct_1 @ X66 )
      | ( ( k2_relset_1 @ X68 @ X67 @ X66 )
       != X67 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X66 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X67 @ X68 ) ) )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X67 ) ) )
      | ~ ( v1_funct_2 @ X66 @ X68 @ X67 )
      | ~ ( v1_funct_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('51',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('53',plain,(
    ! [X40: $i] :
      ( ~ ( v2_funct_1 @ X40 )
      | ( ( k2_funct_1 @ X40 )
        = ( k4_relat_1 @ X40 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k2_funct_1 @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['38','39'])).

thf('56',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X69: $i] :
      ( ( ( k2_struct_0 @ X69 )
        = ( u1_struct_0 @ X69 ) )
      | ~ ( l1_struct_0 @ X69 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('64',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X69: $i] :
      ( ( ( k2_struct_0 @ X69 )
        = ( u1_struct_0 @ X69 ) )
      | ~ ( l1_struct_0 @ X69 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('67',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('71',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['47','48','51','57','70','71'])).

thf('73',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','72'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('75',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) )
      | ( v1_partfun1 @ X61 @ X62 )
      | ~ ( v1_funct_2 @ X61 @ X62 @ X63 )
      | ~ ( v1_funct_1 @ X61 )
      | ( v1_xboole_0 @ X63 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ ( k4_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X69: $i] :
      ( ( ( k2_struct_0 @ X69 )
        = ( u1_struct_0 @ X69 ) )
      | ~ ( l1_struct_0 @ X69 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','44'])).

thf('82',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ~ ( v2_funct_1 @ X66 )
      | ( ( k2_relset_1 @ X68 @ X67 @ X66 )
       != X67 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X66 ) )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X67 ) ) )
      | ~ ( v1_funct_2 @ X66 @ X68 @ X67 )
      | ~ ( v1_funct_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('86',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('87',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('88',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87','88'])).

thf('90',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['80','89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('92',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X69: $i] :
      ( ( ( k2_struct_0 @ X69 )
        = ( u1_struct_0 @ X69 ) )
      | ~ ( l1_struct_0 @ X69 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','44'])).

thf('97',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ~ ( v2_funct_1 @ X66 )
      | ( ( k2_relset_1 @ X68 @ X67 @ X66 )
       != X67 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X66 ) @ X67 @ X68 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X67 ) ) )
      | ~ ( v1_funct_2 @ X66 @ X68 @ X67 )
      | ~ ( v1_funct_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('98',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('101',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('103',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['98','99','100','101','102','103'])).

thf('105',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['95','104'])).

thf('106',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('107',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ( v1_partfun1 @ ( k4_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['79','94','109'])).

thf('111',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( v1_partfun1 @ X65 @ X64 )
      | ( ( k1_relat_1 @ X65 )
        = X64 )
      | ~ ( v4_relat_1 @ X65 @ X64 )
      | ~ ( v1_relat_1 @ X65 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('112',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v4_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('114',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( v1_relat_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('115',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('117',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( v4_relat_1 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('118',plain,(
    v4_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['112','115','118'])).

thf('120',plain,(
    ! [X69: $i] :
      ( ( ( k2_struct_0 @ X69 )
        = ( u1_struct_0 @ X69 ) )
      | ~ ( l1_struct_0 @ X69 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('121',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['112','115','118'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('122',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('123',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('124',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ( X19 = X20 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('128',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('130',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B_1 ) )
    | ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['121','130'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('132',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('133',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B_1 ) )
    | ( r1_tarski @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X69: $i] :
      ( ( ( k2_struct_0 @ X69 )
        = ( u1_struct_0 @ X69 ) )
      | ~ ( l1_struct_0 @ X69 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('135',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['112','115','118'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('137',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('138',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('139',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('140',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('141',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ k1_xboole_0 )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['136','141'])).

thf('143',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('144',plain,
    ( ( ( k3_xboole_0 @ sk_C_1 @ k1_xboole_0 )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k3_xboole_0 @ sk_C_1 @ k1_xboole_0 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['135','144'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('146',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ( ( k3_xboole_0 @ X3 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('147',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B_1 ) )
    | ( r1_xboole_0 @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['112','115','118'])).

thf('149',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('150',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('152',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('153',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('154',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ( X19 = X20 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('159',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['157','160'])).

thf('162',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['152','161'])).

thf('163',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['149','162'])).

thf('164',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('165',plain,
    ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['148','165'])).

thf('167',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['147','166'])).

thf('168',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( r1_xboole_0 @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['134','167'])).

thf('169',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('170',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_C_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('172',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('173',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( r1_tarski @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('174',plain,(
    ! [X35: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X35 ) )
      | ~ ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('175',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('176',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['173','176'])).

thf('178',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['133','177'])).

thf('179',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['120','178'])).

thf('180',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('181',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['119','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('186',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('187',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X8 @ ( k2_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('188',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['185','188'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('190',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('191',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['184','193'])).

thf('195',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_B_1 ) )
      | ( ( k3_xboole_0 @ sk_C_1 @ X0 )
        = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('197',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_C_1 @ X0 )
        = ( k5_xboole_0 @ sk_C_1 @ sk_C_1 ) )
      | ( ( k2_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_C_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['198','199'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('201',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ sk_C_1 @ X0 ) )
      | ( ( k2_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ( ( k3_xboole_0 @ X3 @ X5 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_tarski @ X17 @ X18 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_C_1 @ X0 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_1 )
        = ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['184','193'])).

thf('211',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('212',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('213',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('214',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['209','210'])).

thf('215',plain,(
    ! [X69: $i] :
      ( ( ( k2_struct_0 @ X69 )
        = ( u1_struct_0 @ X69 ) )
      | ~ ( l1_struct_0 @ X69 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('216',plain,(
    ! [X69: $i] :
      ( ( ( k2_struct_0 @ X69 )
        = ( u1_struct_0 @ X69 ) )
      | ~ ( l1_struct_0 @ X69 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('217',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['3','44'])).

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

thf('218',plain,(
    ! [X71: $i,X72: $i,X73: $i] :
      ( ( ( k2_relset_1 @ X72 @ X71 @ X73 )
       != X71 )
      | ~ ( v2_funct_1 @ X73 )
      | ( ( k2_tops_2 @ X72 @ X71 @ X73 )
        = ( k2_funct_1 @ X73 ) )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X72 @ X71 ) ) )
      | ~ ( v1_funct_2 @ X73 @ X72 @ X71 )
      | ~ ( v1_funct_1 @ X73 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('219',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('222',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('223',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('225',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['219','220','221','222','223','224'])).

thf('226',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['216','225'])).

thf('227',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('228',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['226','227','228'])).

thf('230',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['215','230'])).

thf('232',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('233',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['231','232','233'])).

thf('235',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('236',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k4_relat_1 @ sk_C_1 ) )
     != ( k1_relat_1 @ sk_C_1 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','211','212','213','214','234','235'])).

thf('237',plain,(
    ! [X69: $i] :
      ( ( ( k2_struct_0 @ X69 )
        = ( u1_struct_0 @ X69 ) )
      | ~ ( l1_struct_0 @ X69 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('238',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('239',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['237','238'])).

thf('240',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('241',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['239','240','241'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('243',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( ( k1_relset_1 @ X53 @ X54 @ X52 )
        = ( k1_relat_1 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('244',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k4_relat_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['182'])).

thf('246',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k4_relat_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('247',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['229'])).

thf('248',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('249',plain,(
    ! [X69: $i] :
      ( ( ( k2_struct_0 @ X69 )
        = ( u1_struct_0 @ X69 ) )
      | ~ ( l1_struct_0 @ X69 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('250',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('251',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
       != ( k2_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['251','252'])).

thf('254',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['248','253'])).

thf('255',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('256',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('258',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('259',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['256','257','258'])).

thf('260',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k4_relat_1 @ sk_C_1 ) )
     != ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['247','259'])).

thf('261',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != ( k2_relat_1 @ sk_C_1 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['246','260'])).

thf('262',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['261'])).

thf('263',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('264',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['262','263'])).

thf('265',plain,(
    ( k2_relset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k4_relat_1 @ sk_C_1 ) )
 != ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['236','264'])).

thf('266',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['239','240','241'])).

thf('267',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ( ( k2_relset_1 @ X56 @ X57 @ X55 )
        = ( k2_relat_1 @ X55 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('268',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k4_relat_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('269',plain,(
    ! [X39: $i] :
      ( ( ( k10_relat_1 @ X39 @ ( k2_relat_1 @ X39 ) )
        = ( k1_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('270',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['182'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('271',plain,(
    ! [X38: $i] :
      ( ( ( k9_relat_1 @ X38 @ ( k1_relat_1 @ X38 ) )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('272',plain,
    ( ( ( k9_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['270','271'])).

thf('273',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('274',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v2_funct_1 @ X41 )
      | ( ( k10_relat_1 @ X41 @ X42 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X41 ) @ X42 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('275',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C_1 @ X0 )
        = ( k9_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['273','274'])).

thf('276',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['38','39'])).

thf('277',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ ( k4_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['275','276','277','278'])).

thf('280',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('281',plain,
    ( ( k10_relat_1 @ sk_C_1 @ ( k2_relat_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['272','279','280'])).

thf('282',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['269','281'])).

thf('283',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['38','39'])).

thf('284',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['282','283'])).

thf('285',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ ( k4_relat_1 @ sk_C_1 ) )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['268','284'])).

thf('286',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['265','285'])).

thf('287',plain,(
    $false ),
    inference(simplify,[status(thm)],['286'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qP5vcUhH9s
% 0.14/0.36  % Computer   : n006.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:31:53 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 2.13/2.33  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.13/2.33  % Solved by: fo/fo7.sh
% 2.13/2.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.13/2.33  % done 2833 iterations in 1.851s
% 2.13/2.33  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.13/2.33  % SZS output start Refutation
% 2.13/2.33  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.13/2.33  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.13/2.33  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.13/2.33  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.13/2.33  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.13/2.33  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.13/2.33  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.13/2.33  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.13/2.33  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 2.13/2.33  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.13/2.33  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.13/2.33  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.13/2.33  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.13/2.33  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.13/2.33  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.13/2.33  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.13/2.33  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.13/2.33  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.13/2.33  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.13/2.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.13/2.33  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.13/2.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.13/2.33  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.13/2.33  thf(sk_A_type, type, sk_A: $i).
% 2.13/2.33  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.13/2.33  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.13/2.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.13/2.33  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.13/2.33  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.13/2.33  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.13/2.33  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.13/2.33  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 2.13/2.33  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.13/2.33  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.13/2.34  thf(t62_tops_2, conjecture,
% 2.13/2.34    (![A:$i]:
% 2.13/2.34     ( ( l1_struct_0 @ A ) =>
% 2.13/2.34       ( ![B:$i]:
% 2.13/2.34         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.13/2.34           ( ![C:$i]:
% 2.13/2.34             ( ( ( v1_funct_1 @ C ) & 
% 2.13/2.34                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.13/2.34                 ( m1_subset_1 @
% 2.13/2.34                   C @ 
% 2.13/2.34                   ( k1_zfmisc_1 @
% 2.13/2.34                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.13/2.34               ( ( ( ( k2_relset_1 @
% 2.13/2.34                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.13/2.34                     ( k2_struct_0 @ B ) ) & 
% 2.13/2.34                   ( v2_funct_1 @ C ) ) =>
% 2.13/2.34                 ( ( ( k1_relset_1 @
% 2.13/2.34                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.13/2.34                       ( k2_tops_2 @
% 2.13/2.34                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.13/2.34                     ( k2_struct_0 @ B ) ) & 
% 2.13/2.34                   ( ( k2_relset_1 @
% 2.13/2.34                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.13/2.34                       ( k2_tops_2 @
% 2.13/2.34                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.13/2.34                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 2.13/2.34  thf(zf_stmt_0, negated_conjecture,
% 2.13/2.34    (~( ![A:$i]:
% 2.13/2.34        ( ( l1_struct_0 @ A ) =>
% 2.13/2.34          ( ![B:$i]:
% 2.13/2.34            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 2.13/2.34              ( ![C:$i]:
% 2.13/2.34                ( ( ( v1_funct_1 @ C ) & 
% 2.13/2.34                    ( v1_funct_2 @
% 2.13/2.34                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 2.13/2.34                    ( m1_subset_1 @
% 2.13/2.34                      C @ 
% 2.13/2.34                      ( k1_zfmisc_1 @
% 2.13/2.34                        ( k2_zfmisc_1 @
% 2.13/2.34                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 2.13/2.34                  ( ( ( ( k2_relset_1 @
% 2.13/2.34                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 2.13/2.34                        ( k2_struct_0 @ B ) ) & 
% 2.13/2.34                      ( v2_funct_1 @ C ) ) =>
% 2.13/2.34                    ( ( ( k1_relset_1 @
% 2.13/2.34                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.13/2.34                          ( k2_tops_2 @
% 2.13/2.34                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.13/2.34                        ( k2_struct_0 @ B ) ) & 
% 2.13/2.34                      ( ( k2_relset_1 @
% 2.13/2.34                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 2.13/2.34                          ( k2_tops_2 @
% 2.13/2.34                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 2.13/2.34                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 2.13/2.34    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 2.13/2.34  thf('0', plain,
% 2.13/2.34      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 2.13/2.34          != (k2_struct_0 @ sk_B_1))
% 2.13/2.34        | ((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 2.13/2.34            != (k2_struct_0 @ sk_A)))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('1', plain,
% 2.13/2.34      ((((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 2.13/2.34          != (k2_struct_0 @ sk_A)))
% 2.13/2.34         <= (~
% 2.13/2.34             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34                 sk_C_1))
% 2.13/2.34                = (k2_struct_0 @ sk_A))))),
% 2.13/2.34      inference('split', [status(esa)], ['0'])).
% 2.13/2.34  thf(d3_struct_0, axiom,
% 2.13/2.34    (![A:$i]:
% 2.13/2.34     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.13/2.34  thf('2', plain,
% 2.13/2.34      (![X69 : $i]:
% 2.13/2.34         (((k2_struct_0 @ X69) = (u1_struct_0 @ X69)) | ~ (l1_struct_0 @ X69))),
% 2.13/2.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.13/2.34  thf('3', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C_1 @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('4', plain,
% 2.13/2.34      (![X69 : $i]:
% 2.13/2.34         (((k2_struct_0 @ X69) = (u1_struct_0 @ X69)) | ~ (l1_struct_0 @ X69))),
% 2.13/2.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.13/2.34  thf('5', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C_1 @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('6', plain,
% 2.13/2.34      (((m1_subset_1 @ sk_C_1 @ 
% 2.13/2.34         (k1_zfmisc_1 @ 
% 2.13/2.34          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))
% 2.13/2.34        | ~ (l1_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['4', '5'])).
% 2.13/2.34  thf('7', plain, ((l1_struct_0 @ sk_B_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('8', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C_1 @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('demod', [status(thm)], ['6', '7'])).
% 2.13/2.34  thf('9', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C_1 @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf(redefinition_k2_relset_1, axiom,
% 2.13/2.34    (![A:$i,B:$i,C:$i]:
% 2.13/2.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.13/2.34       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.13/2.34  thf('10', plain,
% 2.13/2.34      (![X55 : $i, X56 : $i, X57 : $i]:
% 2.13/2.34         (((k2_relset_1 @ X56 @ X57 @ X55) = (k2_relat_1 @ X55))
% 2.13/2.34          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57))))),
% 2.13/2.34      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.13/2.34  thf('11', plain,
% 2.13/2.34      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34         = (k2_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('sup-', [status(thm)], ['9', '10'])).
% 2.13/2.34  thf('12', plain,
% 2.13/2.34      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34         = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('13', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['11', '12'])).
% 2.13/2.34  thf('14', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C_1 @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))))),
% 2.13/2.34      inference('demod', [status(thm)], ['8', '13'])).
% 2.13/2.34  thf(cc5_funct_2, axiom,
% 2.13/2.34    (![A:$i,B:$i]:
% 2.13/2.34     ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.13/2.34       ( ![C:$i]:
% 2.13/2.34         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.13/2.34           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 2.13/2.34             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 2.13/2.34  thf('15', plain,
% 2.13/2.34      (![X61 : $i, X62 : $i, X63 : $i]:
% 2.13/2.34         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63)))
% 2.13/2.34          | (v1_partfun1 @ X61 @ X62)
% 2.13/2.34          | ~ (v1_funct_2 @ X61 @ X62 @ X63)
% 2.13/2.34          | ~ (v1_funct_1 @ X61)
% 2.13/2.34          | (v1_xboole_0 @ X63))),
% 2.13/2.34      inference('cnf', [status(esa)], [cc5_funct_2])).
% 2.13/2.34  thf('16', plain,
% 2.13/2.34      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 2.13/2.34        | ~ (v1_funct_1 @ sk_C_1)
% 2.13/2.34        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))
% 2.13/2.34        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['14', '15'])).
% 2.13/2.34  thf('17', plain, ((v1_funct_1 @ sk_C_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('18', plain,
% 2.13/2.34      (![X69 : $i]:
% 2.13/2.34         (((k2_struct_0 @ X69) = (u1_struct_0 @ X69)) | ~ (l1_struct_0 @ X69))),
% 2.13/2.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.13/2.34  thf('19', plain,
% 2.13/2.34      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('20', plain,
% 2.13/2.34      (((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))
% 2.13/2.34        | ~ (l1_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['18', '19'])).
% 2.13/2.34  thf('21', plain, ((l1_struct_0 @ sk_B_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('22', plain,
% 2.13/2.34      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['20', '21'])).
% 2.13/2.34  thf('23', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['11', '12'])).
% 2.13/2.34  thf('24', plain,
% 2.13/2.34      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['22', '23'])).
% 2.13/2.34  thf('25', plain,
% 2.13/2.34      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 2.13/2.34        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.34      inference('demod', [status(thm)], ['16', '17', '24'])).
% 2.13/2.34  thf('26', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['11', '12'])).
% 2.13/2.34  thf(fc5_struct_0, axiom,
% 2.13/2.34    (![A:$i]:
% 2.13/2.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.13/2.34       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 2.13/2.34  thf('27', plain,
% 2.13/2.34      (![X70 : $i]:
% 2.13/2.34         (~ (v1_xboole_0 @ (k2_struct_0 @ X70))
% 2.13/2.34          | ~ (l1_struct_0 @ X70)
% 2.13/2.34          | (v2_struct_0 @ X70))),
% 2.13/2.34      inference('cnf', [status(esa)], [fc5_struct_0])).
% 2.13/2.34  thf('28', plain,
% 2.13/2.34      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 2.13/2.34        | (v2_struct_0 @ sk_B_1)
% 2.13/2.34        | ~ (l1_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup-', [status(thm)], ['26', '27'])).
% 2.13/2.34  thf('29', plain, ((l1_struct_0 @ sk_B_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('30', plain,
% 2.13/2.34      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1)) | (v2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['28', '29'])).
% 2.13/2.34  thf('31', plain, (~ (v2_struct_0 @ sk_B_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('32', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('clc', [status(thm)], ['30', '31'])).
% 2.13/2.34  thf('33', plain, ((v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 2.13/2.34      inference('clc', [status(thm)], ['25', '32'])).
% 2.13/2.34  thf(d4_partfun1, axiom,
% 2.13/2.34    (![A:$i,B:$i]:
% 2.13/2.34     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.13/2.34       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 2.13/2.34  thf('34', plain,
% 2.13/2.34      (![X64 : $i, X65 : $i]:
% 2.13/2.34         (~ (v1_partfun1 @ X65 @ X64)
% 2.13/2.34          | ((k1_relat_1 @ X65) = (X64))
% 2.13/2.34          | ~ (v4_relat_1 @ X65 @ X64)
% 2.13/2.34          | ~ (v1_relat_1 @ X65))),
% 2.13/2.34      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.13/2.34  thf('35', plain,
% 2.13/2.34      ((~ (v1_relat_1 @ sk_C_1)
% 2.13/2.34        | ~ (v4_relat_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 2.13/2.34        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['33', '34'])).
% 2.13/2.34  thf('36', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C_1 @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf(cc2_relat_1, axiom,
% 2.13/2.34    (![A:$i]:
% 2.13/2.34     ( ( v1_relat_1 @ A ) =>
% 2.13/2.34       ( ![B:$i]:
% 2.13/2.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.13/2.34  thf('37', plain,
% 2.13/2.34      (![X33 : $i, X34 : $i]:
% 2.13/2.34         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 2.13/2.34          | (v1_relat_1 @ X33)
% 2.13/2.34          | ~ (v1_relat_1 @ X34))),
% 2.13/2.34      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.13/2.34  thf('38', plain,
% 2.13/2.34      ((~ (v1_relat_1 @ 
% 2.13/2.34           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))
% 2.13/2.34        | (v1_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('sup-', [status(thm)], ['36', '37'])).
% 2.13/2.34  thf(fc6_relat_1, axiom,
% 2.13/2.34    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.13/2.34  thf('39', plain,
% 2.13/2.34      (![X36 : $i, X37 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X36 @ X37))),
% 2.13/2.34      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.13/2.34  thf('40', plain, ((v1_relat_1 @ sk_C_1)),
% 2.13/2.34      inference('demod', [status(thm)], ['38', '39'])).
% 2.13/2.34  thf('41', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C_1 @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf(cc2_relset_1, axiom,
% 2.13/2.34    (![A:$i,B:$i,C:$i]:
% 2.13/2.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.13/2.34       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.13/2.34  thf('42', plain,
% 2.13/2.34      (![X46 : $i, X47 : $i, X48 : $i]:
% 2.13/2.34         ((v4_relat_1 @ X46 @ X47)
% 2.13/2.34          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 2.13/2.34      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.13/2.34  thf('43', plain, ((v4_relat_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 2.13/2.34      inference('sup-', [status(thm)], ['41', '42'])).
% 2.13/2.34  thf('44', plain, (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 2.13/2.34      inference('demod', [status(thm)], ['35', '40', '43'])).
% 2.13/2.34  thf('45', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C_1 @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('demod', [status(thm)], ['3', '44'])).
% 2.13/2.34  thf(t31_funct_2, axiom,
% 2.13/2.34    (![A:$i,B:$i,C:$i]:
% 2.13/2.34     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.13/2.34         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.13/2.34       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.13/2.34         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.13/2.34           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.13/2.34           ( m1_subset_1 @
% 2.13/2.34             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.13/2.34  thf('46', plain,
% 2.13/2.34      (![X66 : $i, X67 : $i, X68 : $i]:
% 2.13/2.34         (~ (v2_funct_1 @ X66)
% 2.13/2.34          | ((k2_relset_1 @ X68 @ X67 @ X66) != (X67))
% 2.13/2.34          | (m1_subset_1 @ (k2_funct_1 @ X66) @ 
% 2.13/2.34             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X67 @ X68)))
% 2.13/2.34          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X67)))
% 2.13/2.34          | ~ (v1_funct_2 @ X66 @ X68 @ X67)
% 2.13/2.34          | ~ (v1_funct_1 @ X66))),
% 2.13/2.34      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.13/2.34  thf('47', plain,
% 2.13/2.34      ((~ (v1_funct_1 @ sk_C_1)
% 2.13/2.34        | ~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 2.13/2.34             (u1_struct_0 @ sk_B_1))
% 2.13/2.34        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 2.13/2.34           (k1_zfmisc_1 @ 
% 2.13/2.34            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1))))
% 2.13/2.34        | ((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34            sk_C_1) != (u1_struct_0 @ sk_B_1))
% 2.13/2.34        | ~ (v2_funct_1 @ sk_C_1))),
% 2.13/2.34      inference('sup-', [status(thm)], ['45', '46'])).
% 2.13/2.34  thf('48', plain, ((v1_funct_1 @ sk_C_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('49', plain,
% 2.13/2.34      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('50', plain, (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 2.13/2.34      inference('demod', [status(thm)], ['35', '40', '43'])).
% 2.13/2.34  thf('51', plain,
% 2.13/2.34      ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['49', '50'])).
% 2.13/2.34  thf('52', plain, ((v1_funct_1 @ sk_C_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf(d9_funct_1, axiom,
% 2.13/2.34    (![A:$i]:
% 2.13/2.34     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.13/2.34       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 2.13/2.34  thf('53', plain,
% 2.13/2.34      (![X40 : $i]:
% 2.13/2.34         (~ (v2_funct_1 @ X40)
% 2.13/2.34          | ((k2_funct_1 @ X40) = (k4_relat_1 @ X40))
% 2.13/2.34          | ~ (v1_funct_1 @ X40)
% 2.13/2.34          | ~ (v1_relat_1 @ X40))),
% 2.13/2.34      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.13/2.34  thf('54', plain,
% 2.13/2.34      ((~ (v1_relat_1 @ sk_C_1)
% 2.13/2.34        | ((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))
% 2.13/2.34        | ~ (v2_funct_1 @ sk_C_1))),
% 2.13/2.34      inference('sup-', [status(thm)], ['52', '53'])).
% 2.13/2.34  thf('55', plain, ((v1_relat_1 @ sk_C_1)),
% 2.13/2.34      inference('demod', [status(thm)], ['38', '39'])).
% 2.13/2.34  thf('56', plain, ((v2_funct_1 @ sk_C_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('57', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['54', '55', '56'])).
% 2.13/2.34  thf('58', plain,
% 2.13/2.34      (![X69 : $i]:
% 2.13/2.34         (((k2_struct_0 @ X69) = (u1_struct_0 @ X69)) | ~ (l1_struct_0 @ X69))),
% 2.13/2.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.13/2.34  thf('59', plain,
% 2.13/2.34      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34         = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('60', plain,
% 2.13/2.34      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34          = (k2_struct_0 @ sk_B_1))
% 2.13/2.34        | ~ (l1_struct_0 @ sk_A))),
% 2.13/2.34      inference('sup+', [status(thm)], ['58', '59'])).
% 2.13/2.34  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('62', plain,
% 2.13/2.34      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34         = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['60', '61'])).
% 2.13/2.34  thf('63', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['11', '12'])).
% 2.13/2.34  thf('64', plain,
% 2.13/2.34      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34         = (k2_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['62', '63'])).
% 2.13/2.34  thf('65', plain,
% 2.13/2.34      (![X69 : $i]:
% 2.13/2.34         (((k2_struct_0 @ X69) = (u1_struct_0 @ X69)) | ~ (l1_struct_0 @ X69))),
% 2.13/2.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.13/2.34  thf('66', plain, (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 2.13/2.34      inference('demod', [status(thm)], ['35', '40', '43'])).
% 2.13/2.34  thf('67', plain,
% 2.13/2.34      ((((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 2.13/2.34      inference('sup+', [status(thm)], ['65', '66'])).
% 2.13/2.34  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('69', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 2.13/2.34      inference('demod', [status(thm)], ['67', '68'])).
% 2.13/2.34  thf('70', plain,
% 2.13/2.34      (((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34         = (k2_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['64', '69'])).
% 2.13/2.34  thf('71', plain, ((v2_funct_1 @ sk_C_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('72', plain,
% 2.13/2.34      (((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.13/2.34         (k1_zfmisc_1 @ 
% 2.13/2.34          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1))))
% 2.13/2.34        | ((k2_relat_1 @ sk_C_1) != (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['47', '48', '51', '57', '70', '71'])).
% 2.13/2.34  thf('73', plain,
% 2.13/2.34      ((((k2_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_B_1))
% 2.13/2.34        | ~ (l1_struct_0 @ sk_B_1)
% 2.13/2.34        | (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.13/2.34           (k1_zfmisc_1 @ 
% 2.13/2.34            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1)))))),
% 2.13/2.34      inference('sup-', [status(thm)], ['2', '72'])).
% 2.13/2.34  thf('74', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['11', '12'])).
% 2.13/2.34  thf('75', plain, ((l1_struct_0 @ sk_B_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('76', plain,
% 2.13/2.34      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1))
% 2.13/2.34        | (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.13/2.34           (k1_zfmisc_1 @ 
% 2.13/2.34            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1)))))),
% 2.13/2.34      inference('demod', [status(thm)], ['73', '74', '75'])).
% 2.13/2.34  thf('77', plain,
% 2.13/2.34      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1))))),
% 2.13/2.34      inference('simplify', [status(thm)], ['76'])).
% 2.13/2.34  thf('78', plain,
% 2.13/2.34      (![X61 : $i, X62 : $i, X63 : $i]:
% 2.13/2.34         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63)))
% 2.13/2.34          | (v1_partfun1 @ X61 @ X62)
% 2.13/2.34          | ~ (v1_funct_2 @ X61 @ X62 @ X63)
% 2.13/2.34          | ~ (v1_funct_1 @ X61)
% 2.13/2.34          | (v1_xboole_0 @ X63))),
% 2.13/2.34      inference('cnf', [status(esa)], [cc5_funct_2])).
% 2.13/2.34  thf('79', plain,
% 2.13/2.34      (((v1_xboole_0 @ (k1_relat_1 @ sk_C_1))
% 2.13/2.34        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1))
% 2.13/2.34        | ~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34             (k1_relat_1 @ sk_C_1))
% 2.13/2.34        | (v1_partfun1 @ (k4_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['77', '78'])).
% 2.13/2.34  thf('80', plain,
% 2.13/2.34      (![X69 : $i]:
% 2.13/2.34         (((k2_struct_0 @ X69) = (u1_struct_0 @ X69)) | ~ (l1_struct_0 @ X69))),
% 2.13/2.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.13/2.34  thf('81', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C_1 @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('demod', [status(thm)], ['3', '44'])).
% 2.13/2.34  thf('82', plain,
% 2.13/2.34      (![X66 : $i, X67 : $i, X68 : $i]:
% 2.13/2.34         (~ (v2_funct_1 @ X66)
% 2.13/2.34          | ((k2_relset_1 @ X68 @ X67 @ X66) != (X67))
% 2.13/2.34          | (v1_funct_1 @ (k2_funct_1 @ X66))
% 2.13/2.34          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X67)))
% 2.13/2.34          | ~ (v1_funct_2 @ X66 @ X68 @ X67)
% 2.13/2.34          | ~ (v1_funct_1 @ X66))),
% 2.13/2.34      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.13/2.34  thf('83', plain,
% 2.13/2.34      ((~ (v1_funct_1 @ sk_C_1)
% 2.13/2.34        | ~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 2.13/2.34             (u1_struct_0 @ sk_B_1))
% 2.13/2.34        | (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 2.13/2.34        | ((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34            sk_C_1) != (u1_struct_0 @ sk_B_1))
% 2.13/2.34        | ~ (v2_funct_1 @ sk_C_1))),
% 2.13/2.34      inference('sup-', [status(thm)], ['81', '82'])).
% 2.13/2.34  thf('84', plain, ((v1_funct_1 @ sk_C_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('85', plain,
% 2.13/2.34      ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['49', '50'])).
% 2.13/2.34  thf('86', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['54', '55', '56'])).
% 2.13/2.34  thf('87', plain,
% 2.13/2.34      (((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34         = (k2_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['64', '69'])).
% 2.13/2.34  thf('88', plain, ((v2_funct_1 @ sk_C_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('89', plain,
% 2.13/2.34      (((v1_funct_1 @ (k4_relat_1 @ sk_C_1))
% 2.13/2.34        | ((k2_relat_1 @ sk_C_1) != (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['83', '84', '85', '86', '87', '88'])).
% 2.13/2.34  thf('90', plain,
% 2.13/2.34      ((((k2_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_B_1))
% 2.13/2.34        | ~ (l1_struct_0 @ sk_B_1)
% 2.13/2.34        | (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['80', '89'])).
% 2.13/2.34  thf('91', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['11', '12'])).
% 2.13/2.34  thf('92', plain, ((l1_struct_0 @ sk_B_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('93', plain,
% 2.13/2.34      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1))
% 2.13/2.34        | (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['90', '91', '92'])).
% 2.13/2.34  thf('94', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('simplify', [status(thm)], ['93'])).
% 2.13/2.34  thf('95', plain,
% 2.13/2.34      (![X69 : $i]:
% 2.13/2.34         (((k2_struct_0 @ X69) = (u1_struct_0 @ X69)) | ~ (l1_struct_0 @ X69))),
% 2.13/2.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.13/2.34  thf('96', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C_1 @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('demod', [status(thm)], ['3', '44'])).
% 2.13/2.34  thf('97', plain,
% 2.13/2.34      (![X66 : $i, X67 : $i, X68 : $i]:
% 2.13/2.34         (~ (v2_funct_1 @ X66)
% 2.13/2.34          | ((k2_relset_1 @ X68 @ X67 @ X66) != (X67))
% 2.13/2.34          | (v1_funct_2 @ (k2_funct_1 @ X66) @ X67 @ X68)
% 2.13/2.34          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X67)))
% 2.13/2.34          | ~ (v1_funct_2 @ X66 @ X68 @ X67)
% 2.13/2.34          | ~ (v1_funct_1 @ X66))),
% 2.13/2.34      inference('cnf', [status(esa)], [t31_funct_2])).
% 2.13/2.34  thf('98', plain,
% 2.13/2.34      ((~ (v1_funct_1 @ sk_C_1)
% 2.13/2.34        | ~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 2.13/2.34             (u1_struct_0 @ sk_B_1))
% 2.13/2.34        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34           (k1_relat_1 @ sk_C_1))
% 2.13/2.34        | ((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34            sk_C_1) != (u1_struct_0 @ sk_B_1))
% 2.13/2.34        | ~ (v2_funct_1 @ sk_C_1))),
% 2.13/2.34      inference('sup-', [status(thm)], ['96', '97'])).
% 2.13/2.34  thf('99', plain, ((v1_funct_1 @ sk_C_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('100', plain,
% 2.13/2.34      ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['49', '50'])).
% 2.13/2.34  thf('101', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['54', '55', '56'])).
% 2.13/2.34  thf('102', plain,
% 2.13/2.34      (((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34         = (k2_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['64', '69'])).
% 2.13/2.34  thf('103', plain, ((v2_funct_1 @ sk_C_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('104', plain,
% 2.13/2.34      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34         (k1_relat_1 @ sk_C_1))
% 2.13/2.34        | ((k2_relat_1 @ sk_C_1) != (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('demod', [status(thm)],
% 2.13/2.34                ['98', '99', '100', '101', '102', '103'])).
% 2.13/2.34  thf('105', plain,
% 2.13/2.34      ((((k2_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_B_1))
% 2.13/2.34        | ~ (l1_struct_0 @ sk_B_1)
% 2.13/2.34        | (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34           (k1_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['95', '104'])).
% 2.13/2.34  thf('106', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['11', '12'])).
% 2.13/2.34  thf('107', plain, ((l1_struct_0 @ sk_B_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('108', plain,
% 2.13/2.34      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1))
% 2.13/2.34        | (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34           (k1_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['105', '106', '107'])).
% 2.13/2.34  thf('109', plain,
% 2.13/2.34      ((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34        (k1_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('simplify', [status(thm)], ['108'])).
% 2.13/2.34  thf('110', plain,
% 2.13/2.34      (((v1_xboole_0 @ (k1_relat_1 @ sk_C_1))
% 2.13/2.34        | (v1_partfun1 @ (k4_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['79', '94', '109'])).
% 2.13/2.34  thf('111', plain,
% 2.13/2.34      (![X64 : $i, X65 : $i]:
% 2.13/2.34         (~ (v1_partfun1 @ X65 @ X64)
% 2.13/2.34          | ((k1_relat_1 @ X65) = (X64))
% 2.13/2.34          | ~ (v4_relat_1 @ X65 @ X64)
% 2.13/2.34          | ~ (v1_relat_1 @ X65))),
% 2.13/2.34      inference('cnf', [status(esa)], [d4_partfun1])).
% 2.13/2.34  thf('112', plain,
% 2.13/2.34      (((v1_xboole_0 @ (k1_relat_1 @ sk_C_1))
% 2.13/2.34        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 2.13/2.34        | ~ (v4_relat_1 @ (k4_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))
% 2.13/2.34        | ((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['110', '111'])).
% 2.13/2.34  thf('113', plain,
% 2.13/2.34      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1))))),
% 2.13/2.34      inference('simplify', [status(thm)], ['76'])).
% 2.13/2.34  thf(cc1_relset_1, axiom,
% 2.13/2.34    (![A:$i,B:$i,C:$i]:
% 2.13/2.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.13/2.34       ( v1_relat_1 @ C ) ))).
% 2.13/2.34  thf('114', plain,
% 2.13/2.34      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.13/2.34         ((v1_relat_1 @ X43)
% 2.13/2.34          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 2.13/2.34      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.13/2.34  thf('115', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('sup-', [status(thm)], ['113', '114'])).
% 2.13/2.34  thf('116', plain,
% 2.13/2.34      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1))))),
% 2.13/2.34      inference('simplify', [status(thm)], ['76'])).
% 2.13/2.34  thf('117', plain,
% 2.13/2.34      (![X46 : $i, X47 : $i, X48 : $i]:
% 2.13/2.34         ((v4_relat_1 @ X46 @ X47)
% 2.13/2.34          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 2.13/2.34      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.13/2.34  thf('118', plain,
% 2.13/2.34      ((v4_relat_1 @ (k4_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup-', [status(thm)], ['116', '117'])).
% 2.13/2.34  thf('119', plain,
% 2.13/2.34      (((v1_xboole_0 @ (k1_relat_1 @ sk_C_1))
% 2.13/2.34        | ((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['112', '115', '118'])).
% 2.13/2.34  thf('120', plain,
% 2.13/2.34      (![X69 : $i]:
% 2.13/2.34         (((k2_struct_0 @ X69) = (u1_struct_0 @ X69)) | ~ (l1_struct_0 @ X69))),
% 2.13/2.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.13/2.34  thf('121', plain,
% 2.13/2.34      (((v1_xboole_0 @ (k1_relat_1 @ sk_C_1))
% 2.13/2.34        | ((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['112', '115', '118'])).
% 2.13/2.34  thf(fc4_zfmisc_1, axiom,
% 2.13/2.34    (![A:$i,B:$i]:
% 2.13/2.34     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.13/2.34  thf('122', plain,
% 2.13/2.34      (![X27 : $i, X28 : $i]:
% 2.13/2.34         (~ (v1_xboole_0 @ X27) | (v1_xboole_0 @ (k2_zfmisc_1 @ X27 @ X28)))),
% 2.13/2.34      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 2.13/2.34  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.13/2.34  thf('123', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.13/2.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.13/2.34  thf(t8_boole, axiom,
% 2.13/2.34    (![A:$i,B:$i]:
% 2.13/2.34     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.13/2.34  thf('124', plain,
% 2.13/2.34      (![X19 : $i, X20 : $i]:
% 2.13/2.34         (~ (v1_xboole_0 @ X19) | ~ (v1_xboole_0 @ X20) | ((X19) = (X20)))),
% 2.13/2.34      inference('cnf', [status(esa)], [t8_boole])).
% 2.13/2.34  thf('125', plain,
% 2.13/2.34      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.13/2.34      inference('sup-', [status(thm)], ['123', '124'])).
% 2.13/2.34  thf('126', plain,
% 2.13/2.34      (![X0 : $i, X1 : $i]:
% 2.13/2.34         (~ (v1_xboole_0 @ X1) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['122', '125'])).
% 2.13/2.34  thf('127', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C_1 @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('demod', [status(thm)], ['6', '7'])).
% 2.13/2.34  thf('128', plain,
% 2.13/2.34      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.13/2.34        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.34      inference('sup+', [status(thm)], ['126', '127'])).
% 2.13/2.34  thf('129', plain, (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 2.13/2.34      inference('demod', [status(thm)], ['35', '40', '43'])).
% 2.13/2.34  thf('130', plain,
% 2.13/2.34      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.13/2.34        | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['128', '129'])).
% 2.13/2.34  thf('131', plain,
% 2.13/2.34      ((((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (u1_struct_0 @ sk_B_1))
% 2.13/2.34        | (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['121', '130'])).
% 2.13/2.34  thf(t3_subset, axiom,
% 2.13/2.34    (![A:$i,B:$i]:
% 2.13/2.34     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.13/2.34  thf('132', plain,
% 2.13/2.34      (![X30 : $i, X31 : $i]:
% 2.13/2.34         ((r1_tarski @ X30 @ X31) | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 2.13/2.34      inference('cnf', [status(esa)], [t3_subset])).
% 2.13/2.34  thf('133', plain,
% 2.13/2.34      ((((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (u1_struct_0 @ sk_B_1))
% 2.13/2.34        | (r1_tarski @ sk_C_1 @ k1_xboole_0))),
% 2.13/2.34      inference('sup-', [status(thm)], ['131', '132'])).
% 2.13/2.34  thf('134', plain,
% 2.13/2.34      (![X69 : $i]:
% 2.13/2.34         (((k2_struct_0 @ X69) = (u1_struct_0 @ X69)) | ~ (l1_struct_0 @ X69))),
% 2.13/2.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.13/2.34  thf('135', plain,
% 2.13/2.34      (((v1_xboole_0 @ (k1_relat_1 @ sk_C_1))
% 2.13/2.34        | ((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['112', '115', '118'])).
% 2.13/2.34  thf('136', plain,
% 2.13/2.34      (![X0 : $i, X1 : $i]:
% 2.13/2.34         (~ (v1_xboole_0 @ X1) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['122', '125'])).
% 2.13/2.34  thf('137', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C_1 @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('demod', [status(thm)], ['6', '7'])).
% 2.13/2.34  thf('138', plain,
% 2.13/2.34      (![X30 : $i, X31 : $i]:
% 2.13/2.34         ((r1_tarski @ X30 @ X31) | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 2.13/2.34      inference('cnf', [status(esa)], [t3_subset])).
% 2.13/2.34  thf('139', plain,
% 2.13/2.34      ((r1_tarski @ sk_C_1 @ 
% 2.13/2.34        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['137', '138'])).
% 2.13/2.34  thf(t28_xboole_1, axiom,
% 2.13/2.34    (![A:$i,B:$i]:
% 2.13/2.34     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.13/2.34  thf('140', plain,
% 2.13/2.34      (![X12 : $i, X13 : $i]:
% 2.13/2.34         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 2.13/2.34      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.13/2.34  thf('141', plain,
% 2.13/2.34      (((k3_xboole_0 @ sk_C_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1)))
% 2.13/2.34         = (sk_C_1))),
% 2.13/2.34      inference('sup-', [status(thm)], ['139', '140'])).
% 2.13/2.34  thf('142', plain,
% 2.13/2.34      ((((k3_xboole_0 @ sk_C_1 @ k1_xboole_0) = (sk_C_1))
% 2.13/2.34        | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.34      inference('sup+', [status(thm)], ['136', '141'])).
% 2.13/2.34  thf('143', plain, (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 2.13/2.34      inference('demod', [status(thm)], ['35', '40', '43'])).
% 2.13/2.34  thf('144', plain,
% 2.13/2.34      ((((k3_xboole_0 @ sk_C_1 @ k1_xboole_0) = (sk_C_1))
% 2.13/2.34        | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['142', '143'])).
% 2.13/2.34  thf('145', plain,
% 2.13/2.34      ((((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (u1_struct_0 @ sk_B_1))
% 2.13/2.34        | ((k3_xboole_0 @ sk_C_1 @ k1_xboole_0) = (sk_C_1)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['135', '144'])).
% 2.13/2.34  thf(d7_xboole_0, axiom,
% 2.13/2.34    (![A:$i,B:$i]:
% 2.13/2.34     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.13/2.34       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.13/2.34  thf('146', plain,
% 2.13/2.34      (![X3 : $i, X5 : $i]:
% 2.13/2.34         ((r1_xboole_0 @ X3 @ X5) | ((k3_xboole_0 @ X3 @ X5) != (k1_xboole_0)))),
% 2.13/2.34      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.13/2.34  thf('147', plain,
% 2.13/2.34      ((((sk_C_1) != (k1_xboole_0))
% 2.13/2.34        | ((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (u1_struct_0 @ sk_B_1))
% 2.13/2.34        | (r1_xboole_0 @ sk_C_1 @ k1_xboole_0))),
% 2.13/2.34      inference('sup-', [status(thm)], ['145', '146'])).
% 2.13/2.34  thf('148', plain,
% 2.13/2.34      (((v1_xboole_0 @ (k1_relat_1 @ sk_C_1))
% 2.13/2.34        | ((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['112', '115', '118'])).
% 2.13/2.34  thf('149', plain,
% 2.13/2.34      (![X27 : $i, X28 : $i]:
% 2.13/2.34         (~ (v1_xboole_0 @ X27) | (v1_xboole_0 @ (k2_zfmisc_1 @ X27 @ X28)))),
% 2.13/2.34      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 2.13/2.34  thf('150', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C_1 @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('151', plain,
% 2.13/2.34      (![X30 : $i, X31 : $i]:
% 2.13/2.34         ((r1_tarski @ X30 @ X31) | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 2.13/2.34      inference('cnf', [status(esa)], [t3_subset])).
% 2.13/2.34  thf('152', plain,
% 2.13/2.34      ((r1_tarski @ sk_C_1 @ 
% 2.13/2.34        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['150', '151'])).
% 2.13/2.34  thf(t92_xboole_1, axiom,
% 2.13/2.34    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 2.13/2.34  thf('153', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 2.13/2.34      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.13/2.34  thf('154', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.13/2.34      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.13/2.34  thf('155', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 2.13/2.34      inference('sup+', [status(thm)], ['153', '154'])).
% 2.13/2.34  thf('156', plain,
% 2.13/2.34      (![X19 : $i, X20 : $i]:
% 2.13/2.34         (~ (v1_xboole_0 @ X19) | ~ (v1_xboole_0 @ X20) | ((X19) = (X20)))),
% 2.13/2.34      inference('cnf', [status(esa)], [t8_boole])).
% 2.13/2.34  thf('157', plain,
% 2.13/2.34      (![X0 : $i, X1 : $i]:
% 2.13/2.34         (((k5_xboole_0 @ X0 @ X0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 2.13/2.34      inference('sup-', [status(thm)], ['155', '156'])).
% 2.13/2.34  thf('158', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 2.13/2.34      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.13/2.34  thf(t3_xboole_1, axiom,
% 2.13/2.34    (![A:$i]:
% 2.13/2.34     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.13/2.34  thf('159', plain,
% 2.13/2.34      (![X14 : $i]:
% 2.13/2.34         (((X14) = (k1_xboole_0)) | ~ (r1_tarski @ X14 @ k1_xboole_0))),
% 2.13/2.34      inference('cnf', [status(esa)], [t3_xboole_1])).
% 2.13/2.34  thf('160', plain,
% 2.13/2.34      (![X0 : $i, X1 : $i]:
% 2.13/2.34         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['158', '159'])).
% 2.13/2.34  thf('161', plain,
% 2.13/2.34      (![X0 : $i, X2 : $i]:
% 2.13/2.34         (~ (r1_tarski @ X2 @ X0)
% 2.13/2.34          | ~ (v1_xboole_0 @ X0)
% 2.13/2.34          | ((X2) = (k1_xboole_0)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['157', '160'])).
% 2.13/2.34  thf('162', plain,
% 2.13/2.34      ((((sk_C_1) = (k1_xboole_0))
% 2.13/2.34        | ~ (v1_xboole_0 @ 
% 2.13/2.34             (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('sup-', [status(thm)], ['152', '161'])).
% 2.13/2.34  thf('163', plain,
% 2.13/2.34      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ((sk_C_1) = (k1_xboole_0)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['149', '162'])).
% 2.13/2.34  thf('164', plain, (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 2.13/2.34      inference('demod', [status(thm)], ['35', '40', '43'])).
% 2.13/2.34  thf('165', plain,
% 2.13/2.34      ((~ (v1_xboole_0 @ (k1_relat_1 @ sk_C_1)) | ((sk_C_1) = (k1_xboole_0)))),
% 2.13/2.34      inference('demod', [status(thm)], ['163', '164'])).
% 2.13/2.34  thf('166', plain,
% 2.13/2.34      ((((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (u1_struct_0 @ sk_B_1))
% 2.13/2.34        | ((sk_C_1) = (k1_xboole_0)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['148', '165'])).
% 2.13/2.34  thf('167', plain,
% 2.13/2.34      (((r1_xboole_0 @ sk_C_1 @ k1_xboole_0)
% 2.13/2.34        | ((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('clc', [status(thm)], ['147', '166'])).
% 2.13/2.34  thf('168', plain,
% 2.13/2.34      ((((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (k2_struct_0 @ sk_B_1))
% 2.13/2.34        | ~ (l1_struct_0 @ sk_B_1)
% 2.13/2.34        | (r1_xboole_0 @ sk_C_1 @ k1_xboole_0))),
% 2.13/2.34      inference('sup+', [status(thm)], ['134', '167'])).
% 2.13/2.34  thf('169', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['11', '12'])).
% 2.13/2.34  thf('170', plain, ((l1_struct_0 @ sk_B_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('171', plain,
% 2.13/2.34      ((((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (k2_relat_1 @ sk_C_1))
% 2.13/2.34        | (r1_xboole_0 @ sk_C_1 @ k1_xboole_0))),
% 2.13/2.34      inference('demod', [status(thm)], ['168', '169', '170'])).
% 2.13/2.34  thf(t69_xboole_1, axiom,
% 2.13/2.34    (![A:$i,B:$i]:
% 2.13/2.34     ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.13/2.34       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 2.13/2.34  thf('172', plain,
% 2.13/2.34      (![X17 : $i, X18 : $i]:
% 2.13/2.34         (~ (r1_xboole_0 @ X17 @ X18)
% 2.13/2.34          | ~ (r1_tarski @ X17 @ X18)
% 2.13/2.34          | (v1_xboole_0 @ X17))),
% 2.13/2.34      inference('cnf', [status(esa)], [t69_xboole_1])).
% 2.13/2.34  thf('173', plain,
% 2.13/2.34      ((((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (k2_relat_1 @ sk_C_1))
% 2.13/2.34        | (v1_xboole_0 @ sk_C_1)
% 2.13/2.34        | ~ (r1_tarski @ sk_C_1 @ k1_xboole_0))),
% 2.13/2.34      inference('sup-', [status(thm)], ['171', '172'])).
% 2.13/2.34  thf(fc11_relat_1, axiom,
% 2.13/2.34    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 2.13/2.34  thf('174', plain,
% 2.13/2.34      (![X35 : $i]:
% 2.13/2.34         ((v1_xboole_0 @ (k2_relat_1 @ X35)) | ~ (v1_xboole_0 @ X35))),
% 2.13/2.34      inference('cnf', [status(esa)], [fc11_relat_1])).
% 2.13/2.34  thf('175', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('clc', [status(thm)], ['30', '31'])).
% 2.13/2.34  thf('176', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 2.13/2.34      inference('sup-', [status(thm)], ['174', '175'])).
% 2.13/2.34  thf('177', plain,
% 2.13/2.34      ((~ (r1_tarski @ sk_C_1 @ k1_xboole_0)
% 2.13/2.34        | ((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (k2_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('clc', [status(thm)], ['173', '176'])).
% 2.13/2.34  thf('178', plain,
% 2.13/2.34      ((((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (u1_struct_0 @ sk_B_1))
% 2.13/2.34        | ((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (k2_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['133', '177'])).
% 2.13/2.34  thf('179', plain,
% 2.13/2.34      ((((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (k2_struct_0 @ sk_B_1))
% 2.13/2.34        | ~ (l1_struct_0 @ sk_B_1)
% 2.13/2.34        | ((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (k2_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('sup+', [status(thm)], ['120', '178'])).
% 2.13/2.34  thf('180', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['11', '12'])).
% 2.13/2.34  thf('181', plain, ((l1_struct_0 @ sk_B_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('182', plain,
% 2.13/2.34      ((((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (k2_relat_1 @ sk_C_1))
% 2.13/2.34        | ((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (k2_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['179', '180', '181'])).
% 2.13/2.34  thf('183', plain,
% 2.13/2.34      (((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (k2_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('simplify', [status(thm)], ['182'])).
% 2.13/2.34  thf('184', plain,
% 2.13/2.34      (((v1_xboole_0 @ (k1_relat_1 @ sk_C_1))
% 2.13/2.34        | ((k2_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['119', '183'])).
% 2.13/2.34  thf('185', plain,
% 2.13/2.34      (![X0 : $i, X1 : $i]:
% 2.13/2.34         (~ (v1_xboole_0 @ X1) | ((k1_xboole_0) = (k2_zfmisc_1 @ X1 @ X0)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['122', '125'])).
% 2.13/2.34  thf('186', plain,
% 2.13/2.34      ((r1_tarski @ sk_C_1 @ 
% 2.13/2.34        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['137', '138'])).
% 2.13/2.34  thf(t10_xboole_1, axiom,
% 2.13/2.34    (![A:$i,B:$i,C:$i]:
% 2.13/2.34     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 2.13/2.34  thf('187', plain,
% 2.13/2.34      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.13/2.34         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ X8 @ (k2_xboole_0 @ X10 @ X9)))),
% 2.13/2.34      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.13/2.34  thf('188', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         (r1_tarski @ sk_C_1 @ 
% 2.13/2.34          (k2_xboole_0 @ X0 @ 
% 2.13/2.34           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('sup-', [status(thm)], ['186', '187'])).
% 2.13/2.34  thf('189', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         ((r1_tarski @ sk_C_1 @ (k2_xboole_0 @ X0 @ k1_xboole_0))
% 2.13/2.34          | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.34      inference('sup+', [status(thm)], ['185', '188'])).
% 2.13/2.34  thf(t1_boole, axiom,
% 2.13/2.34    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.13/2.34  thf('190', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 2.13/2.34      inference('cnf', [status(esa)], [t1_boole])).
% 2.13/2.34  thf('191', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         ((r1_tarski @ sk_C_1 @ X0) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.13/2.34      inference('demod', [status(thm)], ['189', '190'])).
% 2.13/2.34  thf('192', plain, (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 2.13/2.34      inference('demod', [status(thm)], ['35', '40', '43'])).
% 2.13/2.34  thf('193', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         ((r1_tarski @ sk_C_1 @ X0) | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['191', '192'])).
% 2.13/2.34  thf('194', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         (((k2_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_B_1))
% 2.13/2.34          | (r1_tarski @ sk_C_1 @ X0))),
% 2.13/2.34      inference('sup-', [status(thm)], ['184', '193'])).
% 2.13/2.34  thf('195', plain,
% 2.13/2.34      (![X12 : $i, X13 : $i]:
% 2.13/2.34         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 2.13/2.34      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.13/2.34  thf('196', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         (((k2_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_B_1))
% 2.13/2.34          | ((k3_xboole_0 @ sk_C_1 @ X0) = (sk_C_1)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['194', '195'])).
% 2.13/2.34  thf(t100_xboole_1, axiom,
% 2.13/2.34    (![A:$i,B:$i]:
% 2.13/2.34     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.13/2.34  thf('197', plain,
% 2.13/2.34      (![X6 : $i, X7 : $i]:
% 2.13/2.34         ((k4_xboole_0 @ X6 @ X7)
% 2.13/2.34           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 2.13/2.34      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.13/2.34  thf('198', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         (((k4_xboole_0 @ sk_C_1 @ X0) = (k5_xboole_0 @ sk_C_1 @ sk_C_1))
% 2.13/2.34          | ((k2_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('sup+', [status(thm)], ['196', '197'])).
% 2.13/2.34  thf('199', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 2.13/2.34      inference('cnf', [status(esa)], [t92_xboole_1])).
% 2.13/2.34  thf('200', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         (((k4_xboole_0 @ sk_C_1 @ X0) = (k1_xboole_0))
% 2.13/2.34          | ((k2_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['198', '199'])).
% 2.13/2.34  thf(t48_xboole_1, axiom,
% 2.13/2.34    (![A:$i,B:$i]:
% 2.13/2.34     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.13/2.34  thf('201', plain,
% 2.13/2.34      (![X15 : $i, X16 : $i]:
% 2.13/2.34         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 2.13/2.34           = (k3_xboole_0 @ X15 @ X16))),
% 2.13/2.34      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.13/2.34  thf('202', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         (((k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ X0))
% 2.13/2.34          | ((k2_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('sup+', [status(thm)], ['200', '201'])).
% 2.13/2.34  thf('203', plain,
% 2.13/2.34      (![X3 : $i, X5 : $i]:
% 2.13/2.34         ((r1_xboole_0 @ X3 @ X5) | ((k3_xboole_0 @ X3 @ X5) != (k1_xboole_0)))),
% 2.13/2.34      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.13/2.34  thf('204', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         (((k1_xboole_0) != (k1_xboole_0))
% 2.13/2.34          | ((k2_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_B_1))
% 2.13/2.34          | (r1_xboole_0 @ sk_C_1 @ X0))),
% 2.13/2.34      inference('sup-', [status(thm)], ['202', '203'])).
% 2.13/2.34  thf('205', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         ((r1_xboole_0 @ sk_C_1 @ X0)
% 2.13/2.34          | ((k2_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('simplify', [status(thm)], ['204'])).
% 2.13/2.34  thf('206', plain,
% 2.13/2.34      (![X17 : $i, X18 : $i]:
% 2.13/2.34         (~ (r1_xboole_0 @ X17 @ X18)
% 2.13/2.34          | ~ (r1_tarski @ X17 @ X18)
% 2.13/2.34          | (v1_xboole_0 @ X17))),
% 2.13/2.34      inference('cnf', [status(esa)], [t69_xboole_1])).
% 2.13/2.34  thf('207', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         (((k2_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_B_1))
% 2.13/2.34          | (v1_xboole_0 @ sk_C_1)
% 2.13/2.34          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 2.13/2.34      inference('sup-', [status(thm)], ['205', '206'])).
% 2.13/2.34  thf('208', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 2.13/2.34      inference('sup-', [status(thm)], ['174', '175'])).
% 2.13/2.34  thf('209', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         (~ (r1_tarski @ sk_C_1 @ X0)
% 2.13/2.34          | ((k2_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('clc', [status(thm)], ['207', '208'])).
% 2.13/2.34  thf('210', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         (((k2_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_B_1))
% 2.13/2.34          | (r1_tarski @ sk_C_1 @ X0))),
% 2.13/2.34      inference('sup-', [status(thm)], ['184', '193'])).
% 2.13/2.34  thf('211', plain, (((k2_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('clc', [status(thm)], ['209', '210'])).
% 2.13/2.34  thf('212', plain, (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 2.13/2.34      inference('demod', [status(thm)], ['35', '40', '43'])).
% 2.13/2.34  thf('213', plain, (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 2.13/2.34      inference('demod', [status(thm)], ['35', '40', '43'])).
% 2.13/2.34  thf('214', plain, (((k2_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('clc', [status(thm)], ['209', '210'])).
% 2.13/2.34  thf('215', plain,
% 2.13/2.34      (![X69 : $i]:
% 2.13/2.34         (((k2_struct_0 @ X69) = (u1_struct_0 @ X69)) | ~ (l1_struct_0 @ X69))),
% 2.13/2.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.13/2.34  thf('216', plain,
% 2.13/2.34      (![X69 : $i]:
% 2.13/2.34         (((k2_struct_0 @ X69) = (u1_struct_0 @ X69)) | ~ (l1_struct_0 @ X69))),
% 2.13/2.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.13/2.34  thf('217', plain,
% 2.13/2.34      ((m1_subset_1 @ sk_C_1 @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('demod', [status(thm)], ['3', '44'])).
% 2.13/2.34  thf(d4_tops_2, axiom,
% 2.13/2.34    (![A:$i,B:$i,C:$i]:
% 2.13/2.34     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.13/2.34         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.13/2.34       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.13/2.34         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 2.13/2.34  thf('218', plain,
% 2.13/2.34      (![X71 : $i, X72 : $i, X73 : $i]:
% 2.13/2.34         (((k2_relset_1 @ X72 @ X71 @ X73) != (X71))
% 2.13/2.34          | ~ (v2_funct_1 @ X73)
% 2.13/2.34          | ((k2_tops_2 @ X72 @ X71 @ X73) = (k2_funct_1 @ X73))
% 2.13/2.34          | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X72 @ X71)))
% 2.13/2.34          | ~ (v1_funct_2 @ X73 @ X72 @ X71)
% 2.13/2.34          | ~ (v1_funct_1 @ X73))),
% 2.13/2.34      inference('cnf', [status(esa)], [d4_tops_2])).
% 2.13/2.34  thf('219', plain,
% 2.13/2.34      ((~ (v1_funct_1 @ sk_C_1)
% 2.13/2.34        | ~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ 
% 2.13/2.34             (u1_struct_0 @ sk_B_1))
% 2.13/2.34        | ((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34            = (k2_funct_1 @ sk_C_1))
% 2.13/2.34        | ~ (v2_funct_1 @ sk_C_1)
% 2.13/2.34        | ((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34            sk_C_1) != (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['217', '218'])).
% 2.13/2.34  thf('220', plain, ((v1_funct_1 @ sk_C_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('221', plain,
% 2.13/2.34      ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['49', '50'])).
% 2.13/2.34  thf('222', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['54', '55', '56'])).
% 2.13/2.34  thf('223', plain, ((v2_funct_1 @ sk_C_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('224', plain,
% 2.13/2.34      (((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34         = (k2_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['64', '69'])).
% 2.13/2.34  thf('225', plain,
% 2.13/2.34      ((((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34          = (k4_relat_1 @ sk_C_1))
% 2.13/2.34        | ((k2_relat_1 @ sk_C_1) != (u1_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('demod', [status(thm)],
% 2.13/2.34                ['219', '220', '221', '222', '223', '224'])).
% 2.13/2.34  thf('226', plain,
% 2.13/2.34      ((((k2_relat_1 @ sk_C_1) != (k2_struct_0 @ sk_B_1))
% 2.13/2.34        | ~ (l1_struct_0 @ sk_B_1)
% 2.13/2.34        | ((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34            = (k4_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['216', '225'])).
% 2.13/2.34  thf('227', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['11', '12'])).
% 2.13/2.34  thf('228', plain, ((l1_struct_0 @ sk_B_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('229', plain,
% 2.13/2.34      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1))
% 2.13/2.34        | ((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34            = (k4_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['226', '227', '228'])).
% 2.13/2.34  thf('230', plain,
% 2.13/2.34      (((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34         = (k4_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('simplify', [status(thm)], ['229'])).
% 2.13/2.34  thf('231', plain,
% 2.13/2.34      ((((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (k2_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34          = (k4_relat_1 @ sk_C_1))
% 2.13/2.34        | ~ (l1_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['215', '230'])).
% 2.13/2.34  thf('232', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['11', '12'])).
% 2.13/2.34  thf('233', plain, ((l1_struct_0 @ sk_B_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('234', plain,
% 2.13/2.34      (((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ sk_C_1)
% 2.13/2.34         = (k4_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['231', '232', '233'])).
% 2.13/2.34  thf('235', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 2.13/2.34      inference('demod', [status(thm)], ['67', '68'])).
% 2.13/2.34  thf('236', plain,
% 2.13/2.34      ((((k2_relset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1) @ 
% 2.13/2.34          (k4_relat_1 @ sk_C_1)) != (k1_relat_1 @ sk_C_1)))
% 2.13/2.34         <= (~
% 2.13/2.34             (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34                 sk_C_1))
% 2.13/2.34                = (k2_struct_0 @ sk_A))))),
% 2.13/2.34      inference('demod', [status(thm)],
% 2.13/2.34                ['1', '211', '212', '213', '214', '234', '235'])).
% 2.13/2.34  thf('237', plain,
% 2.13/2.34      (![X69 : $i]:
% 2.13/2.34         (((k2_struct_0 @ X69) = (u1_struct_0 @ X69)) | ~ (l1_struct_0 @ X69))),
% 2.13/2.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.13/2.34  thf('238', plain,
% 2.13/2.34      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1))))),
% 2.13/2.34      inference('simplify', [status(thm)], ['76'])).
% 2.13/2.34  thf('239', plain,
% 2.13/2.34      (((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.13/2.34         (k1_zfmisc_1 @ 
% 2.13/2.34          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B_1) @ (k1_relat_1 @ sk_C_1))))
% 2.13/2.34        | ~ (l1_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['237', '238'])).
% 2.13/2.34  thf('240', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['11', '12'])).
% 2.13/2.34  thf('241', plain, ((l1_struct_0 @ sk_B_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('242', plain,
% 2.13/2.34      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))))),
% 2.13/2.34      inference('demod', [status(thm)], ['239', '240', '241'])).
% 2.13/2.34  thf(redefinition_k1_relset_1, axiom,
% 2.13/2.34    (![A:$i,B:$i,C:$i]:
% 2.13/2.34     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.13/2.34       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.13/2.34  thf('243', plain,
% 2.13/2.34      (![X52 : $i, X53 : $i, X54 : $i]:
% 2.13/2.34         (((k1_relset_1 @ X53 @ X54 @ X52) = (k1_relat_1 @ X52))
% 2.13/2.34          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54))))),
% 2.13/2.34      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.13/2.34  thf('244', plain,
% 2.13/2.34      (((k1_relset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1) @ 
% 2.13/2.34         (k4_relat_1 @ sk_C_1)) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['242', '243'])).
% 2.13/2.34  thf('245', plain,
% 2.13/2.34      (((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (k2_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('simplify', [status(thm)], ['182'])).
% 2.13/2.34  thf('246', plain,
% 2.13/2.34      (((k1_relset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1) @ 
% 2.13/2.34         (k4_relat_1 @ sk_C_1)) = (k2_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['244', '245'])).
% 2.13/2.34  thf('247', plain,
% 2.13/2.34      (((k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1)
% 2.13/2.34         = (k4_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('simplify', [status(thm)], ['229'])).
% 2.13/2.34  thf('248', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['11', '12'])).
% 2.13/2.34  thf('249', plain,
% 2.13/2.34      (![X69 : $i]:
% 2.13/2.34         (((k2_struct_0 @ X69) = (u1_struct_0 @ X69)) | ~ (l1_struct_0 @ X69))),
% 2.13/2.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.13/2.34  thf('250', plain,
% 2.13/2.34      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 2.13/2.34          != (k2_struct_0 @ sk_B_1)))
% 2.13/2.34         <= (~
% 2.13/2.34             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34                 sk_C_1))
% 2.13/2.34                = (k2_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('split', [status(esa)], ['0'])).
% 2.13/2.34  thf('251', plain,
% 2.13/2.34      (((((k1_relset_1 @ (k2_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 2.13/2.34           != (k2_struct_0 @ sk_B_1))
% 2.13/2.34         | ~ (l1_struct_0 @ sk_B_1)))
% 2.13/2.34         <= (~
% 2.13/2.34             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34                 sk_C_1))
% 2.13/2.34                = (k2_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('sup-', [status(thm)], ['249', '250'])).
% 2.13/2.34  thf('252', plain, ((l1_struct_0 @ sk_B_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('253', plain,
% 2.13/2.34      ((((k1_relset_1 @ (k2_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 2.13/2.34          != (k2_struct_0 @ sk_B_1)))
% 2.13/2.34         <= (~
% 2.13/2.34             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34                 sk_C_1))
% 2.13/2.34                = (k2_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('demod', [status(thm)], ['251', '252'])).
% 2.13/2.34  thf('254', plain,
% 2.13/2.34      ((((k1_relset_1 @ (k2_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 2.13/2.34          != (k2_struct_0 @ sk_B_1)))
% 2.13/2.34         <= (~
% 2.13/2.34             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34                 sk_C_1))
% 2.13/2.34                = (k2_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('sup-', [status(thm)], ['248', '253'])).
% 2.13/2.34  thf('255', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['11', '12'])).
% 2.13/2.34  thf('256', plain,
% 2.13/2.34      ((((k1_relset_1 @ (k2_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 2.13/2.34          != (k2_relat_1 @ sk_C_1)))
% 2.13/2.34         <= (~
% 2.13/2.34             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34                 sk_C_1))
% 2.13/2.34                = (k2_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('demod', [status(thm)], ['254', '255'])).
% 2.13/2.34  thf('257', plain, (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 2.13/2.34      inference('demod', [status(thm)], ['35', '40', '43'])).
% 2.13/2.34  thf('258', plain, (((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A))),
% 2.13/2.34      inference('demod', [status(thm)], ['35', '40', '43'])).
% 2.13/2.34  thf('259', plain,
% 2.13/2.34      ((((k1_relset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1) @ 
% 2.13/2.34          (k2_tops_2 @ (k1_relat_1 @ sk_C_1) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 2.13/2.34          != (k2_relat_1 @ sk_C_1)))
% 2.13/2.34         <= (~
% 2.13/2.34             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34                 sk_C_1))
% 2.13/2.34                = (k2_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('demod', [status(thm)], ['256', '257', '258'])).
% 2.13/2.34  thf('260', plain,
% 2.13/2.34      ((((k1_relset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1) @ 
% 2.13/2.34          (k4_relat_1 @ sk_C_1)) != (k2_relat_1 @ sk_C_1)))
% 2.13/2.34         <= (~
% 2.13/2.34             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34                 sk_C_1))
% 2.13/2.34                = (k2_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('sup-', [status(thm)], ['247', '259'])).
% 2.13/2.34  thf('261', plain,
% 2.13/2.34      ((((k2_relat_1 @ sk_C_1) != (k2_relat_1 @ sk_C_1)))
% 2.13/2.34         <= (~
% 2.13/2.34             (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ 
% 2.13/2.34                 sk_C_1))
% 2.13/2.34                = (k2_struct_0 @ sk_B_1))))),
% 2.13/2.34      inference('sup-', [status(thm)], ['246', '260'])).
% 2.13/2.34  thf('262', plain,
% 2.13/2.34      ((((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 2.13/2.34          = (k2_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('simplify', [status(thm)], ['261'])).
% 2.13/2.34  thf('263', plain,
% 2.13/2.34      (~
% 2.13/2.34       (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 2.13/2.34          = (k2_struct_0 @ sk_A))) | 
% 2.13/2.34       ~
% 2.13/2.34       (((k1_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 2.13/2.34          = (k2_struct_0 @ sk_B_1)))),
% 2.13/2.34      inference('split', [status(esa)], ['0'])).
% 2.13/2.34  thf('264', plain,
% 2.13/2.34      (~
% 2.13/2.34       (((k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 2.13/2.34          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C_1))
% 2.13/2.34          = (k2_struct_0 @ sk_A)))),
% 2.13/2.34      inference('sat_resolution*', [status(thm)], ['262', '263'])).
% 2.13/2.34  thf('265', plain,
% 2.13/2.34      (((k2_relset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1) @ 
% 2.13/2.34         (k4_relat_1 @ sk_C_1)) != (k1_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('simpl_trail', [status(thm)], ['236', '264'])).
% 2.13/2.34  thf('266', plain,
% 2.13/2.34      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 2.13/2.34        (k1_zfmisc_1 @ 
% 2.13/2.34         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))))),
% 2.13/2.34      inference('demod', [status(thm)], ['239', '240', '241'])).
% 2.13/2.34  thf('267', plain,
% 2.13/2.34      (![X55 : $i, X56 : $i, X57 : $i]:
% 2.13/2.34         (((k2_relset_1 @ X56 @ X57 @ X55) = (k2_relat_1 @ X55))
% 2.13/2.34          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57))))),
% 2.13/2.34      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.13/2.34  thf('268', plain,
% 2.13/2.34      (((k2_relset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1) @ 
% 2.13/2.34         (k4_relat_1 @ sk_C_1)) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('sup-', [status(thm)], ['266', '267'])).
% 2.13/2.34  thf(t169_relat_1, axiom,
% 2.13/2.34    (![A:$i]:
% 2.13/2.34     ( ( v1_relat_1 @ A ) =>
% 2.13/2.34       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 2.13/2.34  thf('269', plain,
% 2.13/2.34      (![X39 : $i]:
% 2.13/2.34         (((k10_relat_1 @ X39 @ (k2_relat_1 @ X39)) = (k1_relat_1 @ X39))
% 2.13/2.34          | ~ (v1_relat_1 @ X39))),
% 2.13/2.34      inference('cnf', [status(esa)], [t169_relat_1])).
% 2.13/2.34  thf('270', plain,
% 2.13/2.34      (((k1_relat_1 @ (k4_relat_1 @ sk_C_1)) = (k2_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('simplify', [status(thm)], ['182'])).
% 2.13/2.34  thf(t146_relat_1, axiom,
% 2.13/2.34    (![A:$i]:
% 2.13/2.34     ( ( v1_relat_1 @ A ) =>
% 2.13/2.34       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 2.13/2.34  thf('271', plain,
% 2.13/2.34      (![X38 : $i]:
% 2.13/2.34         (((k9_relat_1 @ X38 @ (k1_relat_1 @ X38)) = (k2_relat_1 @ X38))
% 2.13/2.34          | ~ (v1_relat_1 @ X38))),
% 2.13/2.34      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.13/2.34  thf('272', plain,
% 2.13/2.34      ((((k9_relat_1 @ (k4_relat_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1))
% 2.13/2.34          = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 2.13/2.34        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('sup+', [status(thm)], ['270', '271'])).
% 2.13/2.34  thf('273', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['54', '55', '56'])).
% 2.13/2.34  thf(t155_funct_1, axiom,
% 2.13/2.34    (![A:$i,B:$i]:
% 2.13/2.34     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.13/2.34       ( ( v2_funct_1 @ B ) =>
% 2.13/2.34         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 2.13/2.34  thf('274', plain,
% 2.13/2.34      (![X41 : $i, X42 : $i]:
% 2.13/2.34         (~ (v2_funct_1 @ X41)
% 2.13/2.34          | ((k10_relat_1 @ X41 @ X42)
% 2.13/2.34              = (k9_relat_1 @ (k2_funct_1 @ X41) @ X42))
% 2.13/2.34          | ~ (v1_funct_1 @ X41)
% 2.13/2.34          | ~ (v1_relat_1 @ X41))),
% 2.13/2.34      inference('cnf', [status(esa)], [t155_funct_1])).
% 2.13/2.34  thf('275', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         (((k10_relat_1 @ sk_C_1 @ X0)
% 2.13/2.34            = (k9_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0))
% 2.13/2.34          | ~ (v1_relat_1 @ sk_C_1)
% 2.13/2.34          | ~ (v1_funct_1 @ sk_C_1)
% 2.13/2.34          | ~ (v2_funct_1 @ sk_C_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['273', '274'])).
% 2.13/2.34  thf('276', plain, ((v1_relat_1 @ sk_C_1)),
% 2.13/2.34      inference('demod', [status(thm)], ['38', '39'])).
% 2.13/2.34  thf('277', plain, ((v1_funct_1 @ sk_C_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('278', plain, ((v2_funct_1 @ sk_C_1)),
% 2.13/2.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.13/2.34  thf('279', plain,
% 2.13/2.34      (![X0 : $i]:
% 2.13/2.34         ((k10_relat_1 @ sk_C_1 @ X0)
% 2.13/2.34           = (k9_relat_1 @ (k4_relat_1 @ sk_C_1) @ X0))),
% 2.13/2.34      inference('demod', [status(thm)], ['275', '276', '277', '278'])).
% 2.13/2.34  thf('280', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('sup-', [status(thm)], ['113', '114'])).
% 2.13/2.34  thf('281', plain,
% 2.13/2.34      (((k10_relat_1 @ sk_C_1 @ (k2_relat_1 @ sk_C_1))
% 2.13/2.34         = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['272', '279', '280'])).
% 2.13/2.34  thf('282', plain,
% 2.13/2.34      ((((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 2.13/2.34        | ~ (v1_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('sup+', [status(thm)], ['269', '281'])).
% 2.13/2.34  thf('283', plain, ((v1_relat_1 @ sk_C_1)),
% 2.13/2.34      inference('demod', [status(thm)], ['38', '39'])).
% 2.13/2.34  thf('284', plain,
% 2.13/2.34      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 2.13/2.34      inference('demod', [status(thm)], ['282', '283'])).
% 2.13/2.34  thf('285', plain,
% 2.13/2.34      (((k2_relset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_relat_1 @ sk_C_1) @ 
% 2.13/2.34         (k4_relat_1 @ sk_C_1)) = (k1_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['268', '284'])).
% 2.13/2.34  thf('286', plain, (((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_C_1))),
% 2.13/2.34      inference('demod', [status(thm)], ['265', '285'])).
% 2.13/2.34  thf('287', plain, ($false), inference('simplify', [status(thm)], ['286'])).
% 2.13/2.34  
% 2.13/2.34  % SZS output end Refutation
% 2.13/2.34  
% 2.19/2.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
