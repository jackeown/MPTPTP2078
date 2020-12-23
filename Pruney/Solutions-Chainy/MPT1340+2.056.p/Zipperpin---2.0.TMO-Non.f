%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wNOrrlWSTN

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:15 EST 2020

% Result     : Timeout 57.23s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  337 (6459 expanded)
%              Number of leaves         :   47 (1886 expanded)
%              Depth                    :   38
%              Number of atoms          : 3092 (145931 expanded)
%              Number of equality atoms :  224 (4674 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X35: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('6',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('13',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

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

thf('20',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ( ( k5_relat_1 @ X32 @ ( k2_funct_1 @ X32 ) )
        = ( k6_partfun1 @ X33 ) )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X33 @ X31 @ X32 )
       != X31 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('21',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('23',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','24','25','30','31'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('35',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

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

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('39',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('41',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('42',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X6 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
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

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('55',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('59',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('71',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52','59','71','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('77',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('78',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('80',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('81',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('84',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('85',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('89',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('90',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('91',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('93',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != X21 )
      | ( v1_partfun1 @ X22 @ X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('94',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v4_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
      | ( v1_partfun1 @ X22 @ ( k1_relat_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','94'])).

thf('96',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','95'])).

thf('97',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','104'])).

thf('106',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['88','105'])).

thf('107',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('108',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('112',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('114',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('115',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('118',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','42','78','87','115','116','117'])).

thf('119',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('122',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X32 ) @ X32 )
        = ( k6_partfun1 @ X31 ) )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X33 @ X31 @ X32 )
       != X31 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('123',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('127',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['120','128'])).

thf('130',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('131',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['132'])).

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

thf('134',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X11 @ X10 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('135',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('136',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X11 @ X10 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_B ) )
     != ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['133','136'])).

thf('138',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('139',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('140',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['86'])).

thf('141',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('142',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('143',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('148',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('149',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('150',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('153',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('158',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['150','151','158'])).

thf('160',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('161',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['141','161'])).

thf('163',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('166',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('168',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('169',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('170',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['166','167','170'])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('174',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_B ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','171','172','173'])).

thf('175',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_B ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['119','174'])).

thf('176',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_B ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,
    ( ( ( k6_partfun1 @ ( k2_struct_0 @ sk_B ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','176'])).

thf('178',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('179',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['12','181'])).

thf('183',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['166','167','170'])).

thf('184',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('185',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['182','183','184','185','186'])).

thf('188',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('190',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('191',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('192',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('193',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('196',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('197',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['193','194','195','196','197'])).

thf('199',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['190','198'])).

thf('200',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('201',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['199','200','201'])).

thf('203',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['202'])).

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

thf('204',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X36 @ X38 )
       != X36 )
      | ~ ( v2_funct_1 @ X38 )
      | ( ( k2_tops_2 @ X37 @ X36 @ X38 )
        = ( k2_funct_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('205',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['86'])).

thf('207',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('208',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('209',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X28 ) @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('210',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('213',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('214',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['210','211','212','213','214'])).

thf('216',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['207','215'])).

thf('217',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('218',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('220',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('222',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('223',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['205','206','220','223'])).

thf('225',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['189','224'])).

thf('226',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['187'])).

thf('227',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('228',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['226','227'])).

thf('229',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['166','167','170'])).

thf('230',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('231',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['86'])).

thf('232',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['228','229','230','231'])).

thf('233',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('234',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['232','233'])).

thf('235',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['225','234'])).

thf('236',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('237',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('238',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['239','240'])).

thf('242',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['236','241'])).

thf('243',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['242','243'])).

thf('245',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('246',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('247',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['102','103'])).

thf('249',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('251',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['247','248','251'])).

thf('253',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['166','167','170'])).

thf('254',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('256',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('257',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['244','254','255','256'])).

thf('258',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('259',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X36 @ X38 )
       != X36 )
      | ~ ( v2_funct_1 @ X38 )
      | ( ( k2_tops_2 @ X37 @ X36 @ X38 )
        = ( k2_funct_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('260',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('263',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('265',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['260','261','262','263','264'])).

thf('266',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['265'])).

thf('267',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['257','266'])).

thf('268',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['235','267'])).

thf('269',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['188','268'])).

thf('270',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('271',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('272',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_funct_2 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('273',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['271','272'])).

thf('274',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('275',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('276',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['273','274','275'])).

thf('277',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['270','276'])).

thf('278',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('280',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['277','278','279'])).

thf('281',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['269','280'])).

thf('282',plain,
    ( ( u1_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['281'])).

thf('283',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','282'])).

thf('284',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('285',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['283','284','285'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('287',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('288',plain,(
    $false ),
    inference(demod,[status(thm)],['10','286','287'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wNOrrlWSTN
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:24:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 57.23/57.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 57.23/57.40  % Solved by: fo/fo7.sh
% 57.23/57.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 57.23/57.40  % done 593 iterations in 56.923s
% 57.23/57.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 57.23/57.40  % SZS output start Refutation
% 57.23/57.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 57.23/57.40  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 57.23/57.40  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 57.23/57.40  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 57.23/57.40  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 57.23/57.40  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 57.23/57.40  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 57.23/57.40  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 57.23/57.40  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 57.23/57.40  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 57.23/57.40  thf(sk_C_type, type, sk_C: $i).
% 57.23/57.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 57.23/57.40  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 57.23/57.40  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 57.23/57.40  thf(sk_B_type, type, sk_B: $i).
% 57.23/57.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 57.23/57.40  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 57.23/57.40  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 57.23/57.40  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 57.23/57.40  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 57.23/57.40  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 57.23/57.40  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 57.23/57.40  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 57.23/57.40  thf(sk_A_type, type, sk_A: $i).
% 57.23/57.40  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 57.23/57.40  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 57.23/57.40  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 57.23/57.40  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 57.23/57.40  thf(t64_tops_2, conjecture,
% 57.23/57.40    (![A:$i]:
% 57.23/57.40     ( ( l1_struct_0 @ A ) =>
% 57.23/57.40       ( ![B:$i]:
% 57.23/57.40         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 57.23/57.40           ( ![C:$i]:
% 57.23/57.40             ( ( ( v1_funct_1 @ C ) & 
% 57.23/57.40                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 57.23/57.40                 ( m1_subset_1 @
% 57.23/57.40                   C @ 
% 57.23/57.40                   ( k1_zfmisc_1 @
% 57.23/57.40                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 57.23/57.40               ( ( ( ( k2_relset_1 @
% 57.23/57.40                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 57.23/57.40                     ( k2_struct_0 @ B ) ) & 
% 57.23/57.40                   ( v2_funct_1 @ C ) ) =>
% 57.23/57.40                 ( r2_funct_2 @
% 57.23/57.40                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 57.23/57.40                   ( k2_tops_2 @
% 57.23/57.40                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 57.23/57.40                     ( k2_tops_2 @
% 57.23/57.40                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 57.23/57.40                   C ) ) ) ) ) ) ))).
% 57.23/57.40  thf(zf_stmt_0, negated_conjecture,
% 57.23/57.40    (~( ![A:$i]:
% 57.23/57.40        ( ( l1_struct_0 @ A ) =>
% 57.23/57.40          ( ![B:$i]:
% 57.23/57.40            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 57.23/57.40              ( ![C:$i]:
% 57.23/57.40                ( ( ( v1_funct_1 @ C ) & 
% 57.23/57.40                    ( v1_funct_2 @
% 57.23/57.40                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 57.23/57.40                    ( m1_subset_1 @
% 57.23/57.40                      C @ 
% 57.23/57.40                      ( k1_zfmisc_1 @
% 57.23/57.40                        ( k2_zfmisc_1 @
% 57.23/57.40                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 57.23/57.40                  ( ( ( ( k2_relset_1 @
% 57.23/57.40                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 57.23/57.40                        ( k2_struct_0 @ B ) ) & 
% 57.23/57.40                      ( v2_funct_1 @ C ) ) =>
% 57.23/57.40                    ( r2_funct_2 @
% 57.23/57.40                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 57.23/57.40                      ( k2_tops_2 @
% 57.23/57.40                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 57.23/57.40                        ( k2_tops_2 @
% 57.23/57.40                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 57.23/57.40                      C ) ) ) ) ) ) ) )),
% 57.23/57.40    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 57.23/57.40  thf('0', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf(redefinition_k2_relset_1, axiom,
% 57.23/57.40    (![A:$i,B:$i,C:$i]:
% 57.23/57.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 57.23/57.40       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 57.23/57.40  thf('1', plain,
% 57.23/57.40      (![X15 : $i, X16 : $i, X17 : $i]:
% 57.23/57.40         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 57.23/57.40          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 57.23/57.40      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 57.23/57.40  thf('2', plain,
% 57.23/57.40      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 57.23/57.40         = (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['0', '1'])).
% 57.23/57.40  thf('3', plain,
% 57.23/57.40      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 57.23/57.40         = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['2', '3'])).
% 57.23/57.40  thf(fc5_struct_0, axiom,
% 57.23/57.40    (![A:$i]:
% 57.23/57.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 57.23/57.40       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 57.23/57.40  thf('5', plain,
% 57.23/57.40      (![X35 : $i]:
% 57.23/57.40         (~ (v1_xboole_0 @ (k2_struct_0 @ X35))
% 57.23/57.40          | ~ (l1_struct_0 @ X35)
% 57.23/57.40          | (v2_struct_0 @ X35))),
% 57.23/57.40      inference('cnf', [status(esa)], [fc5_struct_0])).
% 57.23/57.40  thf('6', plain,
% 57.23/57.40      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 57.23/57.40        | (v2_struct_0 @ sk_B)
% 57.23/57.40        | ~ (l1_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup-', [status(thm)], ['4', '5'])).
% 57.23/57.40  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('8', plain,
% 57.23/57.40      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 57.23/57.40      inference('demod', [status(thm)], ['6', '7'])).
% 57.23/57.40  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('clc', [status(thm)], ['8', '9'])).
% 57.23/57.40  thf(d3_struct_0, axiom,
% 57.23/57.40    (![A:$i]:
% 57.23/57.40     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 57.23/57.40  thf('11', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf(t55_funct_1, axiom,
% 57.23/57.40    (![A:$i]:
% 57.23/57.40     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 57.23/57.40       ( ( v2_funct_1 @ A ) =>
% 57.23/57.40         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 57.23/57.40           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 57.23/57.40  thf('12', plain,
% 57.23/57.40      (![X9 : $i]:
% 57.23/57.40         (~ (v2_funct_1 @ X9)
% 57.23/57.40          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 57.23/57.40          | ~ (v1_funct_1 @ X9)
% 57.23/57.40          | ~ (v1_relat_1 @ X9))),
% 57.23/57.40      inference('cnf', [status(esa)], [t55_funct_1])).
% 57.23/57.40  thf('13', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('14', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('15', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('16', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('17', plain,
% 57.23/57.40      (((m1_subset_1 @ sk_C @ 
% 57.23/57.40         (k1_zfmisc_1 @ 
% 57.23/57.40          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 57.23/57.40        | ~ (l1_struct_0 @ sk_A))),
% 57.23/57.40      inference('sup+', [status(thm)], ['15', '16'])).
% 57.23/57.40  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('19', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('demod', [status(thm)], ['17', '18'])).
% 57.23/57.40  thf(t35_funct_2, axiom,
% 57.23/57.40    (![A:$i,B:$i,C:$i]:
% 57.23/57.40     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 57.23/57.40         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 57.23/57.40       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 57.23/57.40         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 57.23/57.40           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 57.23/57.40             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 57.23/57.40  thf('20', plain,
% 57.23/57.40      (![X31 : $i, X32 : $i, X33 : $i]:
% 57.23/57.40         (((X31) = (k1_xboole_0))
% 57.23/57.40          | ~ (v1_funct_1 @ X32)
% 57.23/57.40          | ~ (v1_funct_2 @ X32 @ X33 @ X31)
% 57.23/57.40          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 57.23/57.40          | ((k5_relat_1 @ X32 @ (k2_funct_1 @ X32)) = (k6_partfun1 @ X33))
% 57.23/57.40          | ~ (v2_funct_1 @ X32)
% 57.23/57.40          | ((k2_relset_1 @ X33 @ X31 @ X32) != (X31)))),
% 57.23/57.40      inference('cnf', [status(esa)], [t35_funct_2])).
% 57.23/57.40  thf('21', plain,
% 57.23/57.40      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 57.23/57.40          != (u1_struct_0 @ sk_B))
% 57.23/57.40        | ~ (v2_funct_1 @ sk_C)
% 57.23/57.40        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 57.23/57.40            = (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 57.23/57.40        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 57.23/57.40        | ~ (v1_funct_1 @ sk_C)
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['19', '20'])).
% 57.23/57.40  thf('22', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('demod', [status(thm)], ['17', '18'])).
% 57.23/57.40  thf('23', plain,
% 57.23/57.40      (![X15 : $i, X16 : $i, X17 : $i]:
% 57.23/57.40         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 57.23/57.40          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 57.23/57.40      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 57.23/57.40  thf('24', plain,
% 57.23/57.40      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 57.23/57.40         = (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['22', '23'])).
% 57.23/57.40  thf('25', plain, ((v2_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('26', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('27', plain,
% 57.23/57.40      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('28', plain,
% 57.23/57.40      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 57.23/57.40        | ~ (l1_struct_0 @ sk_A))),
% 57.23/57.40      inference('sup+', [status(thm)], ['26', '27'])).
% 57.23/57.40  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('30', plain,
% 57.23/57.40      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 57.23/57.40      inference('demod', [status(thm)], ['28', '29'])).
% 57.23/57.40  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('32', plain,
% 57.23/57.40      ((((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B))
% 57.23/57.40        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 57.23/57.40            = (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('demod', [status(thm)], ['21', '24', '25', '30', '31'])).
% 57.23/57.40  thf('33', plain,
% 57.23/57.40      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 57.23/57.40        | ~ (l1_struct_0 @ sk_B)
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 57.23/57.40            = (k6_partfun1 @ (k2_struct_0 @ sk_A))))),
% 57.23/57.40      inference('sup-', [status(thm)], ['14', '32'])).
% 57.23/57.40  thf('34', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['2', '3'])).
% 57.23/57.40  thf('35', plain, ((l1_struct_0 @ sk_B)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('36', plain,
% 57.23/57.40      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 57.23/57.40            = (k6_partfun1 @ (k2_struct_0 @ sk_A))))),
% 57.23/57.40      inference('demod', [status(thm)], ['33', '34', '35'])).
% 57.23/57.40  thf('37', plain,
% 57.23/57.40      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 57.23/57.40          = (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('simplify', [status(thm)], ['36'])).
% 57.23/57.40  thf(t48_funct_1, axiom,
% 57.23/57.40    (![A:$i]:
% 57.23/57.40     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 57.23/57.40       ( ![B:$i]:
% 57.23/57.40         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 57.23/57.40           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 57.23/57.40               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 57.23/57.40             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 57.23/57.40  thf('38', plain,
% 57.23/57.40      (![X7 : $i, X8 : $i]:
% 57.23/57.40         (~ (v1_relat_1 @ X7)
% 57.23/57.40          | ~ (v1_funct_1 @ X7)
% 57.23/57.40          | (v2_funct_1 @ X8)
% 57.23/57.40          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 57.23/57.40          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 57.23/57.40          | ~ (v1_funct_1 @ X8)
% 57.23/57.40          | ~ (v1_relat_1 @ X8))),
% 57.23/57.40      inference('cnf', [status(esa)], [t48_funct_1])).
% 57.23/57.40  thf('39', plain,
% 57.23/57.40      ((~ (v2_funct_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 57.23/57.40        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ~ (v1_funct_1 @ sk_C)
% 57.23/57.40        | ~ (v1_relat_1 @ sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['37', '38'])).
% 57.23/57.40  thf(fc4_funct_1, axiom,
% 57.23/57.40    (![A:$i]:
% 57.23/57.40     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 57.23/57.40       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 57.23/57.40  thf('40', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 57.23/57.40      inference('cnf', [status(esa)], [fc4_funct_1])).
% 57.23/57.40  thf(redefinition_k6_partfun1, axiom,
% 57.23/57.40    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 57.23/57.40  thf('41', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 57.23/57.40      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 57.23/57.40  thf('42', plain, (![X6 : $i]: (v2_funct_1 @ (k6_partfun1 @ X6))),
% 57.23/57.40      inference('demod', [status(thm)], ['40', '41'])).
% 57.23/57.40  thf('43', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('44', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('demod', [status(thm)], ['17', '18'])).
% 57.23/57.40  thf('45', plain,
% 57.23/57.40      (((m1_subset_1 @ sk_C @ 
% 57.23/57.40         (k1_zfmisc_1 @ 
% 57.23/57.40          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 57.23/57.40        | ~ (l1_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['43', '44'])).
% 57.23/57.40  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('47', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 57.23/57.40      inference('demod', [status(thm)], ['45', '46'])).
% 57.23/57.40  thf('48', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['2', '3'])).
% 57.23/57.40  thf('49', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 57.23/57.40      inference('demod', [status(thm)], ['47', '48'])).
% 57.23/57.40  thf(t31_funct_2, axiom,
% 57.23/57.40    (![A:$i,B:$i,C:$i]:
% 57.23/57.40     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 57.23/57.40         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 57.23/57.40       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 57.23/57.40         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 57.23/57.40           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 57.23/57.40           ( m1_subset_1 @
% 57.23/57.40             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 57.23/57.40  thf('50', plain,
% 57.23/57.40      (![X28 : $i, X29 : $i, X30 : $i]:
% 57.23/57.40         (~ (v2_funct_1 @ X28)
% 57.23/57.40          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 57.23/57.40          | (m1_subset_1 @ (k2_funct_1 @ X28) @ 
% 57.23/57.40             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 57.23/57.40          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 57.23/57.40          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 57.23/57.40          | ~ (v1_funct_1 @ X28))),
% 57.23/57.40      inference('cnf', [status(esa)], [t31_funct_2])).
% 57.23/57.40  thf('51', plain,
% 57.23/57.40      ((~ (v1_funct_1 @ sk_C)
% 57.23/57.40        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 57.23/57.40        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 57.23/57.40           (k1_zfmisc_1 @ 
% 57.23/57.40            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 57.23/57.40        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 57.23/57.40            != (k2_relat_1 @ sk_C))
% 57.23/57.40        | ~ (v2_funct_1 @ sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['49', '50'])).
% 57.23/57.40  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('53', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('54', plain,
% 57.23/57.40      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 57.23/57.40      inference('demod', [status(thm)], ['28', '29'])).
% 57.23/57.40  thf('55', plain,
% 57.23/57.40      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 57.23/57.40        | ~ (l1_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['53', '54'])).
% 57.23/57.40  thf('56', plain, ((l1_struct_0 @ sk_B)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('57', plain,
% 57.23/57.40      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('demod', [status(thm)], ['55', '56'])).
% 57.23/57.40  thf('58', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['2', '3'])).
% 57.23/57.40  thf('59', plain,
% 57.23/57.40      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['57', '58'])).
% 57.23/57.40  thf('60', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('61', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('62', plain,
% 57.23/57.40      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 57.23/57.40         = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('63', plain,
% 57.23/57.40      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 57.23/57.40          = (k2_struct_0 @ sk_B))
% 57.23/57.40        | ~ (l1_struct_0 @ sk_A))),
% 57.23/57.40      inference('sup+', [status(thm)], ['61', '62'])).
% 57.23/57.40  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('65', plain,
% 57.23/57.40      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 57.23/57.40         = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('demod', [status(thm)], ['63', '64'])).
% 57.23/57.40  thf('66', plain,
% 57.23/57.40      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 57.23/57.40          = (k2_struct_0 @ sk_B))
% 57.23/57.40        | ~ (l1_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['60', '65'])).
% 57.23/57.40  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('68', plain,
% 57.23/57.40      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 57.23/57.40         = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('demod', [status(thm)], ['66', '67'])).
% 57.23/57.40  thf('69', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['2', '3'])).
% 57.23/57.40  thf('70', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['2', '3'])).
% 57.23/57.40  thf('71', plain,
% 57.23/57.40      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 57.23/57.40         = (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['68', '69', '70'])).
% 57.23/57.40  thf('72', plain, ((v2_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('73', plain,
% 57.23/57.40      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 57.23/57.40         (k1_zfmisc_1 @ 
% 57.23/57.40          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 57.23/57.40        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 57.23/57.40      inference('demod', [status(thm)], ['51', '52', '59', '71', '72'])).
% 57.23/57.40  thf('74', plain,
% 57.23/57.40      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 57.23/57.40      inference('simplify', [status(thm)], ['73'])).
% 57.23/57.40  thf(cc2_relat_1, axiom,
% 57.23/57.40    (![A:$i]:
% 57.23/57.40     ( ( v1_relat_1 @ A ) =>
% 57.23/57.40       ( ![B:$i]:
% 57.23/57.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 57.23/57.40  thf('75', plain,
% 57.23/57.40      (![X0 : $i, X1 : $i]:
% 57.23/57.40         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 57.23/57.40          | (v1_relat_1 @ X0)
% 57.23/57.40          | ~ (v1_relat_1 @ X1))),
% 57.23/57.40      inference('cnf', [status(esa)], [cc2_relat_1])).
% 57.23/57.40  thf('76', plain,
% 57.23/57.40      ((~ (v1_relat_1 @ 
% 57.23/57.40           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A)))
% 57.23/57.40        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['74', '75'])).
% 57.23/57.40  thf(fc6_relat_1, axiom,
% 57.23/57.40    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 57.23/57.40  thf('77', plain,
% 57.23/57.40      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 57.23/57.40      inference('cnf', [status(esa)], [fc6_relat_1])).
% 57.23/57.40  thf('78', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['76', '77'])).
% 57.23/57.40  thf('79', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 57.23/57.40      inference('demod', [status(thm)], ['47', '48'])).
% 57.23/57.40  thf('80', plain,
% 57.23/57.40      (![X28 : $i, X29 : $i, X30 : $i]:
% 57.23/57.40         (~ (v2_funct_1 @ X28)
% 57.23/57.40          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 57.23/57.40          | (v1_funct_1 @ (k2_funct_1 @ X28))
% 57.23/57.40          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 57.23/57.40          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 57.23/57.40          | ~ (v1_funct_1 @ X28))),
% 57.23/57.40      inference('cnf', [status(esa)], [t31_funct_2])).
% 57.23/57.40  thf('81', plain,
% 57.23/57.40      ((~ (v1_funct_1 @ sk_C)
% 57.23/57.40        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 57.23/57.40        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 57.23/57.40            != (k2_relat_1 @ sk_C))
% 57.23/57.40        | ~ (v2_funct_1 @ sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['79', '80'])).
% 57.23/57.40  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('83', plain,
% 57.23/57.40      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['57', '58'])).
% 57.23/57.40  thf('84', plain,
% 57.23/57.40      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 57.23/57.40         = (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['68', '69', '70'])).
% 57.23/57.40  thf('85', plain, ((v2_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('86', plain,
% 57.23/57.40      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 57.23/57.40      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 57.23/57.40  thf('87', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 57.23/57.40      inference('simplify', [status(thm)], ['86'])).
% 57.23/57.40  thf('88', plain,
% 57.23/57.40      (![X9 : $i]:
% 57.23/57.40         (~ (v2_funct_1 @ X9)
% 57.23/57.40          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 57.23/57.40          | ~ (v1_funct_1 @ X9)
% 57.23/57.40          | ~ (v1_relat_1 @ X9))),
% 57.23/57.40      inference('cnf', [status(esa)], [t55_funct_1])).
% 57.23/57.40  thf('89', plain,
% 57.23/57.40      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 57.23/57.40      inference('simplify', [status(thm)], ['73'])).
% 57.23/57.40  thf(cc2_relset_1, axiom,
% 57.23/57.40    (![A:$i,B:$i,C:$i]:
% 57.23/57.40     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 57.23/57.40       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 57.23/57.40  thf('90', plain,
% 57.23/57.40      (![X12 : $i, X13 : $i, X14 : $i]:
% 57.23/57.40         ((v4_relat_1 @ X12 @ X13)
% 57.23/57.40          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 57.23/57.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 57.23/57.40  thf('91', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['89', '90'])).
% 57.23/57.40  thf('92', plain,
% 57.23/57.40      (![X9 : $i]:
% 57.23/57.40         (~ (v2_funct_1 @ X9)
% 57.23/57.40          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 57.23/57.40          | ~ (v1_funct_1 @ X9)
% 57.23/57.40          | ~ (v1_relat_1 @ X9))),
% 57.23/57.40      inference('cnf', [status(esa)], [t55_funct_1])).
% 57.23/57.40  thf(d4_partfun1, axiom,
% 57.23/57.40    (![A:$i,B:$i]:
% 57.23/57.40     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 57.23/57.40       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 57.23/57.40  thf('93', plain,
% 57.23/57.40      (![X21 : $i, X22 : $i]:
% 57.23/57.40         (((k1_relat_1 @ X22) != (X21))
% 57.23/57.40          | (v1_partfun1 @ X22 @ X21)
% 57.23/57.40          | ~ (v4_relat_1 @ X22 @ X21)
% 57.23/57.40          | ~ (v1_relat_1 @ X22))),
% 57.23/57.40      inference('cnf', [status(esa)], [d4_partfun1])).
% 57.23/57.40  thf('94', plain,
% 57.23/57.40      (![X22 : $i]:
% 57.23/57.40         (~ (v1_relat_1 @ X22)
% 57.23/57.40          | ~ (v4_relat_1 @ X22 @ (k1_relat_1 @ X22))
% 57.23/57.40          | (v1_partfun1 @ X22 @ (k1_relat_1 @ X22)))),
% 57.23/57.40      inference('simplify', [status(thm)], ['93'])).
% 57.23/57.40  thf('95', plain,
% 57.23/57.40      (![X0 : $i]:
% 57.23/57.40         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 57.23/57.40          | ~ (v1_relat_1 @ X0)
% 57.23/57.40          | ~ (v1_funct_1 @ X0)
% 57.23/57.40          | ~ (v2_funct_1 @ X0)
% 57.23/57.40          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 57.23/57.40          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['92', '94'])).
% 57.23/57.40  thf('96', plain,
% 57.23/57.40      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 57.23/57.40           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 57.23/57.40        | ~ (v2_funct_1 @ sk_C)
% 57.23/57.40        | ~ (v1_funct_1 @ sk_C)
% 57.23/57.40        | ~ (v1_relat_1 @ sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['91', '95'])).
% 57.23/57.40  thf('97', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['76', '77'])).
% 57.23/57.40  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('100', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('101', plain,
% 57.23/57.40      (![X0 : $i, X1 : $i]:
% 57.23/57.40         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 57.23/57.40          | (v1_relat_1 @ X0)
% 57.23/57.40          | ~ (v1_relat_1 @ X1))),
% 57.23/57.40      inference('cnf', [status(esa)], [cc2_relat_1])).
% 57.23/57.40  thf('102', plain,
% 57.23/57.40      ((~ (v1_relat_1 @ 
% 57.23/57.40           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 57.23/57.40        | (v1_relat_1 @ sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['100', '101'])).
% 57.23/57.40  thf('103', plain,
% 57.23/57.40      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 57.23/57.40      inference('cnf', [status(esa)], [fc6_relat_1])).
% 57.23/57.40  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 57.23/57.40      inference('demod', [status(thm)], ['102', '103'])).
% 57.23/57.40  thf('105', plain,
% 57.23/57.40      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 57.23/57.40      inference('demod', [status(thm)], ['96', '97', '98', '99', '104'])).
% 57.23/57.40  thf('106', plain,
% 57.23/57.40      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 57.23/57.40        | ~ (v1_relat_1 @ sk_C)
% 57.23/57.40        | ~ (v1_funct_1 @ sk_C)
% 57.23/57.40        | ~ (v2_funct_1 @ sk_C))),
% 57.23/57.40      inference('sup+', [status(thm)], ['88', '105'])).
% 57.23/57.40  thf('107', plain, ((v1_relat_1 @ sk_C)),
% 57.23/57.40      inference('demod', [status(thm)], ['102', '103'])).
% 57.23/57.40  thf('108', plain, ((v1_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('109', plain, ((v2_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('110', plain,
% 57.23/57.40      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 57.23/57.40  thf('111', plain,
% 57.23/57.40      (![X21 : $i, X22 : $i]:
% 57.23/57.40         (~ (v1_partfun1 @ X22 @ X21)
% 57.23/57.40          | ((k1_relat_1 @ X22) = (X21))
% 57.23/57.40          | ~ (v4_relat_1 @ X22 @ X21)
% 57.23/57.40          | ~ (v1_relat_1 @ X22))),
% 57.23/57.40      inference('cnf', [status(esa)], [d4_partfun1])).
% 57.23/57.40  thf('112', plain,
% 57.23/57.40      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 57.23/57.40        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['110', '111'])).
% 57.23/57.40  thf('113', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['76', '77'])).
% 57.23/57.40  thf('114', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['89', '90'])).
% 57.23/57.40  thf('115', plain,
% 57.23/57.40      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['112', '113', '114'])).
% 57.23/57.40  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('117', plain, ((v1_relat_1 @ sk_C)),
% 57.23/57.40      inference('demod', [status(thm)], ['102', '103'])).
% 57.23/57.40  thf('118', plain,
% 57.23/57.40      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 57.23/57.40        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 57.23/57.40      inference('demod', [status(thm)],
% 57.23/57.40                ['39', '42', '78', '87', '115', '116', '117'])).
% 57.23/57.40  thf('119', plain,
% 57.23/57.40      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('simplify', [status(thm)], ['118'])).
% 57.23/57.40  thf('120', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('121', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('demod', [status(thm)], ['17', '18'])).
% 57.23/57.40  thf('122', plain,
% 57.23/57.40      (![X31 : $i, X32 : $i, X33 : $i]:
% 57.23/57.40         (((X31) = (k1_xboole_0))
% 57.23/57.40          | ~ (v1_funct_1 @ X32)
% 57.23/57.40          | ~ (v1_funct_2 @ X32 @ X33 @ X31)
% 57.23/57.40          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 57.23/57.40          | ((k5_relat_1 @ (k2_funct_1 @ X32) @ X32) = (k6_partfun1 @ X31))
% 57.23/57.40          | ~ (v2_funct_1 @ X32)
% 57.23/57.40          | ((k2_relset_1 @ X33 @ X31 @ X32) != (X31)))),
% 57.23/57.40      inference('cnf', [status(esa)], [t35_funct_2])).
% 57.23/57.40  thf('123', plain,
% 57.23/57.40      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 57.23/57.40          != (u1_struct_0 @ sk_B))
% 57.23/57.40        | ~ (v2_funct_1 @ sk_C)
% 57.23/57.40        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 57.23/57.40            = (k6_partfun1 @ (u1_struct_0 @ sk_B)))
% 57.23/57.40        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 57.23/57.40        | ~ (v1_funct_1 @ sk_C)
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['121', '122'])).
% 57.23/57.40  thf('124', plain,
% 57.23/57.40      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 57.23/57.40         = (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['22', '23'])).
% 57.23/57.40  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('126', plain,
% 57.23/57.40      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 57.23/57.40      inference('demod', [status(thm)], ['28', '29'])).
% 57.23/57.40  thf('127', plain, ((v1_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('128', plain,
% 57.23/57.40      ((((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B))
% 57.23/57.40        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 57.23/57.40            = (k6_partfun1 @ (u1_struct_0 @ sk_B)))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 57.23/57.40  thf('129', plain,
% 57.23/57.40      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 57.23/57.40        | ~ (l1_struct_0 @ sk_B)
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 57.23/57.40            = (k6_partfun1 @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('sup-', [status(thm)], ['120', '128'])).
% 57.23/57.40  thf('130', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['2', '3'])).
% 57.23/57.40  thf('131', plain, ((l1_struct_0 @ sk_B)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('132', plain,
% 57.23/57.40      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 57.23/57.40            = (k6_partfun1 @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('demod', [status(thm)], ['129', '130', '131'])).
% 57.23/57.40  thf('133', plain,
% 57.23/57.40      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 57.23/57.40          = (k6_partfun1 @ (u1_struct_0 @ sk_B)))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('simplify', [status(thm)], ['132'])).
% 57.23/57.40  thf(t63_funct_1, axiom,
% 57.23/57.40    (![A:$i]:
% 57.23/57.40     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 57.23/57.40       ( ![B:$i]:
% 57.23/57.40         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 57.23/57.40           ( ( ( v2_funct_1 @ A ) & 
% 57.23/57.40               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 57.23/57.40               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 57.23/57.40             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 57.23/57.40  thf('134', plain,
% 57.23/57.40      (![X10 : $i, X11 : $i]:
% 57.23/57.40         (~ (v1_relat_1 @ X10)
% 57.23/57.40          | ~ (v1_funct_1 @ X10)
% 57.23/57.40          | ((X10) = (k2_funct_1 @ X11))
% 57.23/57.40          | ((k5_relat_1 @ X11 @ X10) != (k6_relat_1 @ (k1_relat_1 @ X11)))
% 57.23/57.40          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X10))
% 57.23/57.40          | ~ (v2_funct_1 @ X11)
% 57.23/57.40          | ~ (v1_funct_1 @ X11)
% 57.23/57.40          | ~ (v1_relat_1 @ X11))),
% 57.23/57.40      inference('cnf', [status(esa)], [t63_funct_1])).
% 57.23/57.40  thf('135', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 57.23/57.40      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 57.23/57.40  thf('136', plain,
% 57.23/57.40      (![X10 : $i, X11 : $i]:
% 57.23/57.40         (~ (v1_relat_1 @ X10)
% 57.23/57.40          | ~ (v1_funct_1 @ X10)
% 57.23/57.40          | ((X10) = (k2_funct_1 @ X11))
% 57.23/57.40          | ((k5_relat_1 @ X11 @ X10) != (k6_partfun1 @ (k1_relat_1 @ X11)))
% 57.23/57.40          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X10))
% 57.23/57.40          | ~ (v2_funct_1 @ X11)
% 57.23/57.40          | ~ (v1_funct_1 @ X11)
% 57.23/57.40          | ~ (v1_relat_1 @ X11))),
% 57.23/57.40      inference('demod', [status(thm)], ['134', '135'])).
% 57.23/57.40  thf('137', plain,
% 57.23/57.40      ((((k6_partfun1 @ (u1_struct_0 @ sk_B))
% 57.23/57.40          != (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 57.23/57.40        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 57.23/57.40        | ~ (v1_funct_1 @ sk_C)
% 57.23/57.40        | ~ (v1_relat_1 @ sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['133', '136'])).
% 57.23/57.40  thf('138', plain,
% 57.23/57.40      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['112', '113', '114'])).
% 57.23/57.40  thf('139', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['76', '77'])).
% 57.23/57.40  thf('140', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 57.23/57.40      inference('simplify', [status(thm)], ['86'])).
% 57.23/57.40  thf('141', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('142', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('143', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('144', plain,
% 57.23/57.40      (((m1_subset_1 @ sk_C @ 
% 57.23/57.40         (k1_zfmisc_1 @ 
% 57.23/57.40          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 57.23/57.40        | ~ (l1_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['142', '143'])).
% 57.23/57.40  thf('145', plain, ((l1_struct_0 @ sk_B)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('146', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 57.23/57.40      inference('demod', [status(thm)], ['144', '145'])).
% 57.23/57.40  thf('147', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['2', '3'])).
% 57.23/57.40  thf('148', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 57.23/57.40      inference('demod', [status(thm)], ['146', '147'])).
% 57.23/57.40  thf(cc5_funct_2, axiom,
% 57.23/57.40    (![A:$i,B:$i]:
% 57.23/57.40     ( ( ~( v1_xboole_0 @ B ) ) =>
% 57.23/57.40       ( ![C:$i]:
% 57.23/57.40         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 57.23/57.40           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 57.23/57.40             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 57.23/57.40  thf('149', plain,
% 57.23/57.40      (![X18 : $i, X19 : $i, X20 : $i]:
% 57.23/57.40         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 57.23/57.40          | (v1_partfun1 @ X18 @ X19)
% 57.23/57.40          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 57.23/57.40          | ~ (v1_funct_1 @ X18)
% 57.23/57.40          | (v1_xboole_0 @ X20))),
% 57.23/57.40      inference('cnf', [status(esa)], [cc5_funct_2])).
% 57.23/57.40  thf('150', plain,
% 57.23/57.40      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 57.23/57.40        | ~ (v1_funct_1 @ sk_C)
% 57.23/57.40        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 57.23/57.40        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['148', '149'])).
% 57.23/57.40  thf('151', plain, ((v1_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('152', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('153', plain,
% 57.23/57.40      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('154', plain,
% 57.23/57.40      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 57.23/57.40        | ~ (l1_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['152', '153'])).
% 57.23/57.40  thf('155', plain, ((l1_struct_0 @ sk_B)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('156', plain,
% 57.23/57.40      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('demod', [status(thm)], ['154', '155'])).
% 57.23/57.40  thf('157', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['2', '3'])).
% 57.23/57.40  thf('158', plain,
% 57.23/57.40      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['156', '157'])).
% 57.23/57.40  thf('159', plain,
% 57.23/57.40      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 57.23/57.40        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 57.23/57.40      inference('demod', [status(thm)], ['150', '151', '158'])).
% 57.23/57.40  thf('160', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('clc', [status(thm)], ['8', '9'])).
% 57.23/57.40  thf('161', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 57.23/57.40      inference('clc', [status(thm)], ['159', '160'])).
% 57.23/57.40  thf('162', plain,
% 57.23/57.40      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 57.23/57.40      inference('sup+', [status(thm)], ['141', '161'])).
% 57.23/57.40  thf('163', plain, ((l1_struct_0 @ sk_A)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('164', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 57.23/57.40      inference('demod', [status(thm)], ['162', '163'])).
% 57.23/57.40  thf('165', plain,
% 57.23/57.40      (![X21 : $i, X22 : $i]:
% 57.23/57.40         (~ (v1_partfun1 @ X22 @ X21)
% 57.23/57.40          | ((k1_relat_1 @ X22) = (X21))
% 57.23/57.40          | ~ (v4_relat_1 @ X22 @ X21)
% 57.23/57.40          | ~ (v1_relat_1 @ X22))),
% 57.23/57.40      inference('cnf', [status(esa)], [d4_partfun1])).
% 57.23/57.40  thf('166', plain,
% 57.23/57.40      ((~ (v1_relat_1 @ sk_C)
% 57.23/57.40        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 57.23/57.40        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['164', '165'])).
% 57.23/57.40  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 57.23/57.40      inference('demod', [status(thm)], ['102', '103'])).
% 57.23/57.40  thf('168', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('demod', [status(thm)], ['17', '18'])).
% 57.23/57.40  thf('169', plain,
% 57.23/57.40      (![X12 : $i, X13 : $i, X14 : $i]:
% 57.23/57.40         ((v4_relat_1 @ X12 @ X13)
% 57.23/57.40          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 57.23/57.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 57.23/57.40  thf('170', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 57.23/57.40      inference('sup-', [status(thm)], ['168', '169'])).
% 57.23/57.40  thf('171', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 57.23/57.40      inference('demod', [status(thm)], ['166', '167', '170'])).
% 57.23/57.40  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('173', plain, ((v1_relat_1 @ sk_C)),
% 57.23/57.40      inference('demod', [status(thm)], ['102', '103'])).
% 57.23/57.40  thf('174', plain,
% 57.23/57.40      ((((k6_partfun1 @ (u1_struct_0 @ sk_B))
% 57.23/57.40          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 57.23/57.40        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 57.23/57.40      inference('demod', [status(thm)],
% 57.23/57.40                ['137', '138', '139', '140', '171', '172', '173'])).
% 57.23/57.40  thf('175', plain,
% 57.23/57.40      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 57.23/57.40        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ((k6_partfun1 @ (u1_struct_0 @ sk_B))
% 57.23/57.40            != (k6_partfun1 @ (k2_relat_1 @ sk_C))))),
% 57.23/57.40      inference('sup-', [status(thm)], ['119', '174'])).
% 57.23/57.40  thf('176', plain,
% 57.23/57.40      ((((k6_partfun1 @ (u1_struct_0 @ sk_B))
% 57.23/57.40          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 57.23/57.40        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 57.23/57.40        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('simplify', [status(thm)], ['175'])).
% 57.23/57.40  thf('177', plain,
% 57.23/57.40      ((((k6_partfun1 @ (k2_struct_0 @ sk_B))
% 57.23/57.40          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 57.23/57.40        | ~ (l1_struct_0 @ sk_B)
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 57.23/57.40        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['13', '176'])).
% 57.23/57.40  thf('178', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['2', '3'])).
% 57.23/57.40  thf('179', plain, ((l1_struct_0 @ sk_B)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('180', plain,
% 57.23/57.40      ((((k6_partfun1 @ (k2_relat_1 @ sk_C))
% 57.23/57.40          != (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 57.23/57.40        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 57.23/57.40      inference('demod', [status(thm)], ['177', '178', '179'])).
% 57.23/57.40  thf('181', plain,
% 57.23/57.40      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 57.23/57.40        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('simplify', [status(thm)], ['180'])).
% 57.23/57.40  thf('182', plain,
% 57.23/57.40      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 57.23/57.40        | ~ (v1_relat_1 @ sk_C)
% 57.23/57.40        | ~ (v1_funct_1 @ sk_C)
% 57.23/57.40        | ~ (v2_funct_1 @ sk_C)
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 57.23/57.40      inference('sup-', [status(thm)], ['12', '181'])).
% 57.23/57.40  thf('183', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 57.23/57.40      inference('demod', [status(thm)], ['166', '167', '170'])).
% 57.23/57.40  thf('184', plain, ((v1_relat_1 @ sk_C)),
% 57.23/57.40      inference('demod', [status(thm)], ['102', '103'])).
% 57.23/57.40  thf('185', plain, ((v1_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('186', plain, ((v2_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('187', plain,
% 57.23/57.40      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 57.23/57.40      inference('demod', [status(thm)], ['182', '183', '184', '185', '186'])).
% 57.23/57.40  thf('188', plain,
% 57.23/57.40      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('simplify', [status(thm)], ['187'])).
% 57.23/57.40  thf('189', plain,
% 57.23/57.40      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('simplify', [status(thm)], ['118'])).
% 57.23/57.40  thf('190', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('191', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('demod', [status(thm)], ['17', '18'])).
% 57.23/57.40  thf('192', plain,
% 57.23/57.40      (![X28 : $i, X29 : $i, X30 : $i]:
% 57.23/57.40         (~ (v2_funct_1 @ X28)
% 57.23/57.40          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 57.23/57.40          | (m1_subset_1 @ (k2_funct_1 @ X28) @ 
% 57.23/57.40             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 57.23/57.40          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 57.23/57.40          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 57.23/57.40          | ~ (v1_funct_1 @ X28))),
% 57.23/57.40      inference('cnf', [status(esa)], [t31_funct_2])).
% 57.23/57.40  thf('193', plain,
% 57.23/57.40      ((~ (v1_funct_1 @ sk_C)
% 57.23/57.40        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 57.23/57.40        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 57.23/57.40           (k1_zfmisc_1 @ 
% 57.23/57.40            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 57.23/57.40        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 57.23/57.40            != (u1_struct_0 @ sk_B))
% 57.23/57.40        | ~ (v2_funct_1 @ sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['191', '192'])).
% 57.23/57.40  thf('194', plain, ((v1_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('195', plain,
% 57.23/57.40      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 57.23/57.40      inference('demod', [status(thm)], ['28', '29'])).
% 57.23/57.40  thf('196', plain,
% 57.23/57.40      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 57.23/57.40         = (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['22', '23'])).
% 57.23/57.40  thf('197', plain, ((v2_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('198', plain,
% 57.23/57.40      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 57.23/57.40         (k1_zfmisc_1 @ 
% 57.23/57.40          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 57.23/57.40        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 57.23/57.40      inference('demod', [status(thm)], ['193', '194', '195', '196', '197'])).
% 57.23/57.40  thf('199', plain,
% 57.23/57.40      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 57.23/57.40        | ~ (l1_struct_0 @ sk_B)
% 57.23/57.40        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 57.23/57.40           (k1_zfmisc_1 @ 
% 57.23/57.40            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 57.23/57.40      inference('sup-', [status(thm)], ['190', '198'])).
% 57.23/57.40  thf('200', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['2', '3'])).
% 57.23/57.40  thf('201', plain, ((l1_struct_0 @ sk_B)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('202', plain,
% 57.23/57.40      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 57.23/57.40        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 57.23/57.40           (k1_zfmisc_1 @ 
% 57.23/57.40            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 57.23/57.40      inference('demod', [status(thm)], ['199', '200', '201'])).
% 57.23/57.40  thf('203', plain,
% 57.23/57.40      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 57.23/57.40      inference('simplify', [status(thm)], ['202'])).
% 57.23/57.40  thf(d4_tops_2, axiom,
% 57.23/57.40    (![A:$i,B:$i,C:$i]:
% 57.23/57.40     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 57.23/57.40         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 57.23/57.40       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 57.23/57.40         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 57.23/57.40  thf('204', plain,
% 57.23/57.40      (![X36 : $i, X37 : $i, X38 : $i]:
% 57.23/57.40         (((k2_relset_1 @ X37 @ X36 @ X38) != (X36))
% 57.23/57.40          | ~ (v2_funct_1 @ X38)
% 57.23/57.40          | ((k2_tops_2 @ X37 @ X36 @ X38) = (k2_funct_1 @ X38))
% 57.23/57.40          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 57.23/57.40          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 57.23/57.40          | ~ (v1_funct_1 @ X38))),
% 57.23/57.40      inference('cnf', [status(esa)], [d4_tops_2])).
% 57.23/57.40  thf('205', plain,
% 57.23/57.40      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 57.23/57.40             (k2_struct_0 @ sk_A))
% 57.23/57.40        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 57.23/57.40            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 57.23/57.40        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 57.23/57.40            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['203', '204'])).
% 57.23/57.40  thf('206', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 57.23/57.40      inference('simplify', [status(thm)], ['86'])).
% 57.23/57.40  thf('207', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('208', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('demod', [status(thm)], ['17', '18'])).
% 57.23/57.40  thf('209', plain,
% 57.23/57.40      (![X28 : $i, X29 : $i, X30 : $i]:
% 57.23/57.40         (~ (v2_funct_1 @ X28)
% 57.23/57.40          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 57.23/57.40          | (v1_funct_2 @ (k2_funct_1 @ X28) @ X29 @ X30)
% 57.23/57.40          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 57.23/57.40          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 57.23/57.40          | ~ (v1_funct_1 @ X28))),
% 57.23/57.40      inference('cnf', [status(esa)], [t31_funct_2])).
% 57.23/57.40  thf('210', plain,
% 57.23/57.40      ((~ (v1_funct_1 @ sk_C)
% 57.23/57.40        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 57.23/57.40        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 57.23/57.40           (k2_struct_0 @ sk_A))
% 57.23/57.40        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 57.23/57.40            != (u1_struct_0 @ sk_B))
% 57.23/57.40        | ~ (v2_funct_1 @ sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['208', '209'])).
% 57.23/57.40  thf('211', plain, ((v1_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('212', plain,
% 57.23/57.40      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 57.23/57.40      inference('demod', [status(thm)], ['28', '29'])).
% 57.23/57.40  thf('213', plain,
% 57.23/57.40      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 57.23/57.40         = (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['22', '23'])).
% 57.23/57.40  thf('214', plain, ((v2_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('215', plain,
% 57.23/57.40      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 57.23/57.40         (k2_struct_0 @ sk_A))
% 57.23/57.40        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 57.23/57.40      inference('demod', [status(thm)], ['210', '211', '212', '213', '214'])).
% 57.23/57.40  thf('216', plain,
% 57.23/57.40      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 57.23/57.40        | ~ (l1_struct_0 @ sk_B)
% 57.23/57.40        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 57.23/57.40           (k2_struct_0 @ sk_A)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['207', '215'])).
% 57.23/57.40  thf('217', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['2', '3'])).
% 57.23/57.40  thf('218', plain, ((l1_struct_0 @ sk_B)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('219', plain,
% 57.23/57.40      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 57.23/57.40        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 57.23/57.40           (k2_struct_0 @ sk_A)))),
% 57.23/57.40      inference('demod', [status(thm)], ['216', '217', '218'])).
% 57.23/57.40  thf('220', plain,
% 57.23/57.40      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 57.23/57.40        (k2_struct_0 @ sk_A))),
% 57.23/57.40      inference('simplify', [status(thm)], ['219'])).
% 57.23/57.40  thf('221', plain,
% 57.23/57.40      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 57.23/57.40      inference('simplify', [status(thm)], ['202'])).
% 57.23/57.40  thf('222', plain,
% 57.23/57.40      (![X15 : $i, X16 : $i, X17 : $i]:
% 57.23/57.40         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 57.23/57.40          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 57.23/57.40      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 57.23/57.40  thf('223', plain,
% 57.23/57.40      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 57.23/57.40         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['221', '222'])).
% 57.23/57.40  thf('224', plain,
% 57.23/57.40      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 57.23/57.40          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 57.23/57.40        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 57.23/57.40      inference('demod', [status(thm)], ['205', '206', '220', '223'])).
% 57.23/57.40  thf('225', plain,
% 57.23/57.40      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 57.23/57.40        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 57.23/57.40            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 57.23/57.40      inference('sup-', [status(thm)], ['189', '224'])).
% 57.23/57.40  thf('226', plain,
% 57.23/57.40      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('simplify', [status(thm)], ['187'])).
% 57.23/57.40  thf('227', plain,
% 57.23/57.40      (![X9 : $i]:
% 57.23/57.40         (~ (v2_funct_1 @ X9)
% 57.23/57.40          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 57.23/57.40          | ~ (v1_funct_1 @ X9)
% 57.23/57.40          | ~ (v1_relat_1 @ X9))),
% 57.23/57.40      inference('cnf', [status(esa)], [t55_funct_1])).
% 57.23/57.40  thf('228', plain,
% 57.23/57.40      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 57.23/57.40      inference('sup+', [status(thm)], ['226', '227'])).
% 57.23/57.40  thf('229', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 57.23/57.40      inference('demod', [status(thm)], ['166', '167', '170'])).
% 57.23/57.40  thf('230', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['76', '77'])).
% 57.23/57.40  thf('231', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 57.23/57.40      inference('simplify', [status(thm)], ['86'])).
% 57.23/57.40  thf('232', plain,
% 57.23/57.40      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 57.23/57.40      inference('demod', [status(thm)], ['228', '229', '230', '231'])).
% 57.23/57.40  thf('233', plain,
% 57.23/57.40      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('simplify', [status(thm)], ['118'])).
% 57.23/57.40  thf('234', plain,
% 57.23/57.40      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 57.23/57.40      inference('clc', [status(thm)], ['232', '233'])).
% 57.23/57.40  thf('235', plain,
% 57.23/57.40      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 57.23/57.40          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('clc', [status(thm)], ['225', '234'])).
% 57.23/57.40  thf('236', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('237', plain,
% 57.23/57.40      (![X34 : $i]:
% 57.23/57.40         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 57.23/57.40      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.23/57.40  thf('238', plain,
% 57.23/57.40      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 57.23/57.40          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 57.23/57.40           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 57.23/57.40          sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('239', plain,
% 57.23/57.40      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 57.23/57.40           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 57.23/57.40            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 57.23/57.40           sk_C)
% 57.23/57.40        | ~ (l1_struct_0 @ sk_A))),
% 57.23/57.40      inference('sup-', [status(thm)], ['237', '238'])).
% 57.23/57.40  thf('240', plain, ((l1_struct_0 @ sk_A)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('241', plain,
% 57.23/57.40      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 57.23/57.40          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 57.23/57.40           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 57.23/57.40          sk_C)),
% 57.23/57.40      inference('demod', [status(thm)], ['239', '240'])).
% 57.23/57.40  thf('242', plain,
% 57.23/57.40      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 57.23/57.40           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 57.23/57.40            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 57.23/57.40           sk_C)
% 57.23/57.40        | ~ (l1_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup-', [status(thm)], ['236', '241'])).
% 57.23/57.40  thf('243', plain, ((l1_struct_0 @ sk_B)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('244', plain,
% 57.23/57.40      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 57.23/57.40          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 57.23/57.40           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 57.23/57.40          sk_C)),
% 57.23/57.40      inference('demod', [status(thm)], ['242', '243'])).
% 57.23/57.40  thf('245', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 57.23/57.40      inference('clc', [status(thm)], ['159', '160'])).
% 57.23/57.40  thf('246', plain,
% 57.23/57.40      (![X21 : $i, X22 : $i]:
% 57.23/57.40         (~ (v1_partfun1 @ X22 @ X21)
% 57.23/57.40          | ((k1_relat_1 @ X22) = (X21))
% 57.23/57.40          | ~ (v4_relat_1 @ X22 @ X21)
% 57.23/57.40          | ~ (v1_relat_1 @ X22))),
% 57.23/57.40      inference('cnf', [status(esa)], [d4_partfun1])).
% 57.23/57.40  thf('247', plain,
% 57.23/57.40      ((~ (v1_relat_1 @ sk_C)
% 57.23/57.40        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 57.23/57.40        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['245', '246'])).
% 57.23/57.40  thf('248', plain, ((v1_relat_1 @ sk_C)),
% 57.23/57.40      inference('demod', [status(thm)], ['102', '103'])).
% 57.23/57.40  thf('249', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('250', plain,
% 57.23/57.40      (![X12 : $i, X13 : $i, X14 : $i]:
% 57.23/57.40         ((v4_relat_1 @ X12 @ X13)
% 57.23/57.40          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 57.23/57.40      inference('cnf', [status(esa)], [cc2_relset_1])).
% 57.23/57.40  thf('251', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 57.23/57.40      inference('sup-', [status(thm)], ['249', '250'])).
% 57.23/57.40  thf('252', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 57.23/57.40      inference('demod', [status(thm)], ['247', '248', '251'])).
% 57.23/57.40  thf('253', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 57.23/57.40      inference('demod', [status(thm)], ['166', '167', '170'])).
% 57.23/57.40  thf('254', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 57.23/57.40      inference('demod', [status(thm)], ['252', '253'])).
% 57.23/57.40  thf('255', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 57.23/57.40      inference('demod', [status(thm)], ['252', '253'])).
% 57.23/57.40  thf('256', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['2', '3'])).
% 57.23/57.40  thf('257', plain,
% 57.23/57.40      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 57.23/57.40          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 57.23/57.40           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 57.23/57.40          sk_C)),
% 57.23/57.40      inference('demod', [status(thm)], ['244', '254', '255', '256'])).
% 57.23/57.40  thf('258', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 57.23/57.40      inference('demod', [status(thm)], ['47', '48'])).
% 57.23/57.40  thf('259', plain,
% 57.23/57.40      (![X36 : $i, X37 : $i, X38 : $i]:
% 57.23/57.40         (((k2_relset_1 @ X37 @ X36 @ X38) != (X36))
% 57.23/57.40          | ~ (v2_funct_1 @ X38)
% 57.23/57.40          | ((k2_tops_2 @ X37 @ X36 @ X38) = (k2_funct_1 @ X38))
% 57.23/57.40          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 57.23/57.40          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 57.23/57.40          | ~ (v1_funct_1 @ X38))),
% 57.23/57.40      inference('cnf', [status(esa)], [d4_tops_2])).
% 57.23/57.40  thf('260', plain,
% 57.23/57.40      ((~ (v1_funct_1 @ sk_C)
% 57.23/57.40        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 57.23/57.40        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 57.23/57.40            = (k2_funct_1 @ sk_C))
% 57.23/57.40        | ~ (v2_funct_1 @ sk_C)
% 57.23/57.40        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 57.23/57.40            != (k2_relat_1 @ sk_C)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['258', '259'])).
% 57.23/57.40  thf('261', plain, ((v1_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('262', plain,
% 57.23/57.40      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['57', '58'])).
% 57.23/57.40  thf('263', plain, ((v2_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('264', plain,
% 57.23/57.40      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 57.23/57.40         = (k2_relat_1 @ sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['68', '69', '70'])).
% 57.23/57.40  thf('265', plain,
% 57.23/57.40      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 57.23/57.40          = (k2_funct_1 @ sk_C))
% 57.23/57.40        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 57.23/57.40      inference('demod', [status(thm)], ['260', '261', '262', '263', '264'])).
% 57.23/57.40  thf('266', plain,
% 57.23/57.40      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 57.23/57.40         = (k2_funct_1 @ sk_C))),
% 57.23/57.40      inference('simplify', [status(thm)], ['265'])).
% 57.23/57.40  thf('267', plain,
% 57.23/57.40      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 57.23/57.40          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 57.23/57.40           (k2_funct_1 @ sk_C)) @ 
% 57.23/57.40          sk_C)),
% 57.23/57.40      inference('demod', [status(thm)], ['257', '266'])).
% 57.23/57.40  thf('268', plain,
% 57.23/57.40      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 57.23/57.40           (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['235', '267'])).
% 57.23/57.40  thf('269', plain,
% 57.23/57.40      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 57.23/57.40           sk_C)
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['188', '268'])).
% 57.23/57.40  thf('270', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('demod', [status(thm)], ['17', '18'])).
% 57.23/57.40  thf('271', plain,
% 57.23/57.40      ((m1_subset_1 @ sk_C @ 
% 57.23/57.40        (k1_zfmisc_1 @ 
% 57.23/57.40         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 57.23/57.40      inference('demod', [status(thm)], ['17', '18'])).
% 57.23/57.40  thf(reflexivity_r2_funct_2, axiom,
% 57.23/57.40    (![A:$i,B:$i,C:$i,D:$i]:
% 57.23/57.40     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 57.23/57.40         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 57.23/57.40         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 57.23/57.40         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 57.23/57.40       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 57.23/57.40  thf('272', plain,
% 57.23/57.40      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 57.23/57.40         ((r2_funct_2 @ X24 @ X25 @ X26 @ X26)
% 57.23/57.40          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 57.23/57.40          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 57.23/57.40          | ~ (v1_funct_1 @ X26)
% 57.23/57.40          | ~ (v1_funct_1 @ X27)
% 57.23/57.40          | ~ (v1_funct_2 @ X27 @ X24 @ X25)
% 57.23/57.40          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 57.23/57.40      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 57.23/57.40  thf('273', plain,
% 57.23/57.40      (![X0 : $i]:
% 57.23/57.40         (~ (m1_subset_1 @ X0 @ 
% 57.23/57.40             (k1_zfmisc_1 @ 
% 57.23/57.40              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 57.23/57.40          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 57.23/57.40          | ~ (v1_funct_1 @ X0)
% 57.23/57.40          | ~ (v1_funct_1 @ sk_C)
% 57.23/57.40          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 57.23/57.40          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 57.23/57.40             sk_C))),
% 57.23/57.40      inference('sup-', [status(thm)], ['271', '272'])).
% 57.23/57.40  thf('274', plain, ((v1_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('275', plain,
% 57.23/57.40      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 57.23/57.40      inference('demod', [status(thm)], ['28', '29'])).
% 57.23/57.40  thf('276', plain,
% 57.23/57.40      (![X0 : $i]:
% 57.23/57.40         (~ (m1_subset_1 @ X0 @ 
% 57.23/57.40             (k1_zfmisc_1 @ 
% 57.23/57.40              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 57.23/57.40          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 57.23/57.40          | ~ (v1_funct_1 @ X0)
% 57.23/57.40          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 57.23/57.40             sk_C))),
% 57.23/57.40      inference('demod', [status(thm)], ['273', '274', '275'])).
% 57.23/57.40  thf('277', plain,
% 57.23/57.40      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 57.23/57.40        | ~ (v1_funct_1 @ sk_C)
% 57.23/57.40        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 57.23/57.40      inference('sup-', [status(thm)], ['270', '276'])).
% 57.23/57.40  thf('278', plain, ((v1_funct_1 @ sk_C)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('279', plain,
% 57.23/57.40      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 57.23/57.40      inference('demod', [status(thm)], ['28', '29'])).
% 57.23/57.40  thf('280', plain,
% 57.23/57.40      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 57.23/57.40      inference('demod', [status(thm)], ['277', '278', '279'])).
% 57.23/57.40  thf('281', plain,
% 57.23/57.40      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 57.23/57.40        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 57.23/57.40      inference('demod', [status(thm)], ['269', '280'])).
% 57.23/57.40  thf('282', plain, (((u1_struct_0 @ sk_B) = (k1_xboole_0))),
% 57.23/57.40      inference('simplify', [status(thm)], ['281'])).
% 57.23/57.40  thf('283', plain,
% 57.23/57.40      ((((k2_struct_0 @ sk_B) = (k1_xboole_0)) | ~ (l1_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['11', '282'])).
% 57.23/57.40  thf('284', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 57.23/57.40      inference('sup+', [status(thm)], ['2', '3'])).
% 57.23/57.40  thf('285', plain, ((l1_struct_0 @ sk_B)),
% 57.23/57.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.23/57.40  thf('286', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 57.23/57.40      inference('demod', [status(thm)], ['283', '284', '285'])).
% 57.23/57.40  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 57.23/57.40  thf('287', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 57.23/57.40      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 57.23/57.40  thf('288', plain, ($false),
% 57.23/57.40      inference('demod', [status(thm)], ['10', '286', '287'])).
% 57.23/57.40  
% 57.23/57.40  % SZS output end Refutation
% 57.23/57.40  
% 57.23/57.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
