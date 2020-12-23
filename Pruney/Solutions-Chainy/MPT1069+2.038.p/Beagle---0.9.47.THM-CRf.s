%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:50 EST 2020

% Result     : Theorem 6.29s
% Output     : CNFRefutation 6.59s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 473 expanded)
%              Number of leaves         :   46 ( 188 expanded)
%              Depth                    :   23
%              Number of atoms          :  274 (1674 expanded)
%              Number of equality atoms :   53 ( 381 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_64,plain,(
    m1_subset_1('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_68,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_66,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1495,plain,(
    ! [A_290,B_291,C_292] :
      ( k1_relset_1(A_290,B_291,C_292) = k1_relat_1(C_292)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1503,plain,(
    k1_relset_1('#skF_8','#skF_6','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_1495])).

tff(c_70,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1486,plain,(
    ! [A_287,B_288,C_289] :
      ( k2_relset_1(A_287,B_288,C_289) = k2_relat_1(C_289)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1493,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_1486])).

tff(c_62,plain,(
    r1_tarski(k2_relset_1('#skF_7','#skF_8','#skF_9'),k1_relset_1('#skF_8','#skF_6','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1505,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k1_relset_1('#skF_8','#skF_6','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1493,c_62])).

tff(c_1522,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_1505])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_74,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_72,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2698,plain,(
    ! [E_493,C_488,D_489,A_492,F_491,B_490] :
      ( k1_funct_1(k8_funct_2(B_490,C_488,A_492,D_489,E_493),F_491) = k1_funct_1(E_493,k1_funct_1(D_489,F_491))
      | k1_xboole_0 = B_490
      | ~ r1_tarski(k2_relset_1(B_490,C_488,D_489),k1_relset_1(C_488,A_492,E_493))
      | ~ m1_subset_1(F_491,B_490)
      | ~ m1_subset_1(E_493,k1_zfmisc_1(k2_zfmisc_1(C_488,A_492)))
      | ~ v1_funct_1(E_493)
      | ~ m1_subset_1(D_489,k1_zfmisc_1(k2_zfmisc_1(B_490,C_488)))
      | ~ v1_funct_2(D_489,B_490,C_488)
      | ~ v1_funct_1(D_489)
      | v1_xboole_0(C_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2706,plain,(
    ! [A_492,E_493,F_491] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8',A_492,'#skF_9',E_493),F_491) = k1_funct_1(E_493,k1_funct_1('#skF_9',F_491))
      | k1_xboole_0 = '#skF_7'
      | ~ r1_tarski(k2_relat_1('#skF_9'),k1_relset_1('#skF_8',A_492,E_493))
      | ~ m1_subset_1(F_491,'#skF_7')
      | ~ m1_subset_1(E_493,k1_zfmisc_1(k2_zfmisc_1('#skF_8',A_492)))
      | ~ v1_funct_1(E_493)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
      | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
      | ~ v1_funct_1('#skF_9')
      | v1_xboole_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1493,c_2698])).

tff(c_2716,plain,(
    ! [A_492,E_493,F_491] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8',A_492,'#skF_9',E_493),F_491) = k1_funct_1(E_493,k1_funct_1('#skF_9',F_491))
      | k1_xboole_0 = '#skF_7'
      | ~ r1_tarski(k2_relat_1('#skF_9'),k1_relset_1('#skF_8',A_492,E_493))
      | ~ m1_subset_1(F_491,'#skF_7')
      | ~ m1_subset_1(E_493,k1_zfmisc_1(k2_zfmisc_1('#skF_8',A_492)))
      | ~ v1_funct_1(E_493)
      | v1_xboole_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_2706])).

tff(c_2855,plain,(
    ! [A_496,E_497,F_498] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8',A_496,'#skF_9',E_497),F_498) = k1_funct_1(E_497,k1_funct_1('#skF_9',F_498))
      | ~ r1_tarski(k2_relat_1('#skF_9'),k1_relset_1('#skF_8',A_496,E_497))
      | ~ m1_subset_1(F_498,'#skF_7')
      | ~ m1_subset_1(E_497,k1_zfmisc_1(k2_zfmisc_1('#skF_8',A_496)))
      | ~ v1_funct_1(E_497) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_60,c_2716])).

tff(c_2857,plain,(
    ! [F_498] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),F_498) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',F_498))
      | ~ r1_tarski(k2_relat_1('#skF_9'),k1_relat_1('#skF_10'))
      | ~ m1_subset_1(F_498,'#skF_7')
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6')))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1503,c_2855])).

tff(c_2859,plain,(
    ! [F_498] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),F_498) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',F_498))
      | ~ m1_subset_1(F_498,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1522,c_2857])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [C_97,A_98,B_99] :
      ( v1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_90,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_83])).

tff(c_1502,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_1495])).

tff(c_1590,plain,(
    ! [B_316,A_317,C_318] :
      ( k1_xboole_0 = B_316
      | k1_relset_1(A_317,B_316,C_318) = A_317
      | ~ v1_funct_2(C_318,A_317,B_316)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_317,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1593,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_1590])).

tff(c_1599,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1502,c_1593])).

tff(c_1602,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1599])).

tff(c_1699,plain,(
    ! [A_344,B_345,C_346] :
      ( k7_partfun1(A_344,B_345,C_346) = k1_funct_1(B_345,C_346)
      | ~ r2_hidden(C_346,k1_relat_1(B_345))
      | ~ v1_funct_1(B_345)
      | ~ v5_relat_1(B_345,A_344)
      | ~ v1_relat_1(B_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1715,plain,(
    ! [A_344,C_346] :
      ( k7_partfun1(A_344,'#skF_9',C_346) = k1_funct_1('#skF_9',C_346)
      | ~ r2_hidden(C_346,'#skF_7')
      | ~ v1_funct_1('#skF_9')
      | ~ v5_relat_1('#skF_9',A_344)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1602,c_1699])).

tff(c_1759,plain,(
    ! [A_348,C_349] :
      ( k7_partfun1(A_348,'#skF_9',C_349) = k1_funct_1('#skF_9',C_349)
      | ~ r2_hidden(C_349,'#skF_7')
      | ~ v5_relat_1('#skF_9',A_348) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_74,c_1715])).

tff(c_1793,plain,(
    ! [A_348,A_7] :
      ( k7_partfun1(A_348,'#skF_9',A_7) = k1_funct_1('#skF_9',A_7)
      | ~ v5_relat_1('#skF_9',A_348)
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_7,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_12,c_1759])).

tff(c_1799,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1793])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1802,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1799,c_10])).

tff(c_1806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1802])).

tff(c_1808,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1793])).

tff(c_115,plain,(
    ! [C_110,B_111,A_112] :
      ( v5_relat_1(C_110,B_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_123,plain,(
    v5_relat_1('#skF_10','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_115])).

tff(c_91,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_83])).

tff(c_14,plain,(
    ! [A_9,D_48] :
      ( r2_hidden(k1_funct_1(A_9,D_48),k2_relat_1(A_9))
      | ~ r2_hidden(D_48,k1_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_99,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_1'(A_104,B_105),A_104)
      | r1_tarski(A_104,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_104,plain,(
    ! [A_104] : r1_tarski(A_104,A_104) ),
    inference(resolution,[status(thm)],[c_99,c_4])).

tff(c_1574,plain,(
    ! [A_312,C_313] :
      ( r2_hidden('#skF_5'(A_312,k2_relat_1(A_312),C_313),k1_relat_1(A_312))
      | ~ r2_hidden(C_313,k2_relat_1(A_312))
      | ~ v1_funct_1(A_312)
      | ~ v1_relat_1(A_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1577,plain,(
    ! [A_312,C_313,B_2] :
      ( r2_hidden('#skF_5'(A_312,k2_relat_1(A_312),C_313),B_2)
      | ~ r1_tarski(k1_relat_1(A_312),B_2)
      | ~ r2_hidden(C_313,k2_relat_1(A_312))
      | ~ v1_funct_1(A_312)
      | ~ v1_relat_1(A_312) ) ),
    inference(resolution,[status(thm)],[c_1574,c_2])).

tff(c_16,plain,(
    ! [A_9,C_45] :
      ( k1_funct_1(A_9,'#skF_5'(A_9,k2_relat_1(A_9),C_45)) = C_45
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1543,plain,(
    ! [A_297,D_298] :
      ( r2_hidden(k1_funct_1(A_297,D_298),k2_relat_1(A_297))
      | ~ r2_hidden(D_298,k1_relat_1(A_297))
      | ~ v1_funct_1(A_297)
      | ~ v1_relat_1(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1672,plain,(
    ! [A_336,D_337,B_338] :
      ( r2_hidden(k1_funct_1(A_336,D_337),B_338)
      | ~ r1_tarski(k2_relat_1(A_336),B_338)
      | ~ r2_hidden(D_337,k1_relat_1(A_336))
      | ~ v1_funct_1(A_336)
      | ~ v1_relat_1(A_336) ) ),
    inference(resolution,[status(thm)],[c_1543,c_2])).

tff(c_1994,plain,(
    ! [A_387,D_388,B_389,B_390] :
      ( r2_hidden(k1_funct_1(A_387,D_388),B_389)
      | ~ r1_tarski(B_390,B_389)
      | ~ r1_tarski(k2_relat_1(A_387),B_390)
      | ~ r2_hidden(D_388,k1_relat_1(A_387))
      | ~ v1_funct_1(A_387)
      | ~ v1_relat_1(A_387) ) ),
    inference(resolution,[status(thm)],[c_1672,c_2])).

tff(c_2001,plain,(
    ! [A_391,D_392] :
      ( r2_hidden(k1_funct_1(A_391,D_392),k1_relat_1('#skF_10'))
      | ~ r1_tarski(k2_relat_1(A_391),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_392,k1_relat_1(A_391))
      | ~ v1_funct_1(A_391)
      | ~ v1_relat_1(A_391) ) ),
    inference(resolution,[status(thm)],[c_1522,c_1994])).

tff(c_2658,plain,(
    ! [A_478,D_479,B_480] :
      ( r2_hidden(k1_funct_1(A_478,D_479),B_480)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_480)
      | ~ r1_tarski(k2_relat_1(A_478),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_479,k1_relat_1(A_478))
      | ~ v1_funct_1(A_478)
      | ~ v1_relat_1(A_478) ) ),
    inference(resolution,[status(thm)],[c_2001,c_2])).

tff(c_2661,plain,(
    ! [D_479,B_480] :
      ( r2_hidden(k1_funct_1('#skF_9',D_479),B_480)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_480)
      | ~ r2_hidden(D_479,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_104,c_2658])).

tff(c_2665,plain,(
    ! [D_481,B_482] :
      ( r2_hidden(k1_funct_1('#skF_9',D_481),B_482)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_482)
      | ~ r2_hidden(D_481,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_74,c_1602,c_2661])).

tff(c_2679,plain,(
    ! [C_45,B_482] :
      ( r2_hidden(C_45,B_482)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_482)
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_45),'#skF_7')
      | ~ r2_hidden(C_45,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2665])).

tff(c_2693,plain,(
    ! [C_486,B_487] :
      ( r2_hidden(C_486,B_487)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_487)
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_486),'#skF_7')
      | ~ r2_hidden(C_486,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_74,c_2679])).

tff(c_2718,plain,(
    ! [C_494] :
      ( r2_hidden(C_494,k1_relat_1('#skF_10'))
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_494),'#skF_7')
      | ~ r2_hidden(C_494,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_104,c_2693])).

tff(c_2722,plain,(
    ! [C_313] :
      ( r2_hidden(C_313,k1_relat_1('#skF_10'))
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7')
      | ~ r2_hidden(C_313,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1577,c_2718])).

tff(c_2743,plain,(
    ! [C_495] :
      ( r2_hidden(C_495,k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_495,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_74,c_104,c_1602,c_2722])).

tff(c_2815,plain,(
    ! [D_48] :
      ( r2_hidden(k1_funct_1('#skF_9',D_48),k1_relat_1('#skF_10'))
      | ~ r2_hidden(D_48,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_14,c_2743])).

tff(c_2860,plain,(
    ! [D_499] :
      ( r2_hidden(k1_funct_1('#skF_9',D_499),k1_relat_1('#skF_10'))
      | ~ r2_hidden(D_499,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_74,c_1602,c_2815])).

tff(c_54,plain,(
    ! [A_64,B_65,C_67] :
      ( k7_partfun1(A_64,B_65,C_67) = k1_funct_1(B_65,C_67)
      | ~ r2_hidden(C_67,k1_relat_1(B_65))
      | ~ v1_funct_1(B_65)
      | ~ v5_relat_1(B_65,A_64)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_2862,plain,(
    ! [A_64,D_499] :
      ( k7_partfun1(A_64,'#skF_10',k1_funct_1('#skF_9',D_499)) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',D_499))
      | ~ v1_funct_1('#skF_10')
      | ~ v5_relat_1('#skF_10',A_64)
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_499,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2860,c_54])).

tff(c_3056,plain,(
    ! [A_508,D_509] :
      ( k7_partfun1(A_508,'#skF_10',k1_funct_1('#skF_9',D_509)) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',D_509))
      | ~ v5_relat_1('#skF_10',A_508)
      | ~ r2_hidden(D_509,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_68,c_2862])).

tff(c_58,plain,(
    k7_partfun1('#skF_6','#skF_10',k1_funct_1('#skF_9','#skF_11')) != k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_3062,plain,
    ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') != k1_funct_1('#skF_10',k1_funct_1('#skF_9','#skF_11'))
    | ~ v5_relat_1('#skF_10','#skF_6')
    | ~ r2_hidden('#skF_11','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3056,c_58])).

tff(c_3076,plain,
    ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') != k1_funct_1('#skF_10',k1_funct_1('#skF_9','#skF_11'))
    | ~ r2_hidden('#skF_11','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_3062])).

tff(c_3086,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3076])).

tff(c_3089,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_3086])).

tff(c_3092,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3089])).

tff(c_3094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1808,c_3092])).

tff(c_3095,plain,(
    k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') != k1_funct_1('#skF_10',k1_funct_1('#skF_9','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_3076])).

tff(c_3149,plain,(
    ~ m1_subset_1('#skF_11','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2859,c_3095])).

tff(c_3153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3149])).

tff(c_3154,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1599])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3163,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3154,c_8])).

tff(c_3166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:16:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.29/2.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.29/2.24  
% 6.29/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.29/2.25  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 6.29/2.25  
% 6.29/2.25  %Foreground sorts:
% 6.29/2.25  
% 6.29/2.25  
% 6.29/2.25  %Background operators:
% 6.29/2.25  
% 6.29/2.25  
% 6.29/2.25  %Foreground operators:
% 6.29/2.25  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.29/2.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.29/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.29/2.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.29/2.25  tff('#skF_11', type, '#skF_11': $i).
% 6.29/2.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.29/2.25  tff('#skF_7', type, '#skF_7': $i).
% 6.29/2.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.29/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.29/2.25  tff('#skF_10', type, '#skF_10': $i).
% 6.29/2.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.29/2.25  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 6.29/2.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.29/2.25  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 6.29/2.25  tff('#skF_6', type, '#skF_6': $i).
% 6.29/2.25  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.29/2.25  tff('#skF_9', type, '#skF_9': $i).
% 6.29/2.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.29/2.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.29/2.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.29/2.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.29/2.25  tff('#skF_8', type, '#skF_8': $i).
% 6.29/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.29/2.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.29/2.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.29/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.29/2.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.29/2.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.29/2.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.29/2.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.29/2.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.29/2.25  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.29/2.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.29/2.25  
% 6.59/2.27  tff(f_154, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t186_funct_2)).
% 6.59/2.27  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.59/2.27  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.59/2.27  tff(f_129, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 6.59/2.27  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 6.59/2.27  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.59/2.27  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.59/2.27  tff(f_105, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_partfun1)).
% 6.59/2.27  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.59/2.27  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.59/2.27  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 6.59/2.27  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.59/2.27  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.59/2.27  tff(c_76, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.59/2.27  tff(c_64, plain, (m1_subset_1('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.59/2.27  tff(c_68, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.59/2.27  tff(c_66, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.59/2.27  tff(c_1495, plain, (![A_290, B_291, C_292]: (k1_relset_1(A_290, B_291, C_292)=k1_relat_1(C_292) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.59/2.27  tff(c_1503, plain, (k1_relset_1('#skF_8', '#skF_6', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_66, c_1495])).
% 6.59/2.27  tff(c_70, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.59/2.27  tff(c_1486, plain, (![A_287, B_288, C_289]: (k2_relset_1(A_287, B_288, C_289)=k2_relat_1(C_289) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.59/2.27  tff(c_1493, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_70, c_1486])).
% 6.59/2.27  tff(c_62, plain, (r1_tarski(k2_relset_1('#skF_7', '#skF_8', '#skF_9'), k1_relset_1('#skF_8', '#skF_6', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.59/2.27  tff(c_1505, plain, (r1_tarski(k2_relat_1('#skF_9'), k1_relset_1('#skF_8', '#skF_6', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1493, c_62])).
% 6.59/2.27  tff(c_1522, plain, (r1_tarski(k2_relat_1('#skF_9'), k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1503, c_1505])).
% 6.59/2.27  tff(c_60, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.59/2.27  tff(c_74, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.59/2.27  tff(c_72, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.59/2.27  tff(c_2698, plain, (![E_493, C_488, D_489, A_492, F_491, B_490]: (k1_funct_1(k8_funct_2(B_490, C_488, A_492, D_489, E_493), F_491)=k1_funct_1(E_493, k1_funct_1(D_489, F_491)) | k1_xboole_0=B_490 | ~r1_tarski(k2_relset_1(B_490, C_488, D_489), k1_relset_1(C_488, A_492, E_493)) | ~m1_subset_1(F_491, B_490) | ~m1_subset_1(E_493, k1_zfmisc_1(k2_zfmisc_1(C_488, A_492))) | ~v1_funct_1(E_493) | ~m1_subset_1(D_489, k1_zfmisc_1(k2_zfmisc_1(B_490, C_488))) | ~v1_funct_2(D_489, B_490, C_488) | ~v1_funct_1(D_489) | v1_xboole_0(C_488))), inference(cnfTransformation, [status(thm)], [f_129])).
% 6.59/2.27  tff(c_2706, plain, (![A_492, E_493, F_491]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', A_492, '#skF_9', E_493), F_491)=k1_funct_1(E_493, k1_funct_1('#skF_9', F_491)) | k1_xboole_0='#skF_7' | ~r1_tarski(k2_relat_1('#skF_9'), k1_relset_1('#skF_8', A_492, E_493)) | ~m1_subset_1(F_491, '#skF_7') | ~m1_subset_1(E_493, k1_zfmisc_1(k2_zfmisc_1('#skF_8', A_492))) | ~v1_funct_1(E_493) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_9') | v1_xboole_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1493, c_2698])).
% 6.59/2.27  tff(c_2716, plain, (![A_492, E_493, F_491]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', A_492, '#skF_9', E_493), F_491)=k1_funct_1(E_493, k1_funct_1('#skF_9', F_491)) | k1_xboole_0='#skF_7' | ~r1_tarski(k2_relat_1('#skF_9'), k1_relset_1('#skF_8', A_492, E_493)) | ~m1_subset_1(F_491, '#skF_7') | ~m1_subset_1(E_493, k1_zfmisc_1(k2_zfmisc_1('#skF_8', A_492))) | ~v1_funct_1(E_493) | v1_xboole_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_2706])).
% 6.59/2.27  tff(c_2855, plain, (![A_496, E_497, F_498]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', A_496, '#skF_9', E_497), F_498)=k1_funct_1(E_497, k1_funct_1('#skF_9', F_498)) | ~r1_tarski(k2_relat_1('#skF_9'), k1_relset_1('#skF_8', A_496, E_497)) | ~m1_subset_1(F_498, '#skF_7') | ~m1_subset_1(E_497, k1_zfmisc_1(k2_zfmisc_1('#skF_8', A_496))) | ~v1_funct_1(E_497))), inference(negUnitSimplification, [status(thm)], [c_76, c_60, c_2716])).
% 6.59/2.27  tff(c_2857, plain, (![F_498]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), F_498)=k1_funct_1('#skF_10', k1_funct_1('#skF_9', F_498)) | ~r1_tarski(k2_relat_1('#skF_9'), k1_relat_1('#skF_10')) | ~m1_subset_1(F_498, '#skF_7') | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6'))) | ~v1_funct_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1503, c_2855])).
% 6.59/2.27  tff(c_2859, plain, (![F_498]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), F_498)=k1_funct_1('#skF_10', k1_funct_1('#skF_9', F_498)) | ~m1_subset_1(F_498, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1522, c_2857])).
% 6.59/2.27  tff(c_12, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.59/2.27  tff(c_83, plain, (![C_97, A_98, B_99]: (v1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.59/2.27  tff(c_90, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_70, c_83])).
% 6.59/2.27  tff(c_1502, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_70, c_1495])).
% 6.59/2.27  tff(c_1590, plain, (![B_316, A_317, C_318]: (k1_xboole_0=B_316 | k1_relset_1(A_317, B_316, C_318)=A_317 | ~v1_funct_2(C_318, A_317, B_316) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_317, B_316))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.59/2.27  tff(c_1593, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_70, c_1590])).
% 6.59/2.27  tff(c_1599, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1502, c_1593])).
% 6.59/2.27  tff(c_1602, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_1599])).
% 6.59/2.27  tff(c_1699, plain, (![A_344, B_345, C_346]: (k7_partfun1(A_344, B_345, C_346)=k1_funct_1(B_345, C_346) | ~r2_hidden(C_346, k1_relat_1(B_345)) | ~v1_funct_1(B_345) | ~v5_relat_1(B_345, A_344) | ~v1_relat_1(B_345))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.59/2.27  tff(c_1715, plain, (![A_344, C_346]: (k7_partfun1(A_344, '#skF_9', C_346)=k1_funct_1('#skF_9', C_346) | ~r2_hidden(C_346, '#skF_7') | ~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', A_344) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1602, c_1699])).
% 6.59/2.27  tff(c_1759, plain, (![A_348, C_349]: (k7_partfun1(A_348, '#skF_9', C_349)=k1_funct_1('#skF_9', C_349) | ~r2_hidden(C_349, '#skF_7') | ~v5_relat_1('#skF_9', A_348))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_74, c_1715])).
% 6.59/2.27  tff(c_1793, plain, (![A_348, A_7]: (k7_partfun1(A_348, '#skF_9', A_7)=k1_funct_1('#skF_9', A_7) | ~v5_relat_1('#skF_9', A_348) | v1_xboole_0('#skF_7') | ~m1_subset_1(A_7, '#skF_7'))), inference(resolution, [status(thm)], [c_12, c_1759])).
% 6.59/2.27  tff(c_1799, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1793])).
% 6.59/2.27  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.59/2.27  tff(c_1802, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1799, c_10])).
% 6.59/2.27  tff(c_1806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1802])).
% 6.59/2.27  tff(c_1808, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_1793])).
% 6.59/2.27  tff(c_115, plain, (![C_110, B_111, A_112]: (v5_relat_1(C_110, B_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.59/2.27  tff(c_123, plain, (v5_relat_1('#skF_10', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_115])).
% 6.59/2.27  tff(c_91, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_66, c_83])).
% 6.59/2.27  tff(c_14, plain, (![A_9, D_48]: (r2_hidden(k1_funct_1(A_9, D_48), k2_relat_1(A_9)) | ~r2_hidden(D_48, k1_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.59/2.27  tff(c_99, plain, (![A_104, B_105]: (r2_hidden('#skF_1'(A_104, B_105), A_104) | r1_tarski(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.59/2.27  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.59/2.27  tff(c_104, plain, (![A_104]: (r1_tarski(A_104, A_104))), inference(resolution, [status(thm)], [c_99, c_4])).
% 6.59/2.27  tff(c_1574, plain, (![A_312, C_313]: (r2_hidden('#skF_5'(A_312, k2_relat_1(A_312), C_313), k1_relat_1(A_312)) | ~r2_hidden(C_313, k2_relat_1(A_312)) | ~v1_funct_1(A_312) | ~v1_relat_1(A_312))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.59/2.27  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.59/2.27  tff(c_1577, plain, (![A_312, C_313, B_2]: (r2_hidden('#skF_5'(A_312, k2_relat_1(A_312), C_313), B_2) | ~r1_tarski(k1_relat_1(A_312), B_2) | ~r2_hidden(C_313, k2_relat_1(A_312)) | ~v1_funct_1(A_312) | ~v1_relat_1(A_312))), inference(resolution, [status(thm)], [c_1574, c_2])).
% 6.59/2.27  tff(c_16, plain, (![A_9, C_45]: (k1_funct_1(A_9, '#skF_5'(A_9, k2_relat_1(A_9), C_45))=C_45 | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.59/2.27  tff(c_1543, plain, (![A_297, D_298]: (r2_hidden(k1_funct_1(A_297, D_298), k2_relat_1(A_297)) | ~r2_hidden(D_298, k1_relat_1(A_297)) | ~v1_funct_1(A_297) | ~v1_relat_1(A_297))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.59/2.27  tff(c_1672, plain, (![A_336, D_337, B_338]: (r2_hidden(k1_funct_1(A_336, D_337), B_338) | ~r1_tarski(k2_relat_1(A_336), B_338) | ~r2_hidden(D_337, k1_relat_1(A_336)) | ~v1_funct_1(A_336) | ~v1_relat_1(A_336))), inference(resolution, [status(thm)], [c_1543, c_2])).
% 6.59/2.27  tff(c_1994, plain, (![A_387, D_388, B_389, B_390]: (r2_hidden(k1_funct_1(A_387, D_388), B_389) | ~r1_tarski(B_390, B_389) | ~r1_tarski(k2_relat_1(A_387), B_390) | ~r2_hidden(D_388, k1_relat_1(A_387)) | ~v1_funct_1(A_387) | ~v1_relat_1(A_387))), inference(resolution, [status(thm)], [c_1672, c_2])).
% 6.59/2.27  tff(c_2001, plain, (![A_391, D_392]: (r2_hidden(k1_funct_1(A_391, D_392), k1_relat_1('#skF_10')) | ~r1_tarski(k2_relat_1(A_391), k2_relat_1('#skF_9')) | ~r2_hidden(D_392, k1_relat_1(A_391)) | ~v1_funct_1(A_391) | ~v1_relat_1(A_391))), inference(resolution, [status(thm)], [c_1522, c_1994])).
% 6.59/2.27  tff(c_2658, plain, (![A_478, D_479, B_480]: (r2_hidden(k1_funct_1(A_478, D_479), B_480) | ~r1_tarski(k1_relat_1('#skF_10'), B_480) | ~r1_tarski(k2_relat_1(A_478), k2_relat_1('#skF_9')) | ~r2_hidden(D_479, k1_relat_1(A_478)) | ~v1_funct_1(A_478) | ~v1_relat_1(A_478))), inference(resolution, [status(thm)], [c_2001, c_2])).
% 6.59/2.27  tff(c_2661, plain, (![D_479, B_480]: (r2_hidden(k1_funct_1('#skF_9', D_479), B_480) | ~r1_tarski(k1_relat_1('#skF_10'), B_480) | ~r2_hidden(D_479, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_104, c_2658])).
% 6.59/2.27  tff(c_2665, plain, (![D_481, B_482]: (r2_hidden(k1_funct_1('#skF_9', D_481), B_482) | ~r1_tarski(k1_relat_1('#skF_10'), B_482) | ~r2_hidden(D_481, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_74, c_1602, c_2661])).
% 6.59/2.27  tff(c_2679, plain, (![C_45, B_482]: (r2_hidden(C_45, B_482) | ~r1_tarski(k1_relat_1('#skF_10'), B_482) | ~r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_45), '#skF_7') | ~r2_hidden(C_45, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2665])).
% 6.59/2.27  tff(c_2693, plain, (![C_486, B_487]: (r2_hidden(C_486, B_487) | ~r1_tarski(k1_relat_1('#skF_10'), B_487) | ~r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_486), '#skF_7') | ~r2_hidden(C_486, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_74, c_2679])).
% 6.59/2.27  tff(c_2718, plain, (![C_494]: (r2_hidden(C_494, k1_relat_1('#skF_10')) | ~r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_494), '#skF_7') | ~r2_hidden(C_494, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_104, c_2693])).
% 6.59/2.27  tff(c_2722, plain, (![C_313]: (r2_hidden(C_313, k1_relat_1('#skF_10')) | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_7') | ~r2_hidden(C_313, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1577, c_2718])).
% 6.59/2.27  tff(c_2743, plain, (![C_495]: (r2_hidden(C_495, k1_relat_1('#skF_10')) | ~r2_hidden(C_495, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_74, c_104, c_1602, c_2722])).
% 6.59/2.27  tff(c_2815, plain, (![D_48]: (r2_hidden(k1_funct_1('#skF_9', D_48), k1_relat_1('#skF_10')) | ~r2_hidden(D_48, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_14, c_2743])).
% 6.59/2.27  tff(c_2860, plain, (![D_499]: (r2_hidden(k1_funct_1('#skF_9', D_499), k1_relat_1('#skF_10')) | ~r2_hidden(D_499, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_74, c_1602, c_2815])).
% 6.59/2.27  tff(c_54, plain, (![A_64, B_65, C_67]: (k7_partfun1(A_64, B_65, C_67)=k1_funct_1(B_65, C_67) | ~r2_hidden(C_67, k1_relat_1(B_65)) | ~v1_funct_1(B_65) | ~v5_relat_1(B_65, A_64) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.59/2.27  tff(c_2862, plain, (![A_64, D_499]: (k7_partfun1(A_64, '#skF_10', k1_funct_1('#skF_9', D_499))=k1_funct_1('#skF_10', k1_funct_1('#skF_9', D_499)) | ~v1_funct_1('#skF_10') | ~v5_relat_1('#skF_10', A_64) | ~v1_relat_1('#skF_10') | ~r2_hidden(D_499, '#skF_7'))), inference(resolution, [status(thm)], [c_2860, c_54])).
% 6.59/2.27  tff(c_3056, plain, (![A_508, D_509]: (k7_partfun1(A_508, '#skF_10', k1_funct_1('#skF_9', D_509))=k1_funct_1('#skF_10', k1_funct_1('#skF_9', D_509)) | ~v5_relat_1('#skF_10', A_508) | ~r2_hidden(D_509, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_68, c_2862])).
% 6.59/2.27  tff(c_58, plain, (k7_partfun1('#skF_6', '#skF_10', k1_funct_1('#skF_9', '#skF_11'))!=k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_154])).
% 6.59/2.27  tff(c_3062, plain, (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')!=k1_funct_1('#skF_10', k1_funct_1('#skF_9', '#skF_11')) | ~v5_relat_1('#skF_10', '#skF_6') | ~r2_hidden('#skF_11', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3056, c_58])).
% 6.59/2.27  tff(c_3076, plain, (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')!=k1_funct_1('#skF_10', k1_funct_1('#skF_9', '#skF_11')) | ~r2_hidden('#skF_11', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_3062])).
% 6.59/2.27  tff(c_3086, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_3076])).
% 6.59/2.27  tff(c_3089, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1('#skF_11', '#skF_7')), inference(resolution, [status(thm)], [c_12, c_3086])).
% 6.59/2.27  tff(c_3092, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3089])).
% 6.59/2.27  tff(c_3094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1808, c_3092])).
% 6.59/2.27  tff(c_3095, plain, (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')!=k1_funct_1('#skF_10', k1_funct_1('#skF_9', '#skF_11'))), inference(splitRight, [status(thm)], [c_3076])).
% 6.59/2.27  tff(c_3149, plain, (~m1_subset_1('#skF_11', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2859, c_3095])).
% 6.59/2.27  tff(c_3153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_3149])).
% 6.59/2.27  tff(c_3154, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1599])).
% 6.59/2.27  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.59/2.27  tff(c_3163, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3154, c_8])).
% 6.59/2.27  tff(c_3166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_3163])).
% 6.59/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.59/2.27  
% 6.59/2.27  Inference rules
% 6.59/2.27  ----------------------
% 6.59/2.27  #Ref     : 0
% 6.59/2.27  #Sup     : 684
% 6.59/2.27  #Fact    : 0
% 6.59/2.27  #Define  : 0
% 6.59/2.27  #Split   : 24
% 6.59/2.27  #Chain   : 0
% 6.59/2.27  #Close   : 0
% 6.59/2.27  
% 6.59/2.27  Ordering : KBO
% 6.59/2.27  
% 6.59/2.27  Simplification rules
% 6.59/2.27  ----------------------
% 6.59/2.27  #Subsume      : 146
% 6.59/2.27  #Demod        : 386
% 6.59/2.27  #Tautology    : 117
% 6.59/2.27  #SimpNegUnit  : 30
% 6.59/2.27  #BackRed      : 68
% 6.59/2.27  
% 6.59/2.27  #Partial instantiations: 0
% 6.59/2.27  #Strategies tried      : 1
% 6.59/2.27  
% 6.59/2.27  Timing (in seconds)
% 6.59/2.27  ----------------------
% 6.59/2.27  Preprocessing        : 0.38
% 6.59/2.27  Parsing              : 0.18
% 6.59/2.27  CNF conversion       : 0.04
% 6.59/2.27  Main loop            : 1.13
% 6.59/2.27  Inferencing          : 0.41
% 6.59/2.27  Reduction            : 0.35
% 6.59/2.27  Demodulation         : 0.24
% 6.59/2.27  BG Simplification    : 0.05
% 6.59/2.27  Subsumption          : 0.24
% 6.59/2.27  Abstraction          : 0.06
% 6.59/2.27  MUC search           : 0.00
% 6.59/2.27  Cooper               : 0.00
% 6.59/2.27  Total                : 1.56
% 6.59/2.27  Index Insertion      : 0.00
% 6.59/2.27  Index Deletion       : 0.00
% 6.59/2.27  Index Matching       : 0.00
% 6.59/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
