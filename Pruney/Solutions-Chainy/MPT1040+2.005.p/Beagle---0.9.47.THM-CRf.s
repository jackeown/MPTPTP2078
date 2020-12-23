%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:02 EST 2020

% Result     : Theorem 13.70s
% Output     : CNFRefutation 13.70s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 574 expanded)
%              Number of leaves         :   37 ( 198 expanded)
%              Depth                    :   11
%              Number of atoms          :  174 (1628 expanded)
%              Number of equality atoms :   25 ( 579 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_10 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_hidden(D,k5_partfun1(A,B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(c_17510,plain,(
    ! [A_256] :
      ( v1_xboole_0(A_256)
      | r2_hidden('#skF_1'(A_256),A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_105,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_68,plain,(
    ~ r2_hidden('#skF_11',k5_partfun1('#skF_8','#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_82,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_72,plain,(
    r1_partfun1('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_80,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_78,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_74,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_176,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( r2_hidden('#skF_3'(A_82,B_83,C_84,D_85),C_84)
      | ~ r2_hidden(A_82,D_85)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(B_83,C_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_251,plain,(
    ! [A_94] :
      ( r2_hidden('#skF_3'(A_94,'#skF_8','#skF_9','#skF_11'),'#skF_9')
      | ~ r2_hidden(A_94,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_74,c_176])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_258,plain,(
    ! [A_94] :
      ( ~ v1_xboole_0('#skF_9')
      | ~ r2_hidden(A_94,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_251,c_2])).

tff(c_259,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_76,plain,(
    v1_funct_2('#skF_11','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_270,plain,(
    ! [C_96,A_97,B_98] :
      ( v1_partfun1(C_96,A_97)
      | ~ v1_funct_2(C_96,A_97,B_98)
      | ~ v1_funct_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | v1_xboole_0(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_279,plain,
    ( v1_partfun1('#skF_11','#skF_8')
    | ~ v1_funct_2('#skF_11','#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_11')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_74,c_270])).

tff(c_294,plain,
    ( v1_partfun1('#skF_11','#skF_8')
    | v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_279])).

tff(c_295,plain,(
    v1_partfun1('#skF_11','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_294])).

tff(c_16632,plain,(
    ! [F_239,A_240,B_241,C_242] :
      ( r2_hidden(F_239,k5_partfun1(A_240,B_241,C_242))
      | ~ r1_partfun1(C_242,F_239)
      | ~ v1_partfun1(F_239,A_240)
      | ~ m1_subset_1(F_239,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | ~ v1_funct_1(F_239)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | ~ v1_funct_1(C_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_16648,plain,(
    ! [C_242] :
      ( r2_hidden('#skF_11',k5_partfun1('#skF_8','#skF_9',C_242))
      | ~ r1_partfun1(C_242,'#skF_11')
      | ~ v1_partfun1('#skF_11','#skF_8')
      | ~ v1_funct_1('#skF_11')
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9')))
      | ~ v1_funct_1(C_242) ) ),
    inference(resolution,[status(thm)],[c_74,c_16632])).

tff(c_17434,plain,(
    ! [C_246] :
      ( r2_hidden('#skF_11',k5_partfun1('#skF_8','#skF_9',C_246))
      | ~ r1_partfun1(C_246,'#skF_11')
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9')))
      | ~ v1_funct_1(C_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_295,c_16648])).

tff(c_17441,plain,
    ( r2_hidden('#skF_11',k5_partfun1('#skF_8','#skF_9','#skF_10'))
    | ~ r1_partfun1('#skF_10','#skF_11')
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_80,c_17434])).

tff(c_17448,plain,(
    r2_hidden('#skF_11',k5_partfun1('#skF_8','#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_72,c_17441])).

tff(c_17450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_17448])).

tff(c_17452,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_17455,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_17452,c_6])).

tff(c_17459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_17455])).

tff(c_17460,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_17462,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17460,c_17460,c_10])).

tff(c_17499,plain,(
    ! [A_251,B_252] : ~ r2_hidden(A_251,k2_zfmisc_1(A_251,B_252)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_17505,plain,(
    ! [A_6] : ~ r2_hidden(A_6,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_17462,c_17499])).

tff(c_17519,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_17510,c_17505])).

tff(c_17461,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_17468,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17460,c_17461])).

tff(c_17520,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17462,c_17468,c_74])).

tff(c_17535,plain,(
    ! [B_258,A_259] :
      ( v1_xboole_0(B_258)
      | ~ m1_subset_1(B_258,k1_zfmisc_1(A_259))
      | ~ v1_xboole_0(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_17544,plain,
    ( v1_xboole_0('#skF_11')
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_17520,c_17535])).

tff(c_17554,plain,(
    v1_xboole_0('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17519,c_17544])).

tff(c_17475,plain,(
    ! [A_5] :
      ( A_5 = '#skF_8'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17460,c_6])).

tff(c_17561,plain,(
    '#skF_11' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_17554,c_17475])).

tff(c_17571,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17561,c_78])).

tff(c_17506,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17462,c_17468,c_80])).

tff(c_17547,plain,
    ( v1_xboole_0('#skF_10')
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_17506,c_17535])).

tff(c_17557,plain,(
    v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17519,c_17547])).

tff(c_17565,plain,(
    '#skF_10' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_17557,c_17475])).

tff(c_17578,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17565,c_17506])).

tff(c_17570,plain,(
    r1_partfun1('#skF_10','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17561,c_72])).

tff(c_17602,plain,(
    r1_partfun1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17565,c_17570])).

tff(c_12,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_17463,plain,(
    ! [B_7] : k2_zfmisc_1('#skF_8',B_7) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17460,c_17460,c_12])).

tff(c_17526,plain,(
    ! [A_257] : m1_subset_1(k6_partfun1(A_257),k1_zfmisc_1(k2_zfmisc_1(A_257,A_257))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_17530,plain,(
    m1_subset_1(k6_partfun1('#skF_8'),k1_zfmisc_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_17463,c_17526])).

tff(c_17538,plain,
    ( v1_xboole_0(k6_partfun1('#skF_8'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_17530,c_17535])).

tff(c_17550,plain,(
    v1_xboole_0(k6_partfun1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17519,c_17538])).

tff(c_17601,plain,(
    k6_partfun1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_17550,c_17475])).

tff(c_64,plain,(
    ! [A_65] : v1_partfun1(k6_partfun1(A_65),A_65) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_66,plain,(
    ! [A_65] : m1_subset_1(k6_partfun1(A_65),k1_zfmisc_1(k2_zfmisc_1(A_65,A_65))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_23460,plain,(
    ! [F_374,A_375,B_376,C_377] :
      ( r2_hidden(F_374,k5_partfun1(A_375,B_376,C_377))
      | ~ r1_partfun1(C_377,F_374)
      | ~ v1_partfun1(F_374,A_375)
      | ~ m1_subset_1(F_374,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376)))
      | ~ v1_funct_1(F_374)
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376)))
      | ~ v1_funct_1(C_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_23466,plain,(
    ! [A_65,C_377] :
      ( r2_hidden(k6_partfun1(A_65),k5_partfun1(A_65,A_65,C_377))
      | ~ r1_partfun1(C_377,k6_partfun1(A_65))
      | ~ v1_partfun1(k6_partfun1(A_65),A_65)
      | ~ v1_funct_1(k6_partfun1(A_65))
      | ~ m1_subset_1(C_377,k1_zfmisc_1(k2_zfmisc_1(A_65,A_65)))
      | ~ v1_funct_1(C_377) ) ),
    inference(resolution,[status(thm)],[c_66,c_23460])).

tff(c_60253,plain,(
    ! [A_478,C_479] :
      ( r2_hidden(k6_partfun1(A_478),k5_partfun1(A_478,A_478,C_479))
      | ~ r1_partfun1(C_479,k6_partfun1(A_478))
      | ~ v1_funct_1(k6_partfun1(A_478))
      | ~ m1_subset_1(C_479,k1_zfmisc_1(k2_zfmisc_1(A_478,A_478)))
      | ~ v1_funct_1(C_479) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_23466])).

tff(c_60320,plain,(
    ! [C_479] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8',C_479))
      | ~ r1_partfun1(C_479,k6_partfun1('#skF_8'))
      | ~ v1_funct_1(k6_partfun1('#skF_8'))
      | ~ m1_subset_1(C_479,k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8')))
      | ~ v1_funct_1(C_479) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17601,c_60253])).

tff(c_60326,plain,(
    ! [C_480] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8',C_480))
      | ~ r1_partfun1(C_480,'#skF_8')
      | ~ m1_subset_1(C_480,k1_zfmisc_1('#skF_8'))
      | ~ v1_funct_1(C_480) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17462,c_17571,c_17601,c_17601,c_60320])).

tff(c_17509,plain,(
    ~ r2_hidden('#skF_11',k5_partfun1('#skF_8','#skF_8','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17468,c_68])).

tff(c_17568,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17561,c_17509])).

tff(c_17636,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_8','#skF_8','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17565,c_17568])).

tff(c_60333,plain,
    ( ~ r1_partfun1('#skF_8','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8'))
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60326,c_17636])).

tff(c_60343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17571,c_17578,c_17602,c_60333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:07:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.70/6.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.70/6.36  
% 13.70/6.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.70/6.37  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_10 > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3
% 13.70/6.37  
% 13.70/6.37  %Foreground sorts:
% 13.70/6.37  
% 13.70/6.37  
% 13.70/6.37  %Background operators:
% 13.70/6.37  
% 13.70/6.37  
% 13.70/6.37  %Foreground operators:
% 13.70/6.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.70/6.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.70/6.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.70/6.37  tff('#skF_11', type, '#skF_11': $i).
% 13.70/6.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 13.70/6.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.70/6.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.70/6.37  tff('#skF_10', type, '#skF_10': $i).
% 13.70/6.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.70/6.37  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i * $i) > $i).
% 13.70/6.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 13.70/6.37  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 13.70/6.37  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 13.70/6.37  tff('#skF_9', type, '#skF_9': $i).
% 13.70/6.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.70/6.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 13.70/6.37  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 13.70/6.37  tff('#skF_8', type, '#skF_8': $i).
% 13.70/6.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.70/6.37  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 13.70/6.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.70/6.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.70/6.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 13.70/6.37  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 13.70/6.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.70/6.37  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 13.70/6.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.70/6.37  
% 13.70/6.38  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.70/6.38  tff(f_124, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_hidden(D, k5_partfun1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 13.70/6.38  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 13.70/6.38  tff(f_78, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 13.70/6.38  tff(f_99, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 13.70/6.38  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 13.70/6.38  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.70/6.38  tff(f_44, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 13.70/6.38  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 13.70/6.38  tff(f_103, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 13.70/6.38  tff(c_17510, plain, (![A_256]: (v1_xboole_0(A_256) | r2_hidden('#skF_1'(A_256), A_256))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.70/6.38  tff(c_70, plain, (k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.70/6.38  tff(c_105, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_70])).
% 13.70/6.38  tff(c_68, plain, (~r2_hidden('#skF_11', k5_partfun1('#skF_8', '#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.70/6.38  tff(c_82, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.70/6.38  tff(c_72, plain, (r1_partfun1('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.70/6.38  tff(c_80, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.70/6.38  tff(c_78, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.70/6.38  tff(c_74, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.70/6.38  tff(c_176, plain, (![A_82, B_83, C_84, D_85]: (r2_hidden('#skF_3'(A_82, B_83, C_84, D_85), C_84) | ~r2_hidden(A_82, D_85) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(B_83, C_84))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.70/6.38  tff(c_251, plain, (![A_94]: (r2_hidden('#skF_3'(A_94, '#skF_8', '#skF_9', '#skF_11'), '#skF_9') | ~r2_hidden(A_94, '#skF_11'))), inference(resolution, [status(thm)], [c_74, c_176])).
% 13.70/6.38  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.70/6.38  tff(c_258, plain, (![A_94]: (~v1_xboole_0('#skF_9') | ~r2_hidden(A_94, '#skF_11'))), inference(resolution, [status(thm)], [c_251, c_2])).
% 13.70/6.38  tff(c_259, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_258])).
% 13.70/6.38  tff(c_76, plain, (v1_funct_2('#skF_11', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_124])).
% 13.70/6.38  tff(c_270, plain, (![C_96, A_97, B_98]: (v1_partfun1(C_96, A_97) | ~v1_funct_2(C_96, A_97, B_98) | ~v1_funct_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | v1_xboole_0(B_98))), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.70/6.38  tff(c_279, plain, (v1_partfun1('#skF_11', '#skF_8') | ~v1_funct_2('#skF_11', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_11') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_74, c_270])).
% 13.70/6.38  tff(c_294, plain, (v1_partfun1('#skF_11', '#skF_8') | v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_279])).
% 13.70/6.38  tff(c_295, plain, (v1_partfun1('#skF_11', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_259, c_294])).
% 13.70/6.38  tff(c_16632, plain, (![F_239, A_240, B_241, C_242]: (r2_hidden(F_239, k5_partfun1(A_240, B_241, C_242)) | ~r1_partfun1(C_242, F_239) | ~v1_partfun1(F_239, A_240) | ~m1_subset_1(F_239, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | ~v1_funct_1(F_239) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | ~v1_funct_1(C_242))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.70/6.38  tff(c_16648, plain, (![C_242]: (r2_hidden('#skF_11', k5_partfun1('#skF_8', '#skF_9', C_242)) | ~r1_partfun1(C_242, '#skF_11') | ~v1_partfun1('#skF_11', '#skF_8') | ~v1_funct_1('#skF_11') | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'))) | ~v1_funct_1(C_242))), inference(resolution, [status(thm)], [c_74, c_16632])).
% 13.70/6.38  tff(c_17434, plain, (![C_246]: (r2_hidden('#skF_11', k5_partfun1('#skF_8', '#skF_9', C_246)) | ~r1_partfun1(C_246, '#skF_11') | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'))) | ~v1_funct_1(C_246))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_295, c_16648])).
% 13.70/6.38  tff(c_17441, plain, (r2_hidden('#skF_11', k5_partfun1('#skF_8', '#skF_9', '#skF_10')) | ~r1_partfun1('#skF_10', '#skF_11') | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_80, c_17434])).
% 13.70/6.38  tff(c_17448, plain, (r2_hidden('#skF_11', k5_partfun1('#skF_8', '#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_72, c_17441])).
% 13.70/6.38  tff(c_17450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_17448])).
% 13.70/6.38  tff(c_17452, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_258])).
% 13.70/6.38  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.70/6.38  tff(c_17455, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_17452, c_6])).
% 13.70/6.38  tff(c_17459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_17455])).
% 13.70/6.38  tff(c_17460, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_70])).
% 13.70/6.38  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.70/6.38  tff(c_17462, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17460, c_17460, c_10])).
% 13.70/6.38  tff(c_17499, plain, (![A_251, B_252]: (~r2_hidden(A_251, k2_zfmisc_1(A_251, B_252)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.70/6.38  tff(c_17505, plain, (![A_6]: (~r2_hidden(A_6, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_17462, c_17499])).
% 13.70/6.38  tff(c_17519, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_17510, c_17505])).
% 13.70/6.38  tff(c_17461, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_70])).
% 13.70/6.38  tff(c_17468, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_17460, c_17461])).
% 13.70/6.38  tff(c_17520, plain, (m1_subset_1('#skF_11', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_17462, c_17468, c_74])).
% 13.70/6.38  tff(c_17535, plain, (![B_258, A_259]: (v1_xboole_0(B_258) | ~m1_subset_1(B_258, k1_zfmisc_1(A_259)) | ~v1_xboole_0(A_259))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.70/6.38  tff(c_17544, plain, (v1_xboole_0('#skF_11') | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_17520, c_17535])).
% 13.70/6.38  tff(c_17554, plain, (v1_xboole_0('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_17519, c_17544])).
% 13.70/6.38  tff(c_17475, plain, (![A_5]: (A_5='#skF_8' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_17460, c_6])).
% 13.70/6.38  tff(c_17561, plain, ('#skF_11'='#skF_8'), inference(resolution, [status(thm)], [c_17554, c_17475])).
% 13.70/6.38  tff(c_17571, plain, (v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17561, c_78])).
% 13.70/6.38  tff(c_17506, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_17462, c_17468, c_80])).
% 13.70/6.38  tff(c_17547, plain, (v1_xboole_0('#skF_10') | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_17506, c_17535])).
% 13.70/6.38  tff(c_17557, plain, (v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_17519, c_17547])).
% 13.70/6.38  tff(c_17565, plain, ('#skF_10'='#skF_8'), inference(resolution, [status(thm)], [c_17557, c_17475])).
% 13.70/6.38  tff(c_17578, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_17565, c_17506])).
% 13.70/6.38  tff(c_17570, plain, (r1_partfun1('#skF_10', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17561, c_72])).
% 13.70/6.38  tff(c_17602, plain, (r1_partfun1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17565, c_17570])).
% 13.70/6.38  tff(c_12, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.70/6.38  tff(c_17463, plain, (![B_7]: (k2_zfmisc_1('#skF_8', B_7)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17460, c_17460, c_12])).
% 13.70/6.38  tff(c_17526, plain, (![A_257]: (m1_subset_1(k6_partfun1(A_257), k1_zfmisc_1(k2_zfmisc_1(A_257, A_257))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.70/6.38  tff(c_17530, plain, (m1_subset_1(k6_partfun1('#skF_8'), k1_zfmisc_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_17463, c_17526])).
% 13.70/6.38  tff(c_17538, plain, (v1_xboole_0(k6_partfun1('#skF_8')) | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_17530, c_17535])).
% 13.70/6.38  tff(c_17550, plain, (v1_xboole_0(k6_partfun1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_17519, c_17538])).
% 13.70/6.38  tff(c_17601, plain, (k6_partfun1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_17550, c_17475])).
% 13.70/6.38  tff(c_64, plain, (![A_65]: (v1_partfun1(k6_partfun1(A_65), A_65))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.70/6.38  tff(c_66, plain, (![A_65]: (m1_subset_1(k6_partfun1(A_65), k1_zfmisc_1(k2_zfmisc_1(A_65, A_65))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.70/6.38  tff(c_23460, plain, (![F_374, A_375, B_376, C_377]: (r2_hidden(F_374, k5_partfun1(A_375, B_376, C_377)) | ~r1_partfun1(C_377, F_374) | ~v1_partfun1(F_374, A_375) | ~m1_subset_1(F_374, k1_zfmisc_1(k2_zfmisc_1(A_375, B_376))) | ~v1_funct_1(F_374) | ~m1_subset_1(C_377, k1_zfmisc_1(k2_zfmisc_1(A_375, B_376))) | ~v1_funct_1(C_377))), inference(cnfTransformation, [status(thm)], [f_99])).
% 13.70/6.38  tff(c_23466, plain, (![A_65, C_377]: (r2_hidden(k6_partfun1(A_65), k5_partfun1(A_65, A_65, C_377)) | ~r1_partfun1(C_377, k6_partfun1(A_65)) | ~v1_partfun1(k6_partfun1(A_65), A_65) | ~v1_funct_1(k6_partfun1(A_65)) | ~m1_subset_1(C_377, k1_zfmisc_1(k2_zfmisc_1(A_65, A_65))) | ~v1_funct_1(C_377))), inference(resolution, [status(thm)], [c_66, c_23460])).
% 13.70/6.38  tff(c_60253, plain, (![A_478, C_479]: (r2_hidden(k6_partfun1(A_478), k5_partfun1(A_478, A_478, C_479)) | ~r1_partfun1(C_479, k6_partfun1(A_478)) | ~v1_funct_1(k6_partfun1(A_478)) | ~m1_subset_1(C_479, k1_zfmisc_1(k2_zfmisc_1(A_478, A_478))) | ~v1_funct_1(C_479))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_23466])).
% 13.70/6.38  tff(c_60320, plain, (![C_479]: (r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', C_479)) | ~r1_partfun1(C_479, k6_partfun1('#skF_8')) | ~v1_funct_1(k6_partfun1('#skF_8')) | ~m1_subset_1(C_479, k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8'))) | ~v1_funct_1(C_479))), inference(superposition, [status(thm), theory('equality')], [c_17601, c_60253])).
% 13.70/6.38  tff(c_60326, plain, (![C_480]: (r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', C_480)) | ~r1_partfun1(C_480, '#skF_8') | ~m1_subset_1(C_480, k1_zfmisc_1('#skF_8')) | ~v1_funct_1(C_480))), inference(demodulation, [status(thm), theory('equality')], [c_17462, c_17571, c_17601, c_17601, c_60320])).
% 13.70/6.38  tff(c_17509, plain, (~r2_hidden('#skF_11', k5_partfun1('#skF_8', '#skF_8', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_17468, c_68])).
% 13.70/6.38  tff(c_17568, plain, (~r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_17561, c_17509])).
% 13.70/6.38  tff(c_17636, plain, (~r2_hidden('#skF_8', k5_partfun1('#skF_8', '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_17565, c_17568])).
% 13.70/6.38  tff(c_60333, plain, (~r1_partfun1('#skF_8', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8')) | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_60326, c_17636])).
% 13.70/6.38  tff(c_60343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17571, c_17578, c_17602, c_60333])).
% 13.70/6.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.70/6.38  
% 13.70/6.38  Inference rules
% 13.70/6.38  ----------------------
% 13.70/6.38  #Ref     : 0
% 13.70/6.38  #Sup     : 15128
% 13.70/6.38  #Fact    : 0
% 13.70/6.38  #Define  : 0
% 13.70/6.38  #Split   : 9
% 13.70/6.38  #Chain   : 0
% 13.70/6.38  #Close   : 0
% 13.70/6.38  
% 13.70/6.38  Ordering : KBO
% 13.70/6.38  
% 13.70/6.38  Simplification rules
% 13.70/6.38  ----------------------
% 13.70/6.38  #Subsume      : 3504
% 13.70/6.38  #Demod        : 49382
% 13.70/6.38  #Tautology    : 11019
% 13.70/6.38  #SimpNegUnit  : 13
% 13.70/6.38  #BackRed      : 21
% 13.70/6.38  
% 13.70/6.38  #Partial instantiations: 0
% 13.70/6.38  #Strategies tried      : 1
% 13.70/6.38  
% 13.70/6.38  Timing (in seconds)
% 13.70/6.38  ----------------------
% 13.91/6.39  Preprocessing        : 0.35
% 13.91/6.39  Parsing              : 0.18
% 13.91/6.39  CNF conversion       : 0.03
% 13.91/6.39  Main loop            : 5.23
% 13.91/6.39  Inferencing          : 1.02
% 13.91/6.39  Reduction            : 2.23
% 13.91/6.39  Demodulation         : 1.83
% 13.91/6.39  BG Simplification    : 0.13
% 13.91/6.39  Subsumption          : 1.68
% 13.91/6.39  Abstraction          : 0.26
% 13.91/6.39  MUC search           : 0.00
% 13.91/6.39  Cooper               : 0.00
% 13.91/6.39  Total                : 5.62
% 13.91/6.39  Index Insertion      : 0.00
% 13.91/6.39  Index Deletion       : 0.00
% 13.91/6.39  Index Matching       : 0.00
% 13.91/6.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
