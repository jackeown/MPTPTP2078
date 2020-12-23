%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1045+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:19 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 212 expanded)
%              Number of leaves         :   23 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  121 ( 538 expanded)
%              Number of equality atoms :   37 ( 266 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k5_partfun1(A,B,k3_partfun1(C,A,B)) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k3_partfun1(C,A,B) = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
      <=> k5_partfun1(A,B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_partfun1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(c_24,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_25,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_33,plain,(
    ! [C_20,A_21,B_22] :
      ( k3_partfun1(C_20,A_21,B_22) = C_20
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_33])).

tff(c_39,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_36])).

tff(c_16,plain,(
    k5_partfun1('#skF_1','#skF_2',k3_partfun1('#skF_3','#skF_1','#skF_2')) != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    k5_partfun1('#skF_1','#skF_2','#skF_3') != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_16])).

tff(c_59,plain,(
    ! [A_29,B_30,C_31] :
      ( k5_partfun1(A_29,B_30,C_31) = k1_tarski(C_31)
      | ~ v1_partfun1(C_31,A_29)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ v1_funct_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,
    ( k5_partfun1('#skF_1','#skF_2','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_59])).

tff(c_65,plain,
    ( k5_partfun1('#skF_1','#skF_2','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_62])).

tff(c_66,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_65])).

tff(c_22,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_52,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_partfun1(C_26,A_27)
      | ~ v1_funct_2(C_26,A_27,B_28)
      | ~ v1_funct_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | v1_xboole_0(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_52])).

tff(c_58,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_55])).

tff(c_67,plain,(
    v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_58])).

tff(c_12,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_70,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_67,c_12])).

tff(c_74,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25,c_70])).

tff(c_75,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_76,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_81,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_76])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_20])).

tff(c_133,plain,(
    ! [C_45,A_46,B_47] :
      ( k3_partfun1(C_45,A_46,B_47) = C_45
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_136,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_133])).

tff(c_139,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_136])).

tff(c_90,plain,(
    k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_3','#skF_1','#skF_1')) != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_81,c_16])).

tff(c_140,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_3') != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_90])).

tff(c_97,plain,(
    ! [C_36,A_37,B_38] :
      ( k3_partfun1(C_36,A_37,B_38) = C_36
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38)))
      | ~ v1_funct_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_100,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_97])).

tff(c_103,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_100])).

tff(c_104,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_3') != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_90])).

tff(c_91,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_partfun1(C_33,A_34)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_91])).

tff(c_96,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_83,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_22])).

tff(c_109,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_partfun1(C_39,A_40)
      | ~ v1_funct_2(C_39,A_40,B_41)
      | ~ v1_funct_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | v1_xboole_0(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_112,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_82,c_109])).

tff(c_115,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_83,c_112])).

tff(c_116,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_115])).

tff(c_117,plain,(
    ! [A_42,B_43,C_44] :
      ( k5_partfun1(A_42,B_43,C_44) = k1_tarski(C_44)
      | ~ v1_partfun1(C_44,A_42)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_120,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_117])).

tff(c_123,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_3') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_116,c_120])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_123])).

tff(c_126,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_145,plain,(
    ! [A_48,B_49,C_50] :
      ( k5_partfun1(A_48,B_49,C_50) = k1_tarski(C_50)
      | ~ v1_partfun1(C_50,A_48)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_148,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_145])).

tff(c_151,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_3') = k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_126,c_148])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_151])).

%------------------------------------------------------------------------------
