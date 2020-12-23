%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:26 EST 2020

% Result     : Theorem 13.41s
% Output     : CNFRefutation 13.55s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 192 expanded)
%              Number of leaves         :   43 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :   99 ( 250 expanded)
%              Number of equality atoms :   60 ( 125 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_64,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_90,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_52,plain,(
    ! [A_39] : k2_subset_1(A_39) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_62,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_65,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_62])).

tff(c_20,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [B_24,A_23] : k2_tarski(B_24,A_23) = k2_tarski(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_250,plain,(
    ! [A_68,B_69] : k3_tarski(k2_tarski(A_68,B_69)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_285,plain,(
    ! [A_78,B_79] : k3_tarski(k2_tarski(A_78,B_79)) = k2_xboole_0(B_79,A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_250])).

tff(c_42,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_291,plain,(
    ! [B_79,A_78] : k2_xboole_0(B_79,A_78) = k2_xboole_0(A_78,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_42])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_58,plain,(
    ! [A_44] : ~ v1_xboole_0(k1_zfmisc_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_471,plain,(
    ! [B_93,A_94] :
      ( r2_hidden(B_93,A_94)
      | ~ m1_subset_1(B_93,A_94)
      | v1_xboole_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [C_34,A_30] :
      ( r1_tarski(C_34,A_30)
      | ~ r2_hidden(C_34,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_478,plain,(
    ! [B_93,A_30] :
      ( r1_tarski(B_93,A_30)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_30))
      | v1_xboole_0(k1_zfmisc_1(A_30)) ) ),
    inference(resolution,[status(thm)],[c_471,c_30])).

tff(c_488,plain,(
    ! [B_97,A_98] :
      ( r1_tarski(B_97,A_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_98)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_478])).

tff(c_501,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_488])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_505,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_501,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_127,plain,(
    ! [A_54,B_55] : k2_xboole_0(A_54,k3_xboole_0(A_54,B_55)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_127])).

tff(c_518,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_136])).

tff(c_551,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_518])).

tff(c_1130,plain,(
    ! [A_115,B_116] :
      ( k4_xboole_0(A_115,B_116) = k3_subset_1(A_115,B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1143,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1130])).

tff(c_347,plain,(
    ! [A_82,B_83] : k5_xboole_0(A_82,k3_xboole_0(A_82,B_83)) = k4_xboole_0(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1246,plain,(
    ! [B_119,A_120] : k5_xboole_0(B_119,k3_xboole_0(A_120,B_119)) = k4_xboole_0(B_119,A_120) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_347])).

tff(c_1282,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_1246])).

tff(c_1304,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1143,c_1282])).

tff(c_22,plain,(
    ! [A_21,B_22] : k5_xboole_0(k5_xboole_0(A_21,B_22),k3_xboole_0(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1312,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1304,c_22])).

tff(c_1315,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_505,c_291,c_2,c_1312])).

tff(c_18,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1147,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_18])).

tff(c_1150,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_2,c_1147])).

tff(c_308,plain,(
    ! [B_80,A_81] : k2_xboole_0(B_80,A_81) = k2_xboole_0(A_81,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_42])).

tff(c_16,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_383,plain,(
    ! [A_85,B_86] : k4_xboole_0(A_85,k2_xboole_0(B_86,A_85)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_16])).

tff(c_399,plain,(
    ! [B_2,A_1] : k4_xboole_0(k3_xboole_0(B_2,A_1),A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_383])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2255,plain,(
    ! [A_137,B_138,C_139] : k5_xboole_0(k3_xboole_0(A_137,B_138),k3_xboole_0(C_139,B_138)) = k3_xboole_0(k5_xboole_0(A_137,C_139),B_138) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2272,plain,(
    ! [A_137,B_138] : k3_xboole_0(k5_xboole_0(A_137,k3_xboole_0(A_137,B_138)),B_138) = k4_xboole_0(k3_xboole_0(A_137,B_138),B_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_2255,c_8])).

tff(c_2362,plain,(
    ! [B_140,A_141] : k3_xboole_0(B_140,k4_xboole_0(A_141,B_140)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_2,c_8,c_2272])).

tff(c_2414,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1150,c_2362])).

tff(c_2647,plain,(
    k5_xboole_0(k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4'),k1_xboole_0) = k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2414,c_22])).

tff(c_2683,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1315,c_291,c_2647])).

tff(c_56,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k3_subset_1(A_42,B_43),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5488,plain,(
    ! [A_184,B_185,C_186] :
      ( k4_subset_1(A_184,B_185,C_186) = k2_xboole_0(B_185,C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(A_184))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(A_184)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18549,plain,(
    ! [A_304,B_305,B_306] :
      ( k4_subset_1(A_304,B_305,k3_subset_1(A_304,B_306)) = k2_xboole_0(B_305,k3_subset_1(A_304,B_306))
      | ~ m1_subset_1(B_305,k1_zfmisc_1(A_304))
      | ~ m1_subset_1(B_306,k1_zfmisc_1(A_304)) ) ),
    inference(resolution,[status(thm)],[c_56,c_5488])).

tff(c_18828,plain,(
    ! [B_309] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_309)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_309))
      | ~ m1_subset_1(B_309,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_64,c_18549])).

tff(c_18851,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_64,c_18828])).

tff(c_18863,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2683,c_18851])).

tff(c_18865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_18863])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.41/5.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.55/5.86  
% 13.55/5.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.55/5.86  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 13.55/5.86  
% 13.55/5.86  %Foreground sorts:
% 13.55/5.86  
% 13.55/5.86  
% 13.55/5.86  %Background operators:
% 13.55/5.86  
% 13.55/5.86  
% 13.55/5.86  %Foreground operators:
% 13.55/5.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.55/5.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.55/5.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.55/5.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.55/5.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.55/5.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.55/5.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.55/5.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.55/5.86  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 13.55/5.86  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 13.55/5.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.55/5.86  tff('#skF_3', type, '#skF_3': $i).
% 13.55/5.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.55/5.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.55/5.86  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.55/5.86  tff('#skF_4', type, '#skF_4': $i).
% 13.55/5.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.55/5.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 13.55/5.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.55/5.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.55/5.86  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.55/5.86  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 13.55/5.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.55/5.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.55/5.86  
% 13.55/5.88  tff(f_79, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 13.55/5.88  tff(f_101, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 13.55/5.88  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 13.55/5.88  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.55/5.88  tff(f_64, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 13.55/5.88  tff(f_90, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 13.55/5.88  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 13.55/5.88  tff(f_62, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 13.55/5.88  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.55/5.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.55/5.88  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 13.55/5.88  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 13.55/5.88  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.55/5.88  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 13.55/5.88  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.55/5.88  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 13.55/5.88  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 13.55/5.88  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 13.55/5.88  tff(f_96, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 13.55/5.88  tff(c_52, plain, (![A_39]: (k2_subset_1(A_39)=A_39)), inference(cnfTransformation, [status(thm)], [f_79])).
% 13.55/5.88  tff(c_62, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.55/5.88  tff(c_65, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_62])).
% 13.55/5.88  tff(c_20, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.55/5.88  tff(c_24, plain, (![B_24, A_23]: (k2_tarski(B_24, A_23)=k2_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.55/5.88  tff(c_250, plain, (![A_68, B_69]: (k3_tarski(k2_tarski(A_68, B_69))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.55/5.88  tff(c_285, plain, (![A_78, B_79]: (k3_tarski(k2_tarski(A_78, B_79))=k2_xboole_0(B_79, A_78))), inference(superposition, [status(thm), theory('equality')], [c_24, c_250])).
% 13.55/5.88  tff(c_42, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.55/5.88  tff(c_291, plain, (![B_79, A_78]: (k2_xboole_0(B_79, A_78)=k2_xboole_0(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_285, c_42])).
% 13.55/5.88  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.55/5.88  tff(c_58, plain, (![A_44]: (~v1_xboole_0(k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.55/5.88  tff(c_471, plain, (![B_93, A_94]: (r2_hidden(B_93, A_94) | ~m1_subset_1(B_93, A_94) | v1_xboole_0(A_94))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.55/5.88  tff(c_30, plain, (![C_34, A_30]: (r1_tarski(C_34, A_30) | ~r2_hidden(C_34, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.55/5.88  tff(c_478, plain, (![B_93, A_30]: (r1_tarski(B_93, A_30) | ~m1_subset_1(B_93, k1_zfmisc_1(A_30)) | v1_xboole_0(k1_zfmisc_1(A_30)))), inference(resolution, [status(thm)], [c_471, c_30])).
% 13.55/5.88  tff(c_488, plain, (![B_97, A_98]: (r1_tarski(B_97, A_98) | ~m1_subset_1(B_97, k1_zfmisc_1(A_98)))), inference(negUnitSimplification, [status(thm)], [c_58, c_478])).
% 13.55/5.88  tff(c_501, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_488])).
% 13.55/5.88  tff(c_14, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.55/5.88  tff(c_505, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_501, c_14])).
% 13.55/5.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.55/5.88  tff(c_127, plain, (![A_54, B_55]: (k2_xboole_0(A_54, k3_xboole_0(A_54, B_55))=A_54)), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.55/5.88  tff(c_136, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_127])).
% 13.55/5.88  tff(c_518, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_505, c_136])).
% 13.55/5.88  tff(c_551, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_291, c_518])).
% 13.55/5.88  tff(c_1130, plain, (![A_115, B_116]: (k4_xboole_0(A_115, B_116)=k3_subset_1(A_115, B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.55/5.88  tff(c_1143, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_1130])).
% 13.55/5.88  tff(c_347, plain, (![A_82, B_83]: (k5_xboole_0(A_82, k3_xboole_0(A_82, B_83))=k4_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.55/5.88  tff(c_1246, plain, (![B_119, A_120]: (k5_xboole_0(B_119, k3_xboole_0(A_120, B_119))=k4_xboole_0(B_119, A_120))), inference(superposition, [status(thm), theory('equality')], [c_2, c_347])).
% 13.55/5.88  tff(c_1282, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_505, c_1246])).
% 13.55/5.88  tff(c_1304, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1143, c_1282])).
% 13.55/5.88  tff(c_22, plain, (![A_21, B_22]: (k5_xboole_0(k5_xboole_0(A_21, B_22), k3_xboole_0(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.55/5.88  tff(c_1312, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1304, c_22])).
% 13.55/5.88  tff(c_1315, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_551, c_505, c_291, c_2, c_1312])).
% 13.55/5.88  tff(c_18, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.55/5.88  tff(c_1147, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1143, c_18])).
% 13.55/5.88  tff(c_1150, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_505, c_2, c_1147])).
% 13.55/5.88  tff(c_308, plain, (![B_80, A_81]: (k2_xboole_0(B_80, A_81)=k2_xboole_0(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_285, c_42])).
% 13.55/5.88  tff(c_16, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.55/5.88  tff(c_383, plain, (![A_85, B_86]: (k4_xboole_0(A_85, k2_xboole_0(B_86, A_85))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_308, c_16])).
% 13.55/5.88  tff(c_399, plain, (![B_2, A_1]: (k4_xboole_0(k3_xboole_0(B_2, A_1), A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_136, c_383])).
% 13.55/5.88  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.55/5.88  tff(c_2255, plain, (![A_137, B_138, C_139]: (k5_xboole_0(k3_xboole_0(A_137, B_138), k3_xboole_0(C_139, B_138))=k3_xboole_0(k5_xboole_0(A_137, C_139), B_138))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.55/5.88  tff(c_2272, plain, (![A_137, B_138]: (k3_xboole_0(k5_xboole_0(A_137, k3_xboole_0(A_137, B_138)), B_138)=k4_xboole_0(k3_xboole_0(A_137, B_138), B_138))), inference(superposition, [status(thm), theory('equality')], [c_2255, c_8])).
% 13.55/5.88  tff(c_2362, plain, (![B_140, A_141]: (k3_xboole_0(B_140, k4_xboole_0(A_141, B_140))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_399, c_2, c_8, c_2272])).
% 13.55/5.88  tff(c_2414, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1150, c_2362])).
% 13.55/5.88  tff(c_2647, plain, (k5_xboole_0(k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4'), k1_xboole_0)=k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2414, c_22])).
% 13.55/5.88  tff(c_2683, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1315, c_291, c_2647])).
% 13.55/5.88  tff(c_56, plain, (![A_42, B_43]: (m1_subset_1(k3_subset_1(A_42, B_43), k1_zfmisc_1(A_42)) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.55/5.88  tff(c_5488, plain, (![A_184, B_185, C_186]: (k4_subset_1(A_184, B_185, C_186)=k2_xboole_0(B_185, C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(A_184)) | ~m1_subset_1(B_185, k1_zfmisc_1(A_184)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.55/5.88  tff(c_18549, plain, (![A_304, B_305, B_306]: (k4_subset_1(A_304, B_305, k3_subset_1(A_304, B_306))=k2_xboole_0(B_305, k3_subset_1(A_304, B_306)) | ~m1_subset_1(B_305, k1_zfmisc_1(A_304)) | ~m1_subset_1(B_306, k1_zfmisc_1(A_304)))), inference(resolution, [status(thm)], [c_56, c_5488])).
% 13.55/5.88  tff(c_18828, plain, (![B_309]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_309))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_309)) | ~m1_subset_1(B_309, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_64, c_18549])).
% 13.55/5.88  tff(c_18851, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_18828])).
% 13.55/5.88  tff(c_18863, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2683, c_18851])).
% 13.55/5.88  tff(c_18865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_18863])).
% 13.55/5.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.55/5.88  
% 13.55/5.88  Inference rules
% 13.55/5.88  ----------------------
% 13.55/5.88  #Ref     : 0
% 13.55/5.88  #Sup     : 4734
% 13.55/5.89  #Fact    : 0
% 13.55/5.89  #Define  : 0
% 13.55/5.89  #Split   : 0
% 13.55/5.89  #Chain   : 0
% 13.55/5.89  #Close   : 0
% 13.55/5.89  
% 13.55/5.89  Ordering : KBO
% 13.55/5.89  
% 13.55/5.89  Simplification rules
% 13.55/5.89  ----------------------
% 13.55/5.89  #Subsume      : 88
% 13.55/5.89  #Demod        : 6352
% 13.55/5.89  #Tautology    : 3249
% 13.55/5.89  #SimpNegUnit  : 22
% 13.55/5.89  #BackRed      : 2
% 13.55/5.89  
% 13.55/5.89  #Partial instantiations: 0
% 13.55/5.89  #Strategies tried      : 1
% 13.55/5.89  
% 13.55/5.89  Timing (in seconds)
% 13.55/5.89  ----------------------
% 13.71/5.89  Preprocessing        : 0.54
% 13.71/5.89  Parsing              : 0.27
% 13.71/5.89  CNF conversion       : 0.04
% 13.71/5.89  Main loop            : 4.41
% 13.71/5.89  Inferencing          : 0.88
% 13.71/5.89  Reduction            : 2.52
% 13.71/5.89  Demodulation         : 2.21
% 13.71/5.89  BG Simplification    : 0.13
% 13.71/5.89  Subsumption          : 0.68
% 13.71/5.89  Abstraction          : 0.18
% 13.71/5.89  MUC search           : 0.00
% 13.71/5.89  Cooper               : 0.00
% 13.71/5.89  Total                : 5.01
% 13.71/5.89  Index Insertion      : 0.00
% 13.71/5.89  Index Deletion       : 0.00
% 13.71/5.89  Index Matching       : 0.00
% 13.71/5.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
