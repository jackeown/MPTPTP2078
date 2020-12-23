%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:41 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 164 expanded)
%              Number of leaves         :   35 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :   89 ( 174 expanded)
%              Number of equality atoms :   54 ( 123 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_56,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_58,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_54,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_34,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [A_27] : m1_subset_1(k2_subset_1(A_27),k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_39,plain,(
    ! [A_27] : m1_subset_1(A_27,k1_zfmisc_1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_901,plain,(
    ! [A_89,B_90,C_91] :
      ( k4_subset_1(A_89,B_90,C_91) = k2_xboole_0(B_90,C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_89))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2290,plain,(
    ! [A_116,B_117] :
      ( k4_subset_1(A_116,B_117,A_116) = k2_xboole_0(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_116)) ) ),
    inference(resolution,[status(thm)],[c_39,c_901])).

tff(c_2297,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_2290])).

tff(c_36,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_36])).

tff(c_2307,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2297,c_40])).

tff(c_20,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_133,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_158,plain,(
    ! [B_50,A_51] : k3_tarski(k2_tarski(B_50,A_51)) = k2_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_133])).

tff(c_26,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_181,plain,(
    ! [B_52,A_53] : k2_xboole_0(B_52,A_53) = k2_xboole_0(A_53,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_26])).

tff(c_12,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_203,plain,(
    ! [A_53] : k2_xboole_0(k1_xboole_0,A_53) = A_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_12])).

tff(c_164,plain,(
    ! [B_50,A_51] : k2_xboole_0(B_50,A_51) = k2_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_26])).

tff(c_79,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k2_xboole_0(A_39,B_40)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_86,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_79])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_441,plain,(
    ! [A_65,B_66] :
      ( ~ r2_hidden('#skF_1'(A_65,B_66),B_66)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_447,plain,(
    ! [A_67] : r1_tarski(A_67,A_67) ),
    inference(resolution,[status(thm)],[c_6,c_441])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_452,plain,(
    ! [A_68] : k3_xboole_0(A_68,A_68) = A_68 ),
    inference(resolution,[status(thm)],[c_447,c_14])).

tff(c_10,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_458,plain,(
    ! [A_68] : k5_xboole_0(A_68,A_68) = k4_xboole_0(A_68,A_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_10])).

tff(c_463,plain,(
    ! [A_68] : k5_xboole_0(A_68,A_68) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_458])).

tff(c_821,plain,(
    ! [C_84,A_85,B_86] :
      ( r2_hidden(C_84,A_85)
      | ~ r2_hidden(C_84,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2312,plain,(
    ! [A_119,B_120,A_121] :
      ( r2_hidden('#skF_1'(A_119,B_120),A_121)
      | ~ m1_subset_1(A_119,k1_zfmisc_1(A_121))
      | r1_tarski(A_119,B_120) ) ),
    inference(resolution,[status(thm)],[c_6,c_821])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2324,plain,(
    ! [A_122,A_123] :
      ( ~ m1_subset_1(A_122,k1_zfmisc_1(A_123))
      | r1_tarski(A_122,A_123) ) ),
    inference(resolution,[status(thm)],[c_2312,c_4])).

tff(c_2333,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_2324])).

tff(c_2337,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2333,c_14])).

tff(c_2341,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2337,c_10])).

tff(c_2344,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_2341])).

tff(c_8,plain,(
    ! [A_6] : k2_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_287,plain,(
    ! [A_57,B_58] : k2_xboole_0(A_57,k4_xboole_0(B_58,A_57)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_310,plain,(
    ! [A_15,B_16] : k2_xboole_0(k2_xboole_0(A_15,B_16),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_15,B_16),A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_287])).

tff(c_472,plain,(
    ! [A_70,B_71] : k2_xboole_0(k2_xboole_0(A_70,B_71),A_70) = k2_xboole_0(A_70,B_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_310])).

tff(c_317,plain,(
    ! [A_15,B_16] : k2_xboole_0(k2_xboole_0(A_15,B_16),A_15) = k2_xboole_0(A_15,B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_310])).

tff(c_475,plain,(
    ! [A_70,B_71] : k2_xboole_0(k2_xboole_0(A_70,B_71),k2_xboole_0(A_70,B_71)) = k2_xboole_0(k2_xboole_0(A_70,B_71),A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_317])).

tff(c_531,plain,(
    ! [A_70,B_71] : k2_xboole_0(A_70,k2_xboole_0(A_70,B_71)) = k2_xboole_0(A_70,B_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_8,c_475])).

tff(c_16,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_389,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k2_xboole_0(B_64,A_63)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_18])).

tff(c_397,plain,(
    ! [B_64,A_63] : k2_xboole_0(k2_xboole_0(B_64,A_63),k1_xboole_0) = k2_xboole_0(k2_xboole_0(B_64,A_63),A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_16])).

tff(c_1011,plain,(
    ! [B_94,A_95] : k2_xboole_0(k2_xboole_0(B_94,A_95),A_95) = k2_xboole_0(B_94,A_95) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_397])).

tff(c_1498,plain,(
    ! [B_103,A_104] : k2_xboole_0(k2_xboole_0(B_103,A_104),B_103) = k2_xboole_0(A_104,B_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_1011])).

tff(c_1679,plain,(
    ! [B_108,A_109] : k2_xboole_0(B_108,k2_xboole_0(B_108,A_109)) = k2_xboole_0(A_109,B_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_1498,c_164])).

tff(c_1783,plain,(
    ! [B_14,A_13] : k2_xboole_0(k4_xboole_0(B_14,A_13),A_13) = k2_xboole_0(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1679])).

tff(c_1831,plain,(
    ! [B_14,A_13] : k2_xboole_0(k4_xboole_0(B_14,A_13),A_13) = k2_xboole_0(A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_1783])).

tff(c_2352,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_2') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2344,c_1831])).

tff(c_2371,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_164,c_2352])).

tff(c_2373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2307,c_2371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 18:22:34 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.58  
% 3.56/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.58  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.56/1.58  
% 3.56/1.58  %Foreground sorts:
% 3.56/1.58  
% 3.56/1.58  
% 3.56/1.58  %Background operators:
% 3.56/1.58  
% 3.56/1.58  
% 3.56/1.58  %Foreground operators:
% 3.56/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.56/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.56/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.56/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.56/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.56/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.56/1.58  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.56/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.56/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.56/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.56/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.56/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.56/1.58  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.56/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.58  
% 3.56/1.59  tff(f_76, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 3.56/1.59  tff(f_56, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.56/1.59  tff(f_58, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.56/1.59  tff(f_71, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.56/1.59  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.56/1.59  tff(f_54, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.56/1.59  tff(f_38, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.56/1.59  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.56/1.59  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.56/1.59  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.56/1.59  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.56/1.59  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.56/1.59  tff(f_34, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.56/1.59  tff(f_44, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.56/1.59  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.56/1.59  tff(c_28, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.56/1.59  tff(c_30, plain, (![A_27]: (m1_subset_1(k2_subset_1(A_27), k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.56/1.59  tff(c_39, plain, (![A_27]: (m1_subset_1(A_27, k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 3.56/1.59  tff(c_901, plain, (![A_89, B_90, C_91]: (k4_subset_1(A_89, B_90, C_91)=k2_xboole_0(B_90, C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(A_89)) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.56/1.59  tff(c_2290, plain, (![A_116, B_117]: (k4_subset_1(A_116, B_117, A_116)=k2_xboole_0(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(A_116)))), inference(resolution, [status(thm)], [c_39, c_901])).
% 3.56/1.59  tff(c_2297, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_2290])).
% 3.56/1.59  tff(c_36, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.56/1.59  tff(c_40, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_36])).
% 3.56/1.59  tff(c_2307, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2297, c_40])).
% 3.56/1.59  tff(c_20, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.56/1.59  tff(c_133, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.56/1.59  tff(c_158, plain, (![B_50, A_51]: (k3_tarski(k2_tarski(B_50, A_51))=k2_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_20, c_133])).
% 3.56/1.59  tff(c_26, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.56/1.59  tff(c_181, plain, (![B_52, A_53]: (k2_xboole_0(B_52, A_53)=k2_xboole_0(A_53, B_52))), inference(superposition, [status(thm), theory('equality')], [c_158, c_26])).
% 3.56/1.59  tff(c_12, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.56/1.59  tff(c_203, plain, (![A_53]: (k2_xboole_0(k1_xboole_0, A_53)=A_53)), inference(superposition, [status(thm), theory('equality')], [c_181, c_12])).
% 3.56/1.59  tff(c_164, plain, (![B_50, A_51]: (k2_xboole_0(B_50, A_51)=k2_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_158, c_26])).
% 3.56/1.59  tff(c_79, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k2_xboole_0(A_39, B_40))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.56/1.59  tff(c_86, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_79])).
% 3.56/1.59  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.56/1.59  tff(c_441, plain, (![A_65, B_66]: (~r2_hidden('#skF_1'(A_65, B_66), B_66) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.56/1.59  tff(c_447, plain, (![A_67]: (r1_tarski(A_67, A_67))), inference(resolution, [status(thm)], [c_6, c_441])).
% 3.56/1.59  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.56/1.59  tff(c_452, plain, (![A_68]: (k3_xboole_0(A_68, A_68)=A_68)), inference(resolution, [status(thm)], [c_447, c_14])).
% 3.56/1.59  tff(c_10, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.56/1.59  tff(c_458, plain, (![A_68]: (k5_xboole_0(A_68, A_68)=k4_xboole_0(A_68, A_68))), inference(superposition, [status(thm), theory('equality')], [c_452, c_10])).
% 3.56/1.59  tff(c_463, plain, (![A_68]: (k5_xboole_0(A_68, A_68)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_458])).
% 3.56/1.59  tff(c_821, plain, (![C_84, A_85, B_86]: (r2_hidden(C_84, A_85) | ~r2_hidden(C_84, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.56/1.59  tff(c_2312, plain, (![A_119, B_120, A_121]: (r2_hidden('#skF_1'(A_119, B_120), A_121) | ~m1_subset_1(A_119, k1_zfmisc_1(A_121)) | r1_tarski(A_119, B_120))), inference(resolution, [status(thm)], [c_6, c_821])).
% 3.56/1.59  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.56/1.59  tff(c_2324, plain, (![A_122, A_123]: (~m1_subset_1(A_122, k1_zfmisc_1(A_123)) | r1_tarski(A_122, A_123))), inference(resolution, [status(thm)], [c_2312, c_4])).
% 3.56/1.59  tff(c_2333, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_2324])).
% 3.56/1.59  tff(c_2337, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_2333, c_14])).
% 3.56/1.59  tff(c_2341, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2337, c_10])).
% 3.56/1.59  tff(c_2344, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_463, c_2341])).
% 3.56/1.59  tff(c_8, plain, (![A_6]: (k2_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.56/1.59  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.56/1.59  tff(c_287, plain, (![A_57, B_58]: (k2_xboole_0(A_57, k4_xboole_0(B_58, A_57))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.56/1.59  tff(c_310, plain, (![A_15, B_16]: (k2_xboole_0(k2_xboole_0(A_15, B_16), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_15, B_16), A_15))), inference(superposition, [status(thm), theory('equality')], [c_18, c_287])).
% 3.56/1.59  tff(c_472, plain, (![A_70, B_71]: (k2_xboole_0(k2_xboole_0(A_70, B_71), A_70)=k2_xboole_0(A_70, B_71))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_310])).
% 3.56/1.59  tff(c_317, plain, (![A_15, B_16]: (k2_xboole_0(k2_xboole_0(A_15, B_16), A_15)=k2_xboole_0(A_15, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_310])).
% 3.56/1.59  tff(c_475, plain, (![A_70, B_71]: (k2_xboole_0(k2_xboole_0(A_70, B_71), k2_xboole_0(A_70, B_71))=k2_xboole_0(k2_xboole_0(A_70, B_71), A_70))), inference(superposition, [status(thm), theory('equality')], [c_472, c_317])).
% 3.56/1.59  tff(c_531, plain, (![A_70, B_71]: (k2_xboole_0(A_70, k2_xboole_0(A_70, B_71))=k2_xboole_0(A_70, B_71))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_8, c_475])).
% 3.56/1.59  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.56/1.59  tff(c_389, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k2_xboole_0(B_64, A_63))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_181, c_18])).
% 3.56/1.59  tff(c_397, plain, (![B_64, A_63]: (k2_xboole_0(k2_xboole_0(B_64, A_63), k1_xboole_0)=k2_xboole_0(k2_xboole_0(B_64, A_63), A_63))), inference(superposition, [status(thm), theory('equality')], [c_389, c_16])).
% 3.56/1.59  tff(c_1011, plain, (![B_94, A_95]: (k2_xboole_0(k2_xboole_0(B_94, A_95), A_95)=k2_xboole_0(B_94, A_95))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_397])).
% 3.56/1.59  tff(c_1498, plain, (![B_103, A_104]: (k2_xboole_0(k2_xboole_0(B_103, A_104), B_103)=k2_xboole_0(A_104, B_103))), inference(superposition, [status(thm), theory('equality')], [c_164, c_1011])).
% 3.56/1.59  tff(c_1679, plain, (![B_108, A_109]: (k2_xboole_0(B_108, k2_xboole_0(B_108, A_109))=k2_xboole_0(A_109, B_108))), inference(superposition, [status(thm), theory('equality')], [c_1498, c_164])).
% 3.56/1.59  tff(c_1783, plain, (![B_14, A_13]: (k2_xboole_0(k4_xboole_0(B_14, A_13), A_13)=k2_xboole_0(A_13, k2_xboole_0(A_13, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1679])).
% 3.56/1.59  tff(c_1831, plain, (![B_14, A_13]: (k2_xboole_0(k4_xboole_0(B_14, A_13), A_13)=k2_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_531, c_1783])).
% 3.56/1.59  tff(c_2352, plain, (k2_xboole_0(k1_xboole_0, '#skF_2')=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2344, c_1831])).
% 3.56/1.59  tff(c_2371, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_203, c_164, c_2352])).
% 3.56/1.59  tff(c_2373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2307, c_2371])).
% 3.56/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.59  
% 3.56/1.59  Inference rules
% 3.56/1.59  ----------------------
% 3.56/1.59  #Ref     : 0
% 3.56/1.59  #Sup     : 581
% 3.56/1.59  #Fact    : 0
% 3.56/1.59  #Define  : 0
% 3.56/1.59  #Split   : 0
% 3.56/1.59  #Chain   : 0
% 3.56/1.59  #Close   : 0
% 3.56/1.59  
% 3.56/1.59  Ordering : KBO
% 3.56/1.59  
% 3.56/1.59  Simplification rules
% 3.56/1.59  ----------------------
% 3.56/1.59  #Subsume      : 21
% 3.56/1.59  #Demod        : 699
% 3.56/1.59  #Tautology    : 433
% 3.56/1.59  #SimpNegUnit  : 1
% 3.56/1.59  #BackRed      : 1
% 3.56/1.59  
% 3.56/1.59  #Partial instantiations: 0
% 3.56/1.59  #Strategies tried      : 1
% 3.56/1.59  
% 3.56/1.59  Timing (in seconds)
% 3.56/1.59  ----------------------
% 3.56/1.60  Preprocessing        : 0.31
% 3.56/1.60  Parsing              : 0.17
% 3.56/1.60  CNF conversion       : 0.02
% 3.56/1.60  Main loop            : 0.53
% 3.56/1.60  Inferencing          : 0.16
% 3.56/1.60  Reduction            : 0.26
% 3.56/1.60  Demodulation         : 0.22
% 3.56/1.60  BG Simplification    : 0.02
% 3.56/1.60  Subsumption          : 0.07
% 3.56/1.60  Abstraction          : 0.03
% 3.56/1.60  MUC search           : 0.00
% 3.56/1.60  Cooper               : 0.00
% 3.56/1.60  Total                : 0.87
% 3.56/1.60  Index Insertion      : 0.00
% 3.56/1.60  Index Deletion       : 0.00
% 3.56/1.60  Index Matching       : 0.00
% 3.56/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
