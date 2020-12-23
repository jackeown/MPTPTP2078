%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:33 EST 2020

% Result     : Theorem 14.35s
% Output     : CNFRefutation 14.47s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 213 expanded)
%              Number of leaves         :   39 (  88 expanded)
%              Depth                    :   22
%              Number of atoms          :   99 ( 319 expanded)
%              Number of equality atoms :   44 ( 117 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k6_subset_1(k1_relat_1(B),k1_relat_1(k7_relat_1(B,A))) = k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t213_relat_1)).

tff(f_60,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_91,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_54,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_58,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

tff(c_78,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_50,plain,(
    ! [A_24,B_25] : k6_subset_1(A_24,B_25) = k4_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_66,plain,(
    ! [B_50,A_49] :
      ( k1_relat_1(k6_subset_1(B_50,k7_relat_1(B_50,A_49))) = k6_subset_1(k1_relat_1(B_50),A_49)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_79,plain,(
    ! [B_50,A_49] :
      ( k1_relat_1(k4_xboole_0(B_50,k7_relat_1(B_50,A_49))) = k4_xboole_0(k1_relat_1(B_50),A_49)
      | ~ v1_relat_1(B_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_66])).

tff(c_74,plain,(
    ! [B_54,A_53] :
      ( k3_xboole_0(k1_relat_1(B_54),A_53) = k1_relat_1(k7_relat_1(B_54,A_53))
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_155,plain,(
    ! [A_64] :
      ( k7_relat_1(A_64,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_163,plain,(
    k7_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_155])).

tff(c_58,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(k7_relat_1(A_43,B_44))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_167,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_58])).

tff(c_171,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_167])).

tff(c_1000,plain,(
    ! [A_127,B_128] :
      ( r2_hidden(k4_tarski('#skF_5'(A_127,B_128),'#skF_6'(A_127,B_128)),A_127)
      | r1_tarski(A_127,B_128)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_70,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_187,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(k7_relat_1(B_67,A_68),B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    ! [A_18,B_19] :
      ( k2_xboole_0(A_18,B_19) = B_19
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_332,plain,(
    ! [B_89,A_90] :
      ( k2_xboole_0(k7_relat_1(B_89,A_90),B_89) = B_89
      | ~ v1_relat_1(B_89) ) ),
    inference(resolution,[status(thm)],[c_187,c_42])).

tff(c_44,plain,(
    ! [A_20] : k2_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_342,plain,(
    ! [A_90] :
      ( k7_relat_1(k1_xboole_0,A_90) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_44])).

tff(c_358,plain,(
    ! [A_90] : k7_relat_1(k1_xboole_0,A_90) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_342])).

tff(c_261,plain,(
    ! [B_85,A_86] :
      ( k3_xboole_0(k1_relat_1(B_85),A_86) = k1_relat_1(k7_relat_1(B_85,A_86))
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_290,plain,(
    ! [A_86] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_86)) = k3_xboole_0(k1_xboole_0,A_86)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_261])).

tff(c_294,plain,(
    ! [A_86] : k1_relat_1(k7_relat_1(k1_xboole_0,A_86)) = k3_xboole_0(k1_xboole_0,A_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_290])).

tff(c_366,plain,(
    ! [A_86] : k3_xboole_0(k1_xboole_0,A_86) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_294])).

tff(c_393,plain,(
    ! [A_92] : k3_xboole_0(k1_xboole_0,A_92) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_366])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_398,plain,(
    ! [D_8,A_92] :
      ( r2_hidden(D_8,A_92)
      | ~ r2_hidden(D_8,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_6])).

tff(c_1018,plain,(
    ! [B_128,A_92] :
      ( r2_hidden(k4_tarski('#skF_5'(k1_xboole_0,B_128),'#skF_6'(k1_xboole_0,B_128)),A_92)
      | r1_tarski(k1_xboole_0,B_128)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1000,c_398])).

tff(c_1661,plain,(
    ! [B_178,A_179] :
      ( r2_hidden(k4_tarski('#skF_5'(k1_xboole_0,B_178),'#skF_6'(k1_xboole_0,B_178)),A_179)
      | r1_tarski(k1_xboole_0,B_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_1018])).

tff(c_54,plain,(
    ! [A_26,B_36] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_26,B_36),'#skF_6'(A_26,B_36)),B_36)
      | r1_tarski(A_26,B_36)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1694,plain,(
    ! [A_179] :
      ( ~ v1_relat_1(k1_xboole_0)
      | r1_tarski(k1_xboole_0,A_179) ) ),
    inference(resolution,[status(thm)],[c_1661,c_54])).

tff(c_1775,plain,(
    ! [A_181] : r1_tarski(k1_xboole_0,A_181) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_1694])).

tff(c_1779,plain,(
    ! [A_181] : k2_xboole_0(k1_xboole_0,A_181) = A_181 ),
    inference(resolution,[status(thm)],[c_1775,c_42])).

tff(c_48,plain,(
    ! [A_23] : k4_xboole_0(k1_xboole_0,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1784,plain,(
    ! [A_182] : k2_xboole_0(k1_xboole_0,A_182) = A_182 ),
    inference(resolution,[status(thm)],[c_1775,c_42])).

tff(c_46,plain,(
    ! [A_21,B_22] : k4_xboole_0(k2_xboole_0(A_21,B_22),B_22) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1796,plain,(
    ! [A_182] : k4_xboole_0(k1_xboole_0,A_182) = k4_xboole_0(A_182,A_182) ),
    inference(superposition,[status(thm),theory(equality)],[c_1784,c_46])).

tff(c_1818,plain,(
    ! [A_183] : k4_xboole_0(A_183,A_183) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1796])).

tff(c_40,plain,(
    ! [A_15,B_16,C_17] : k2_xboole_0(k4_xboole_0(A_15,B_16),k4_xboole_0(A_15,C_17)) = k4_xboole_0(A_15,k3_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1839,plain,(
    ! [A_183,C_17] : k4_xboole_0(A_183,k3_xboole_0(A_183,C_17)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(A_183,C_17)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1818,c_40])).

tff(c_2164,plain,(
    ! [A_191,C_192] : k4_xboole_0(A_191,k3_xboole_0(A_191,C_192)) = k4_xboole_0(A_191,C_192) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1779,c_1839])).

tff(c_38766,plain,(
    ! [B_727,A_728] :
      ( k4_xboole_0(k1_relat_1(B_727),k1_relat_1(k7_relat_1(B_727,A_728))) = k4_xboole_0(k1_relat_1(B_727),A_728)
      | ~ v1_relat_1(B_727) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_2164])).

tff(c_76,plain,(
    k6_subset_1(k1_relat_1('#skF_8'),k1_relat_1(k7_relat_1('#skF_8','#skF_7'))) != k1_relat_1(k6_subset_1('#skF_8',k7_relat_1('#skF_8','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_80,plain,(
    k4_xboole_0(k1_relat_1('#skF_8'),k1_relat_1(k7_relat_1('#skF_8','#skF_7'))) != k1_relat_1(k4_xboole_0('#skF_8',k7_relat_1('#skF_8','#skF_7'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_76])).

tff(c_38950,plain,
    ( k1_relat_1(k4_xboole_0('#skF_8',k7_relat_1('#skF_8','#skF_7'))) != k4_xboole_0(k1_relat_1('#skF_8'),'#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_38766,c_80])).

tff(c_39016,plain,(
    k1_relat_1(k4_xboole_0('#skF_8',k7_relat_1('#skF_8','#skF_7'))) != k4_xboole_0(k1_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_38950])).

tff(c_39033,plain,(
    ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_39016])).

tff(c_39037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_39033])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:06:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.35/7.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.35/7.10  
% 14.35/7.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.35/7.10  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_5
% 14.35/7.10  
% 14.35/7.10  %Foreground sorts:
% 14.35/7.10  
% 14.35/7.10  
% 14.35/7.10  %Background operators:
% 14.35/7.10  
% 14.35/7.10  
% 14.35/7.10  %Foreground operators:
% 14.35/7.10  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 14.35/7.10  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 14.35/7.10  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.35/7.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.35/7.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.35/7.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.35/7.10  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 14.35/7.10  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 14.35/7.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.35/7.10  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 14.35/7.10  tff('#skF_7', type, '#skF_7': $i).
% 14.35/7.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.35/7.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.35/7.10  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 14.35/7.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.35/7.10  tff('#skF_8', type, '#skF_8': $i).
% 14.35/7.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.35/7.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.35/7.10  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.35/7.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.35/7.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.35/7.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.35/7.10  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 14.35/7.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.35/7.10  
% 14.47/7.11  tff(f_104, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k6_subset_1(k1_relat_1(B), k1_relat_1(k7_relat_1(B, A))) = k1_relat_1(k6_subset_1(B, k7_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t213_relat_1)).
% 14.47/7.11  tff(f_60, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 14.47/7.11  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 14.47/7.11  tff(f_99, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 14.47/7.11  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 14.47/7.11  tff(f_74, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 14.47/7.11  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 14.47/7.11  tff(f_91, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 14.47/7.11  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 14.47/7.11  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 14.47/7.11  tff(f_54, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 14.47/7.11  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 14.47/7.11  tff(f_58, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 14.47/7.11  tff(f_56, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 14.47/7.11  tff(f_48, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 14.47/7.11  tff(c_78, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.47/7.11  tff(c_50, plain, (![A_24, B_25]: (k6_subset_1(A_24, B_25)=k4_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_60])).
% 14.47/7.11  tff(c_66, plain, (![B_50, A_49]: (k1_relat_1(k6_subset_1(B_50, k7_relat_1(B_50, A_49)))=k6_subset_1(k1_relat_1(B_50), A_49) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_88])).
% 14.47/7.11  tff(c_79, plain, (![B_50, A_49]: (k1_relat_1(k4_xboole_0(B_50, k7_relat_1(B_50, A_49)))=k4_xboole_0(k1_relat_1(B_50), A_49) | ~v1_relat_1(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_66])).
% 14.47/7.11  tff(c_74, plain, (![B_54, A_53]: (k3_xboole_0(k1_relat_1(B_54), A_53)=k1_relat_1(k7_relat_1(B_54, A_53)) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.47/7.11  tff(c_155, plain, (![A_64]: (k7_relat_1(A_64, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_78])).
% 14.47/7.11  tff(c_163, plain, (k7_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_78, c_155])).
% 14.47/7.11  tff(c_58, plain, (![A_43, B_44]: (v1_relat_1(k7_relat_1(A_43, B_44)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.47/7.11  tff(c_167, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_163, c_58])).
% 14.47/7.11  tff(c_171, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_167])).
% 14.47/7.11  tff(c_1000, plain, (![A_127, B_128]: (r2_hidden(k4_tarski('#skF_5'(A_127, B_128), '#skF_6'(A_127, B_128)), A_127) | r1_tarski(A_127, B_128) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.47/7.11  tff(c_70, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 14.47/7.11  tff(c_187, plain, (![B_67, A_68]: (r1_tarski(k7_relat_1(B_67, A_68), B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.47/7.11  tff(c_42, plain, (![A_18, B_19]: (k2_xboole_0(A_18, B_19)=B_19 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.47/7.11  tff(c_332, plain, (![B_89, A_90]: (k2_xboole_0(k7_relat_1(B_89, A_90), B_89)=B_89 | ~v1_relat_1(B_89))), inference(resolution, [status(thm)], [c_187, c_42])).
% 14.47/7.11  tff(c_44, plain, (![A_20]: (k2_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_54])).
% 14.47/7.11  tff(c_342, plain, (![A_90]: (k7_relat_1(k1_xboole_0, A_90)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_332, c_44])).
% 14.47/7.11  tff(c_358, plain, (![A_90]: (k7_relat_1(k1_xboole_0, A_90)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_171, c_342])).
% 14.47/7.11  tff(c_261, plain, (![B_85, A_86]: (k3_xboole_0(k1_relat_1(B_85), A_86)=k1_relat_1(k7_relat_1(B_85, A_86)) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_99])).
% 14.47/7.11  tff(c_290, plain, (![A_86]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_86))=k3_xboole_0(k1_xboole_0, A_86) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_70, c_261])).
% 14.47/7.11  tff(c_294, plain, (![A_86]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_86))=k3_xboole_0(k1_xboole_0, A_86))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_290])).
% 14.47/7.11  tff(c_366, plain, (![A_86]: (k3_xboole_0(k1_xboole_0, A_86)=k1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_358, c_294])).
% 14.47/7.11  tff(c_393, plain, (![A_92]: (k3_xboole_0(k1_xboole_0, A_92)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_366])).
% 14.47/7.11  tff(c_6, plain, (![D_8, B_4, A_3]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 14.47/7.11  tff(c_398, plain, (![D_8, A_92]: (r2_hidden(D_8, A_92) | ~r2_hidden(D_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_393, c_6])).
% 14.47/7.11  tff(c_1018, plain, (![B_128, A_92]: (r2_hidden(k4_tarski('#skF_5'(k1_xboole_0, B_128), '#skF_6'(k1_xboole_0, B_128)), A_92) | r1_tarski(k1_xboole_0, B_128) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1000, c_398])).
% 14.47/7.11  tff(c_1661, plain, (![B_178, A_179]: (r2_hidden(k4_tarski('#skF_5'(k1_xboole_0, B_178), '#skF_6'(k1_xboole_0, B_178)), A_179) | r1_tarski(k1_xboole_0, B_178))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_1018])).
% 14.47/7.11  tff(c_54, plain, (![A_26, B_36]: (~r2_hidden(k4_tarski('#skF_5'(A_26, B_36), '#skF_6'(A_26, B_36)), B_36) | r1_tarski(A_26, B_36) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.47/7.11  tff(c_1694, plain, (![A_179]: (~v1_relat_1(k1_xboole_0) | r1_tarski(k1_xboole_0, A_179))), inference(resolution, [status(thm)], [c_1661, c_54])).
% 14.47/7.11  tff(c_1775, plain, (![A_181]: (r1_tarski(k1_xboole_0, A_181))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_1694])).
% 14.47/7.11  tff(c_1779, plain, (![A_181]: (k2_xboole_0(k1_xboole_0, A_181)=A_181)), inference(resolution, [status(thm)], [c_1775, c_42])).
% 14.47/7.11  tff(c_48, plain, (![A_23]: (k4_xboole_0(k1_xboole_0, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.47/7.11  tff(c_1784, plain, (![A_182]: (k2_xboole_0(k1_xboole_0, A_182)=A_182)), inference(resolution, [status(thm)], [c_1775, c_42])).
% 14.47/7.11  tff(c_46, plain, (![A_21, B_22]: (k4_xboole_0(k2_xboole_0(A_21, B_22), B_22)=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.47/7.11  tff(c_1796, plain, (![A_182]: (k4_xboole_0(k1_xboole_0, A_182)=k4_xboole_0(A_182, A_182))), inference(superposition, [status(thm), theory('equality')], [c_1784, c_46])).
% 14.47/7.11  tff(c_1818, plain, (![A_183]: (k4_xboole_0(A_183, A_183)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1796])).
% 14.47/7.11  tff(c_40, plain, (![A_15, B_16, C_17]: (k2_xboole_0(k4_xboole_0(A_15, B_16), k4_xboole_0(A_15, C_17))=k4_xboole_0(A_15, k3_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.47/7.11  tff(c_1839, plain, (![A_183, C_17]: (k4_xboole_0(A_183, k3_xboole_0(A_183, C_17))=k2_xboole_0(k1_xboole_0, k4_xboole_0(A_183, C_17)))), inference(superposition, [status(thm), theory('equality')], [c_1818, c_40])).
% 14.47/7.11  tff(c_2164, plain, (![A_191, C_192]: (k4_xboole_0(A_191, k3_xboole_0(A_191, C_192))=k4_xboole_0(A_191, C_192))), inference(demodulation, [status(thm), theory('equality')], [c_1779, c_1839])).
% 14.47/7.11  tff(c_38766, plain, (![B_727, A_728]: (k4_xboole_0(k1_relat_1(B_727), k1_relat_1(k7_relat_1(B_727, A_728)))=k4_xboole_0(k1_relat_1(B_727), A_728) | ~v1_relat_1(B_727))), inference(superposition, [status(thm), theory('equality')], [c_74, c_2164])).
% 14.47/7.11  tff(c_76, plain, (k6_subset_1(k1_relat_1('#skF_8'), k1_relat_1(k7_relat_1('#skF_8', '#skF_7')))!=k1_relat_1(k6_subset_1('#skF_8', k7_relat_1('#skF_8', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 14.47/7.11  tff(c_80, plain, (k4_xboole_0(k1_relat_1('#skF_8'), k1_relat_1(k7_relat_1('#skF_8', '#skF_7')))!=k1_relat_1(k4_xboole_0('#skF_8', k7_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_76])).
% 14.47/7.11  tff(c_38950, plain, (k1_relat_1(k4_xboole_0('#skF_8', k7_relat_1('#skF_8', '#skF_7')))!=k4_xboole_0(k1_relat_1('#skF_8'), '#skF_7') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_38766, c_80])).
% 14.47/7.11  tff(c_39016, plain, (k1_relat_1(k4_xboole_0('#skF_8', k7_relat_1('#skF_8', '#skF_7')))!=k4_xboole_0(k1_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_38950])).
% 14.47/7.11  tff(c_39033, plain, (~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_79, c_39016])).
% 14.47/7.11  tff(c_39037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_39033])).
% 14.47/7.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.47/7.11  
% 14.47/7.11  Inference rules
% 14.47/7.11  ----------------------
% 14.47/7.11  #Ref     : 0
% 14.47/7.11  #Sup     : 9344
% 14.47/7.11  #Fact    : 0
% 14.47/7.11  #Define  : 0
% 14.47/7.11  #Split   : 3
% 14.47/7.11  #Chain   : 0
% 14.47/7.11  #Close   : 0
% 14.47/7.11  
% 14.47/7.11  Ordering : KBO
% 14.47/7.11  
% 14.47/7.11  Simplification rules
% 14.47/7.11  ----------------------
% 14.47/7.11  #Subsume      : 1535
% 14.47/7.11  #Demod        : 7303
% 14.47/7.11  #Tautology    : 2335
% 14.47/7.11  #SimpNegUnit  : 40
% 14.47/7.11  #BackRed      : 12
% 14.47/7.11  
% 14.47/7.11  #Partial instantiations: 0
% 14.47/7.11  #Strategies tried      : 1
% 14.47/7.11  
% 14.47/7.11  Timing (in seconds)
% 14.47/7.11  ----------------------
% 14.47/7.12  Preprocessing        : 0.34
% 14.47/7.12  Parsing              : 0.18
% 14.47/7.12  CNF conversion       : 0.03
% 14.47/7.12  Main loop            : 6.02
% 14.47/7.12  Inferencing          : 1.11
% 14.47/7.12  Reduction            : 2.71
% 14.47/7.12  Demodulation         : 2.34
% 14.47/7.12  BG Simplification    : 0.16
% 14.47/7.12  Subsumption          : 1.73
% 14.47/7.12  Abstraction          : 0.22
% 14.47/7.12  MUC search           : 0.00
% 14.47/7.12  Cooper               : 0.00
% 14.47/7.12  Total                : 6.40
% 14.47/7.12  Index Insertion      : 0.00
% 14.47/7.12  Index Deletion       : 0.00
% 14.47/7.12  Index Matching       : 0.00
% 14.47/7.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
