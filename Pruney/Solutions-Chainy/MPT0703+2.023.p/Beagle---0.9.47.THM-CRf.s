%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:11 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   67 (  95 expanded)
%              Number of leaves         :   27 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 162 expanded)
%              Number of equality atoms :   36 (  46 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).

tff(c_41,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | k4_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_45,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_41,c_28])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_105,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_127,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_105])).

tff(c_130,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_152,plain,(
    ! [A_16,B_17] : k3_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = A_16 ),
    inference(resolution,[status(thm)],[c_22,c_130])).

tff(c_287,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_296,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k5_xboole_0(A_16,A_16) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_287])).

tff(c_305,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_296])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_46,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_69,plain,(
    k2_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_46])).

tff(c_18,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_67,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_xboole_0(A_12,B_13),A_12) = A_12 ),
    inference(resolution,[status(thm)],[c_18,c_46])).

tff(c_261,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(A_47,C_48)
      | ~ r1_tarski(k2_xboole_0(A_47,B_49),C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_321,plain,(
    ! [A_53,B_54,B_55] : r1_tarski(A_53,k2_xboole_0(k2_xboole_0(A_53,B_54),B_55)) ),
    inference(resolution,[status(thm)],[c_22,c_261])).

tff(c_395,plain,(
    ! [A_58,B_59,B_60] : r1_tarski(k3_xboole_0(A_58,B_59),k2_xboole_0(A_58,B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_321])).

tff(c_430,plain,(
    ! [B_61] : r1_tarski(k3_xboole_0('#skF_1',B_61),k2_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_395])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_451,plain,(
    ! [B_61] : k4_xboole_0(k3_xboole_0('#skF_1',B_61),k2_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_430,c_10])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_692,plain,(
    ! [B_72,A_73] :
      ( k9_relat_1(B_72,k10_relat_1(B_72,A_73)) = A_73
      | ~ r1_tarski(A_73,k2_relat_1(B_72))
      | ~ v1_funct_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_705,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_692])).

tff(c_717,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_705])).

tff(c_1064,plain,(
    ! [C_89,A_90,B_91] :
      ( k3_xboole_0(k10_relat_1(C_89,A_90),k10_relat_1(C_89,B_91)) = k10_relat_1(C_89,k3_xboole_0(A_90,B_91))
      | ~ v1_funct_1(C_89)
      | ~ v1_relat_1(C_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_149,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_130])).

tff(c_1073,plain,
    ( k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1064,c_149])).

tff(c_1111,plain,(
    k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1073])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3100,plain,(
    ! [B_161,A_162] :
      ( k9_relat_1(B_161,k10_relat_1(B_161,A_162)) = A_162
      | ~ v1_funct_1(B_161)
      | ~ v1_relat_1(B_161)
      | k4_xboole_0(A_162,k2_relat_1(B_161)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_692])).

tff(c_3119,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k2_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1111,c_3100])).

tff(c_3135,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_36,c_34,c_717,c_3119])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3209,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3135,c_12])).

tff(c_3242,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_3209])).

tff(c_3244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_3242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.66  
% 3.69/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/1.66  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.69/1.66  
% 3.69/1.66  %Foreground sorts:
% 3.69/1.66  
% 3.69/1.66  
% 3.69/1.66  %Background operators:
% 3.69/1.66  
% 3.69/1.66  
% 3.69/1.66  %Foreground operators:
% 3.69/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.69/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.69/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.69/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.69/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.69/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.69/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.69/1.66  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.69/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.69/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.69/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.66  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.69/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.69/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.69/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.69/1.66  
% 3.87/1.67  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.87/1.67  tff(f_78, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 3.87/1.67  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.87/1.67  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.87/1.67  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.87/1.67  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.87/1.67  tff(f_47, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.87/1.67  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.87/1.67  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 3.87/1.67  tff(f_59, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_funct_1)).
% 3.87/1.67  tff(c_41, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | k4_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.87/1.67  tff(c_28, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.87/1.67  tff(c_45, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_41, c_28])).
% 3.87/1.67  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.87/1.67  tff(c_105, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.87/1.67  tff(c_127, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_105])).
% 3.87/1.67  tff(c_130, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.67  tff(c_152, plain, (![A_16, B_17]: (k3_xboole_0(A_16, k2_xboole_0(A_16, B_17))=A_16)), inference(resolution, [status(thm)], [c_22, c_130])).
% 3.87/1.67  tff(c_287, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.87/1.67  tff(c_296, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k5_xboole_0(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_152, c_287])).
% 3.87/1.67  tff(c_305, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_296])).
% 3.87/1.67  tff(c_30, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.87/1.67  tff(c_46, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.87/1.67  tff(c_69, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_46])).
% 3.87/1.67  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.87/1.67  tff(c_67, plain, (![A_12, B_13]: (k2_xboole_0(k3_xboole_0(A_12, B_13), A_12)=A_12)), inference(resolution, [status(thm)], [c_18, c_46])).
% 3.87/1.67  tff(c_261, plain, (![A_47, C_48, B_49]: (r1_tarski(A_47, C_48) | ~r1_tarski(k2_xboole_0(A_47, B_49), C_48))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.87/1.67  tff(c_321, plain, (![A_53, B_54, B_55]: (r1_tarski(A_53, k2_xboole_0(k2_xboole_0(A_53, B_54), B_55)))), inference(resolution, [status(thm)], [c_22, c_261])).
% 3.87/1.67  tff(c_395, plain, (![A_58, B_59, B_60]: (r1_tarski(k3_xboole_0(A_58, B_59), k2_xboole_0(A_58, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_321])).
% 3.87/1.67  tff(c_430, plain, (![B_61]: (r1_tarski(k3_xboole_0('#skF_1', B_61), k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_69, c_395])).
% 3.87/1.67  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.87/1.67  tff(c_451, plain, (![B_61]: (k4_xboole_0(k3_xboole_0('#skF_1', B_61), k2_relat_1('#skF_3'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_430, c_10])).
% 3.87/1.67  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.87/1.67  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.87/1.68  tff(c_692, plain, (![B_72, A_73]: (k9_relat_1(B_72, k10_relat_1(B_72, A_73))=A_73 | ~r1_tarski(A_73, k2_relat_1(B_72)) | ~v1_funct_1(B_72) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.87/1.68  tff(c_705, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_692])).
% 3.87/1.68  tff(c_717, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_705])).
% 3.87/1.68  tff(c_1064, plain, (![C_89, A_90, B_91]: (k3_xboole_0(k10_relat_1(C_89, A_90), k10_relat_1(C_89, B_91))=k10_relat_1(C_89, k3_xboole_0(A_90, B_91)) | ~v1_funct_1(C_89) | ~v1_relat_1(C_89))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.87/1.68  tff(c_32, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.87/1.68  tff(c_149, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_130])).
% 3.87/1.68  tff(c_1073, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1064, c_149])).
% 3.87/1.68  tff(c_1111, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1073])).
% 3.87/1.68  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.87/1.68  tff(c_3100, plain, (![B_161, A_162]: (k9_relat_1(B_161, k10_relat_1(B_161, A_162))=A_162 | ~v1_funct_1(B_161) | ~v1_relat_1(B_161) | k4_xboole_0(A_162, k2_relat_1(B_161))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_692])).
% 3.87/1.68  tff(c_3119, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k2_relat_1('#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1111, c_3100])).
% 3.87/1.68  tff(c_3135, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_451, c_36, c_34, c_717, c_3119])).
% 3.87/1.68  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.87/1.68  tff(c_3209, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3135, c_12])).
% 3.87/1.68  tff(c_3242, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_305, c_3209])).
% 3.87/1.68  tff(c_3244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_3242])).
% 3.87/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.68  
% 3.87/1.68  Inference rules
% 3.87/1.68  ----------------------
% 3.87/1.68  #Ref     : 0
% 3.87/1.68  #Sup     : 789
% 3.87/1.68  #Fact    : 0
% 3.87/1.68  #Define  : 0
% 3.87/1.68  #Split   : 2
% 3.87/1.68  #Chain   : 0
% 3.87/1.68  #Close   : 0
% 3.87/1.68  
% 3.87/1.68  Ordering : KBO
% 3.87/1.68  
% 3.87/1.68  Simplification rules
% 3.87/1.68  ----------------------
% 3.87/1.68  #Subsume      : 50
% 3.87/1.68  #Demod        : 478
% 3.87/1.68  #Tautology    : 497
% 3.87/1.68  #SimpNegUnit  : 1
% 3.87/1.68  #BackRed      : 0
% 3.87/1.68  
% 3.87/1.68  #Partial instantiations: 0
% 3.87/1.68  #Strategies tried      : 1
% 3.87/1.68  
% 3.87/1.68  Timing (in seconds)
% 3.87/1.68  ----------------------
% 3.87/1.68  Preprocessing        : 0.28
% 3.87/1.68  Parsing              : 0.16
% 3.87/1.68  CNF conversion       : 0.02
% 3.87/1.68  Main loop            : 0.63
% 3.87/1.68  Inferencing          : 0.21
% 3.87/1.68  Reduction            : 0.24
% 3.87/1.68  Demodulation         : 0.18
% 3.87/1.68  BG Simplification    : 0.03
% 3.87/1.68  Subsumption          : 0.11
% 3.87/1.68  Abstraction          : 0.03
% 3.87/1.68  MUC search           : 0.00
% 3.87/1.68  Cooper               : 0.00
% 3.87/1.68  Total                : 0.94
% 3.87/1.68  Index Insertion      : 0.00
% 3.87/1.68  Index Deletion       : 0.00
% 3.87/1.68  Index Matching       : 0.00
% 3.87/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
