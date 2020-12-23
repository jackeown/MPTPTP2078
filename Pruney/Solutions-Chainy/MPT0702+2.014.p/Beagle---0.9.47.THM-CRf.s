%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:04 EST 2020

% Result     : Theorem 5.90s
% Output     : CNFRefutation 5.90s
% Verified   : 
% Statistics : Number of formulae       :   52 (  94 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 228 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_22,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_85,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_101,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_85])).

tff(c_812,plain,(
    ! [C_62,A_63,B_64] :
      ( k3_xboole_0(k9_relat_1(C_62,A_63),k9_relat_1(C_62,B_64)) = k9_relat_1(C_62,k3_xboole_0(A_63,B_64))
      | ~ v2_funct_1(C_62)
      | ~ v1_funct_1(C_62)
      | ~ v1_relat_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_861,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_812])).

tff(c_879,plain,(
    k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_861])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k10_relat_1(B_18,k9_relat_1(B_18,A_17)),A_17)
      | ~ v2_funct_1(B_18)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_894,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_879,c_20])).

tff(c_904,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_894])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_154,plain,(
    ! [A_31,C_32,B_33] :
      ( r1_tarski(A_31,C_32)
      | ~ r1_tarski(B_33,C_32)
      | ~ r1_tarski(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_167,plain,(
    ! [A_31,A_5,B_6] :
      ( r1_tarski(A_31,A_5)
      | ~ r1_tarski(A_31,k3_xboole_0(A_5,B_6)) ) ),
    inference(resolution,[status(thm)],[c_10,c_154])).

tff(c_5450,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_904,c_167])).

tff(c_601,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,k10_relat_1(B_58,k9_relat_1(B_58,A_57)))
      | ~ r1_tarski(A_57,k1_relat_1(B_58))
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6807,plain,(
    ! [B_169,A_170] :
      ( k10_relat_1(B_169,k9_relat_1(B_169,A_170)) = A_170
      | ~ r1_tarski(k10_relat_1(B_169,k9_relat_1(B_169,A_170)),A_170)
      | ~ r1_tarski(A_170,k1_relat_1(B_169))
      | ~ v1_relat_1(B_169) ) ),
    inference(resolution,[status(thm)],[c_601,c_4])).

tff(c_6810,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5450,c_6807])).

tff(c_6831,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_6810])).

tff(c_36,plain,(
    ! [B_22,A_23] : k3_xboole_0(B_22,A_23) = k3_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_51,plain,(
    ! [B_22,A_23] : r1_tarski(k3_xboole_0(B_22,A_23),A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_10])).

tff(c_166,plain,(
    ! [A_31,A_23,B_22] :
      ( r1_tarski(A_31,A_23)
      | ~ r1_tarski(A_31,k3_xboole_0(B_22,A_23)) ) ),
    inference(resolution,[status(thm)],[c_51,c_154])).

tff(c_5449,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_904,c_166])).

tff(c_6840,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6831,c_5449])).

tff(c_6845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_6840])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:43:23 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.90/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.12  
% 5.90/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.12  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.90/2.12  
% 5.90/2.12  %Foreground sorts:
% 5.90/2.12  
% 5.90/2.12  
% 5.90/2.12  %Background operators:
% 5.90/2.12  
% 5.90/2.12  
% 5.90/2.12  %Foreground operators:
% 5.90/2.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.90/2.12  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.90/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.90/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.90/2.12  tff('#skF_2', type, '#skF_2': $i).
% 5.90/2.12  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.90/2.12  tff('#skF_3', type, '#skF_3': $i).
% 5.90/2.12  tff('#skF_1', type, '#skF_1': $i).
% 5.90/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.90/2.12  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.90/2.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.90/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.90/2.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.90/2.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.90/2.12  
% 5.90/2.13  tff(f_80, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 5.90/2.13  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.90/2.13  tff(f_53, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 5.90/2.13  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 5.90/2.13  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.90/2.13  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.90/2.13  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 5.90/2.13  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.90/2.13  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.90/2.13  tff(c_22, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.90/2.13  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.90/2.13  tff(c_26, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.90/2.13  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.90/2.13  tff(c_24, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.90/2.13  tff(c_28, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.90/2.13  tff(c_85, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.90/2.13  tff(c_101, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_85])).
% 5.90/2.13  tff(c_812, plain, (![C_62, A_63, B_64]: (k3_xboole_0(k9_relat_1(C_62, A_63), k9_relat_1(C_62, B_64))=k9_relat_1(C_62, k3_xboole_0(A_63, B_64)) | ~v2_funct_1(C_62) | ~v1_funct_1(C_62) | ~v1_relat_1(C_62))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.90/2.13  tff(c_861, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_101, c_812])).
% 5.90/2.13  tff(c_879, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_861])).
% 5.90/2.13  tff(c_20, plain, (![B_18, A_17]: (r1_tarski(k10_relat_1(B_18, k9_relat_1(B_18, A_17)), A_17) | ~v2_funct_1(B_18) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.90/2.13  tff(c_894, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_879, c_20])).
% 5.90/2.13  tff(c_904, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_894])).
% 5.90/2.13  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.90/2.13  tff(c_154, plain, (![A_31, C_32, B_33]: (r1_tarski(A_31, C_32) | ~r1_tarski(B_33, C_32) | ~r1_tarski(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.90/2.13  tff(c_167, plain, (![A_31, A_5, B_6]: (r1_tarski(A_31, A_5) | ~r1_tarski(A_31, k3_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_10, c_154])).
% 5.90/2.13  tff(c_5450, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), '#skF_1')), inference(resolution, [status(thm)], [c_904, c_167])).
% 5.90/2.13  tff(c_601, plain, (![A_57, B_58]: (r1_tarski(A_57, k10_relat_1(B_58, k9_relat_1(B_58, A_57))) | ~r1_tarski(A_57, k1_relat_1(B_58)) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.90/2.13  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.90/2.13  tff(c_6807, plain, (![B_169, A_170]: (k10_relat_1(B_169, k9_relat_1(B_169, A_170))=A_170 | ~r1_tarski(k10_relat_1(B_169, k9_relat_1(B_169, A_170)), A_170) | ~r1_tarski(A_170, k1_relat_1(B_169)) | ~v1_relat_1(B_169))), inference(resolution, [status(thm)], [c_601, c_4])).
% 5.90/2.13  tff(c_6810, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5450, c_6807])).
% 5.90/2.13  tff(c_6831, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_6810])).
% 5.90/2.13  tff(c_36, plain, (![B_22, A_23]: (k3_xboole_0(B_22, A_23)=k3_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.90/2.13  tff(c_51, plain, (![B_22, A_23]: (r1_tarski(k3_xboole_0(B_22, A_23), A_23))), inference(superposition, [status(thm), theory('equality')], [c_36, c_10])).
% 5.90/2.13  tff(c_166, plain, (![A_31, A_23, B_22]: (r1_tarski(A_31, A_23) | ~r1_tarski(A_31, k3_xboole_0(B_22, A_23)))), inference(resolution, [status(thm)], [c_51, c_154])).
% 5.90/2.13  tff(c_5449, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), '#skF_2')), inference(resolution, [status(thm)], [c_904, c_166])).
% 5.90/2.13  tff(c_6840, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6831, c_5449])).
% 5.90/2.13  tff(c_6845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_6840])).
% 5.90/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.13  
% 5.90/2.13  Inference rules
% 5.90/2.13  ----------------------
% 5.90/2.13  #Ref     : 0
% 5.90/2.13  #Sup     : 1655
% 5.90/2.13  #Fact    : 0
% 5.90/2.13  #Define  : 0
% 5.90/2.13  #Split   : 4
% 5.90/2.13  #Chain   : 0
% 5.90/2.13  #Close   : 0
% 5.90/2.13  
% 5.90/2.13  Ordering : KBO
% 5.90/2.13  
% 5.90/2.13  Simplification rules
% 5.90/2.13  ----------------------
% 5.90/2.13  #Subsume      : 198
% 5.90/2.13  #Demod        : 1302
% 5.90/2.13  #Tautology    : 895
% 5.90/2.13  #SimpNegUnit  : 1
% 5.90/2.13  #BackRed      : 4
% 5.90/2.13  
% 5.90/2.13  #Partial instantiations: 0
% 5.90/2.13  #Strategies tried      : 1
% 5.90/2.13  
% 5.90/2.13  Timing (in seconds)
% 5.90/2.13  ----------------------
% 5.90/2.14  Preprocessing        : 0.28
% 5.90/2.14  Parsing              : 0.15
% 5.90/2.14  CNF conversion       : 0.02
% 5.90/2.14  Main loop            : 1.09
% 5.90/2.14  Inferencing          : 0.29
% 5.90/2.14  Reduction            : 0.50
% 5.90/2.14  Demodulation         : 0.41
% 5.90/2.14  BG Simplification    : 0.03
% 5.90/2.14  Subsumption          : 0.21
% 5.90/2.14  Abstraction          : 0.05
% 5.90/2.14  MUC search           : 0.00
% 5.90/2.14  Cooper               : 0.00
% 5.90/2.14  Total                : 1.40
% 5.90/2.14  Index Insertion      : 0.00
% 5.90/2.14  Index Deletion       : 0.00
% 5.90/2.14  Index Matching       : 0.00
% 5.90/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
