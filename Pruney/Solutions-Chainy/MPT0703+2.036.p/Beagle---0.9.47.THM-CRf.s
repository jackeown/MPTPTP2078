%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:13 EST 2020

% Result     : Theorem 6.91s
% Output     : CNFRefutation 7.09s
% Verified   : 
% Statistics : Number of formulae       :   60 (  97 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 192 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k3_xboole_0(A,k10_relat_1(C,B)),k10_relat_1(C,k3_xboole_0(k9_relat_1(C,A),B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_funct_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k10_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(c_36,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_38,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3371,plain,(
    ! [B_176,A_177] :
      ( k9_relat_1(B_176,k10_relat_1(B_176,A_177)) = A_177
      | ~ r1_tarski(A_177,k2_relat_1(B_176))
      | ~ v1_funct_1(B_176)
      | ~ v1_relat_1(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3417,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_3371])).

tff(c_3447,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3417])).

tff(c_40,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_101,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_117,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_101])).

tff(c_3945,plain,(
    ! [A_194,C_195,B_196] :
      ( r1_tarski(k3_xboole_0(A_194,k10_relat_1(C_195,B_196)),k10_relat_1(C_195,k3_xboole_0(k9_relat_1(C_195,A_194),B_196)))
      | ~ v1_relat_1(C_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3984,plain,
    ( r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',k3_xboole_0(k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')),'#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_3945])).

tff(c_4004,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3447,c_3984])).

tff(c_4355,plain,(
    ! [C_204,A_205,B_206] :
      ( r1_tarski(k10_relat_1(C_204,k3_xboole_0(A_205,B_206)),k3_xboole_0(k10_relat_1(C_204,A_205),k10_relat_1(C_204,B_206)))
      | ~ v1_relat_1(C_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4401,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_4355])).

tff(c_4421,plain,(
    r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4401])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10397,plain,
    ( k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1')
    | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_4421,c_2])).

tff(c_10411,plain,(
    k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4004,c_10397])).

tff(c_605,plain,(
    ! [A_86,C_87,B_88] :
      ( r1_tarski(A_86,C_87)
      | ~ r1_tarski(B_88,C_87)
      | ~ r1_tarski(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_652,plain,(
    ! [A_86] :
      ( r1_tarski(A_86,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_86,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_605])).

tff(c_3393,plain,(
    ! [A_86] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_86)) = A_86
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_86,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_652,c_3371])).

tff(c_3432,plain,(
    ! [A_86] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_86)) = A_86
      | ~ r1_tarski(A_86,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_3393])).

tff(c_10421,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10411,c_3432])).

tff(c_10454,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3447,c_10421])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [A_40,B_41] :
      ( k2_xboole_0(A_40,B_41) = B_41
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_1795,plain,(
    ! [A_140,B_141,C_142] : r1_tarski(k2_xboole_0(k3_xboole_0(A_140,B_141),k3_xboole_0(A_140,C_142)),k2_xboole_0(B_141,C_142)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1899,plain,(
    ! [A_140,B_141] : r1_tarski(k3_xboole_0(A_140,B_141),k2_xboole_0(B_141,B_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_1795])).

tff(c_1917,plain,(
    ! [A_140,B_141] : r1_tarski(k3_xboole_0(A_140,B_141),B_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_1899])).

tff(c_10544,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10454,c_1917])).

tff(c_10600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_10544])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.91/2.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.91/2.44  
% 6.91/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.09/2.44  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 7.09/2.44  
% 7.09/2.44  %Foreground sorts:
% 7.09/2.44  
% 7.09/2.44  
% 7.09/2.44  %Background operators:
% 7.09/2.44  
% 7.09/2.44  
% 7.09/2.44  %Foreground operators:
% 7.09/2.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.09/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.09/2.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.09/2.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.09/2.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.09/2.44  tff('#skF_2', type, '#skF_2': $i).
% 7.09/2.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.09/2.44  tff('#skF_3', type, '#skF_3': $i).
% 7.09/2.44  tff('#skF_1', type, '#skF_1': $i).
% 7.09/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.09/2.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.09/2.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.09/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.09/2.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.09/2.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.09/2.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.09/2.44  
% 7.09/2.46  tff(f_102, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 7.09/2.46  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.09/2.46  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 7.09/2.46  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.09/2.46  tff(f_91, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k3_xboole_0(A, k10_relat_1(C, B)), k10_relat_1(C, k3_xboole_0(k9_relat_1(C, A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_funct_1)).
% 7.09/2.46  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k10_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_relat_1)).
% 7.09/2.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.09/2.46  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.09/2.46  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.09/2.46  tff(f_53, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 7.09/2.46  tff(c_36, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.09/2.46  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.09/2.46  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.09/2.46  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.09/2.46  tff(c_38, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.09/2.46  tff(c_3371, plain, (![B_176, A_177]: (k9_relat_1(B_176, k10_relat_1(B_176, A_177))=A_177 | ~r1_tarski(A_177, k2_relat_1(B_176)) | ~v1_funct_1(B_176) | ~v1_relat_1(B_176))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.09/2.46  tff(c_3417, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_3371])).
% 7.09/2.46  tff(c_3447, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3417])).
% 7.09/2.46  tff(c_40, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.09/2.46  tff(c_101, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.09/2.46  tff(c_117, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_101])).
% 7.09/2.46  tff(c_3945, plain, (![A_194, C_195, B_196]: (r1_tarski(k3_xboole_0(A_194, k10_relat_1(C_195, B_196)), k10_relat_1(C_195, k3_xboole_0(k9_relat_1(C_195, A_194), B_196))) | ~v1_relat_1(C_195))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.09/2.46  tff(c_3984, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', k3_xboole_0(k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1')), '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_117, c_3945])).
% 7.09/2.46  tff(c_4004, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3447, c_3984])).
% 7.09/2.46  tff(c_4355, plain, (![C_204, A_205, B_206]: (r1_tarski(k10_relat_1(C_204, k3_xboole_0(A_205, B_206)), k3_xboole_0(k10_relat_1(C_204, A_205), k10_relat_1(C_204, B_206))) | ~v1_relat_1(C_204))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.09/2.46  tff(c_4401, plain, (r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_117, c_4355])).
% 7.09/2.46  tff(c_4421, plain, (r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4401])).
% 7.09/2.46  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.09/2.46  tff(c_10397, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1') | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_4421, c_2])).
% 7.09/2.46  tff(c_10411, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4004, c_10397])).
% 7.09/2.46  tff(c_605, plain, (![A_86, C_87, B_88]: (r1_tarski(A_86, C_87) | ~r1_tarski(B_88, C_87) | ~r1_tarski(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.09/2.46  tff(c_652, plain, (![A_86]: (r1_tarski(A_86, k2_relat_1('#skF_3')) | ~r1_tarski(A_86, '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_605])).
% 7.09/2.46  tff(c_3393, plain, (![A_86]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_86))=A_86 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_86, '#skF_1'))), inference(resolution, [status(thm)], [c_652, c_3371])).
% 7.09/2.46  tff(c_3432, plain, (![A_86]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_86))=A_86 | ~r1_tarski(A_86, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_3393])).
% 7.09/2.46  tff(c_10421, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10411, c_3432])).
% 7.09/2.46  tff(c_10454, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3447, c_10421])).
% 7.09/2.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.09/2.46  tff(c_49, plain, (![A_40, B_41]: (k2_xboole_0(A_40, B_41)=B_41 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.09/2.46  tff(c_65, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_49])).
% 7.09/2.46  tff(c_1795, plain, (![A_140, B_141, C_142]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_140, B_141), k3_xboole_0(A_140, C_142)), k2_xboole_0(B_141, C_142)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.09/2.46  tff(c_1899, plain, (![A_140, B_141]: (r1_tarski(k3_xboole_0(A_140, B_141), k2_xboole_0(B_141, B_141)))), inference(superposition, [status(thm), theory('equality')], [c_65, c_1795])).
% 7.09/2.46  tff(c_1917, plain, (![A_140, B_141]: (r1_tarski(k3_xboole_0(A_140, B_141), B_141))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_1899])).
% 7.09/2.46  tff(c_10544, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10454, c_1917])).
% 7.09/2.46  tff(c_10600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_10544])).
% 7.09/2.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.09/2.46  
% 7.09/2.46  Inference rules
% 7.09/2.46  ----------------------
% 7.09/2.46  #Ref     : 0
% 7.09/2.46  #Sup     : 2601
% 7.09/2.46  #Fact    : 0
% 7.09/2.46  #Define  : 0
% 7.09/2.46  #Split   : 3
% 7.09/2.46  #Chain   : 0
% 7.09/2.46  #Close   : 0
% 7.09/2.46  
% 7.09/2.46  Ordering : KBO
% 7.09/2.46  
% 7.09/2.46  Simplification rules
% 7.09/2.46  ----------------------
% 7.09/2.46  #Subsume      : 102
% 7.09/2.46  #Demod        : 1528
% 7.09/2.46  #Tautology    : 1565
% 7.09/2.46  #SimpNegUnit  : 1
% 7.09/2.46  #BackRed      : 2
% 7.09/2.46  
% 7.09/2.46  #Partial instantiations: 0
% 7.09/2.46  #Strategies tried      : 1
% 7.09/2.46  
% 7.09/2.46  Timing (in seconds)
% 7.09/2.46  ----------------------
% 7.09/2.46  Preprocessing        : 0.29
% 7.09/2.46  Parsing              : 0.16
% 7.09/2.46  CNF conversion       : 0.02
% 7.09/2.46  Main loop            : 1.38
% 7.09/2.46  Inferencing          : 0.42
% 7.09/2.46  Reduction            : 0.56
% 7.09/2.46  Demodulation         : 0.45
% 7.09/2.46  BG Simplification    : 0.04
% 7.09/2.46  Subsumption          : 0.26
% 7.09/2.46  Abstraction          : 0.07
% 7.09/2.46  MUC search           : 0.00
% 7.09/2.46  Cooper               : 0.00
% 7.09/2.46  Total                : 1.70
% 7.09/2.46  Index Insertion      : 0.00
% 7.09/2.46  Index Deletion       : 0.00
% 7.09/2.46  Index Matching       : 0.00
% 7.09/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
