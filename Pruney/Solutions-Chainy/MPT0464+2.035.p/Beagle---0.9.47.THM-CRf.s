%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:47 EST 2020

% Result     : Theorem 5.30s
% Output     : CNFRefutation 5.30s
% Verified   : 
% Statistics : Number of formulae       :   55 (  74 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 130 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    ! [A_36,B_37] :
      ( v1_relat_1(k3_xboole_0(A_36,B_37))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k1_xboole_0
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_399,plain,(
    ! [A_89,B_90] :
      ( k2_xboole_0(A_89,k4_xboole_0(B_90,A_89)) = B_90
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_426,plain,(
    ! [B_2] :
      ( k2_xboole_0(B_2,k1_xboole_0) = B_2
      | ~ r1_tarski(B_2,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_399])).

tff(c_433,plain,(
    ! [B_2] : k2_xboole_0(B_2,k1_xboole_0) = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_426])).

tff(c_834,plain,(
    ! [A_117,B_118,C_119] : r1_tarski(k2_xboole_0(k3_xboole_0(A_117,B_118),k3_xboole_0(A_117,C_119)),k2_xboole_0(B_118,C_119)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(k2_xboole_0(A_8,B_9),C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_860,plain,(
    ! [A_120,B_121,C_122] : r1_tarski(k3_xboole_0(A_120,B_121),k2_xboole_0(B_121,C_122)) ),
    inference(resolution,[status(thm)],[c_834,c_18])).

tff(c_868,plain,(
    ! [A_120,B_2] : r1_tarski(k3_xboole_0(A_120,B_2),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_860])).

tff(c_2708,plain,(
    ! [C_211,A_212,B_213] :
      ( r1_tarski(k5_relat_1(C_211,A_212),k5_relat_1(C_211,B_213))
      | ~ r1_tarski(A_212,B_213)
      | ~ v1_relat_1(C_211)
      | ~ v1_relat_1(B_213)
      | ~ v1_relat_1(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    ! [A_11,B_12] : r1_tarski(k3_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1893,plain,(
    ! [C_174,A_175,B_176] :
      ( r1_tarski(k5_relat_1(C_174,A_175),k5_relat_1(C_174,B_176))
      | ~ r1_tarski(A_175,B_176)
      | ~ v1_relat_1(C_174)
      | ~ v1_relat_1(B_176)
      | ~ v1_relat_1(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_945,plain,(
    ! [A_126,B_127,C_128] :
      ( r1_tarski(A_126,k3_xboole_0(B_127,C_128))
      | ~ r1_tarski(A_126,C_128)
      | ~ r1_tarski(A_126,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_46,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_967,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_945,c_46])).

tff(c_1225,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_967])).

tff(c_1898,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1893,c_1225])).

tff(c_1910,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_20,c_1898])).

tff(c_1916,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1910])).

tff(c_1920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1916])).

tff(c_1921,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_967])).

tff(c_2714,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2708,c_1921])).

tff(c_2723,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_868,c_2714])).

tff(c_2728,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_2723])).

tff(c_2732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2728])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:55:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.30/2.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/2.35  
% 5.30/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/2.36  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.30/2.36  
% 5.30/2.36  %Foreground sorts:
% 5.30/2.36  
% 5.30/2.36  
% 5.30/2.36  %Background operators:
% 5.30/2.36  
% 5.30/2.36  
% 5.30/2.36  %Foreground operators:
% 5.30/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.30/2.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.30/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.30/2.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.30/2.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.30/2.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.30/2.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.30/2.36  tff('#skF_2', type, '#skF_2': $i).
% 5.30/2.36  tff('#skF_3', type, '#skF_3': $i).
% 5.30/2.36  tff('#skF_1', type, '#skF_1': $i).
% 5.30/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.30/2.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.30/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.30/2.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.30/2.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.30/2.36  
% 5.30/2.38  tff(f_108, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 5.30/2.38  tff(f_85, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 5.30/2.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.30/2.38  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.30/2.38  tff(f_67, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 5.30/2.38  tff(f_57, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 5.30/2.38  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.30/2.38  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 5.30/2.38  tff(f_47, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.30/2.38  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.30/2.38  tff(c_50, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.30/2.38  tff(c_42, plain, (![A_36, B_37]: (v1_relat_1(k3_xboole_0(A_36, B_37)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.30/2.38  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.30/2.38  tff(c_52, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.30/2.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.30/2.38  tff(c_60, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k1_xboole_0 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.30/2.38  tff(c_80, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_60])).
% 5.30/2.38  tff(c_399, plain, (![A_89, B_90]: (k2_xboole_0(A_89, k4_xboole_0(B_90, A_89))=B_90 | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.30/2.38  tff(c_426, plain, (![B_2]: (k2_xboole_0(B_2, k1_xboole_0)=B_2 | ~r1_tarski(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_80, c_399])).
% 5.30/2.38  tff(c_433, plain, (![B_2]: (k2_xboole_0(B_2, k1_xboole_0)=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_426])).
% 5.30/2.38  tff(c_834, plain, (![A_117, B_118, C_119]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_117, B_118), k3_xboole_0(A_117, C_119)), k2_xboole_0(B_118, C_119)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.30/2.38  tff(c_18, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(k2_xboole_0(A_8, B_9), C_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.30/2.38  tff(c_860, plain, (![A_120, B_121, C_122]: (r1_tarski(k3_xboole_0(A_120, B_121), k2_xboole_0(B_121, C_122)))), inference(resolution, [status(thm)], [c_834, c_18])).
% 5.30/2.38  tff(c_868, plain, (![A_120, B_2]: (r1_tarski(k3_xboole_0(A_120, B_2), B_2))), inference(superposition, [status(thm), theory('equality')], [c_433, c_860])).
% 5.30/2.38  tff(c_2708, plain, (![C_211, A_212, B_213]: (r1_tarski(k5_relat_1(C_211, A_212), k5_relat_1(C_211, B_213)) | ~r1_tarski(A_212, B_213) | ~v1_relat_1(C_211) | ~v1_relat_1(B_213) | ~v1_relat_1(A_212))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.30/2.38  tff(c_20, plain, (![A_11, B_12]: (r1_tarski(k3_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.30/2.38  tff(c_1893, plain, (![C_174, A_175, B_176]: (r1_tarski(k5_relat_1(C_174, A_175), k5_relat_1(C_174, B_176)) | ~r1_tarski(A_175, B_176) | ~v1_relat_1(C_174) | ~v1_relat_1(B_176) | ~v1_relat_1(A_175))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.30/2.38  tff(c_945, plain, (![A_126, B_127, C_128]: (r1_tarski(A_126, k3_xboole_0(B_127, C_128)) | ~r1_tarski(A_126, C_128) | ~r1_tarski(A_126, B_127))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.30/2.38  tff(c_46, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.30/2.38  tff(c_967, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_945, c_46])).
% 5.30/2.38  tff(c_1225, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_967])).
% 5.30/2.38  tff(c_1898, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1893, c_1225])).
% 5.30/2.38  tff(c_1910, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_20, c_1898])).
% 5.30/2.38  tff(c_1916, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_42, c_1910])).
% 5.30/2.38  tff(c_1920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1916])).
% 5.30/2.38  tff(c_1921, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_967])).
% 5.30/2.38  tff(c_2714, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2708, c_1921])).
% 5.30/2.38  tff(c_2723, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_868, c_2714])).
% 5.30/2.38  tff(c_2728, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_42, c_2723])).
% 5.30/2.38  tff(c_2732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_2728])).
% 5.30/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.30/2.38  
% 5.30/2.38  Inference rules
% 5.30/2.38  ----------------------
% 5.30/2.38  #Ref     : 0
% 5.30/2.38  #Sup     : 655
% 5.30/2.38  #Fact    : 0
% 5.30/2.38  #Define  : 0
% 5.30/2.38  #Split   : 2
% 5.30/2.38  #Chain   : 0
% 5.30/2.38  #Close   : 0
% 5.30/2.38  
% 5.30/2.38  Ordering : KBO
% 5.30/2.38  
% 5.30/2.38  Simplification rules
% 5.30/2.38  ----------------------
% 5.30/2.38  #Subsume      : 55
% 5.30/2.38  #Demod        : 381
% 5.30/2.38  #Tautology    : 360
% 5.30/2.38  #SimpNegUnit  : 4
% 5.30/2.38  #BackRed      : 3
% 5.30/2.38  
% 5.30/2.38  #Partial instantiations: 0
% 5.30/2.38  #Strategies tried      : 1
% 5.30/2.38  
% 5.30/2.38  Timing (in seconds)
% 5.30/2.38  ----------------------
% 5.30/2.38  Preprocessing        : 0.50
% 5.30/2.38  Parsing              : 0.27
% 5.30/2.38  CNF conversion       : 0.04
% 5.30/2.38  Main loop            : 1.00
% 5.30/2.38  Inferencing          : 0.34
% 5.30/2.38  Reduction            : 0.35
% 5.30/2.38  Demodulation         : 0.27
% 5.30/2.38  BG Simplification    : 0.04
% 5.30/2.39  Subsumption          : 0.18
% 5.30/2.39  Abstraction          : 0.05
% 5.30/2.39  MUC search           : 0.00
% 5.30/2.39  Cooper               : 0.00
% 5.30/2.39  Total                : 1.54
% 5.30/2.39  Index Insertion      : 0.00
% 5.30/2.39  Index Deletion       : 0.00
% 5.30/2.39  Index Matching       : 0.00
% 5.30/2.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
