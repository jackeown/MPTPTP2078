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
% DateTime   : Thu Dec  3 09:45:34 EST 2020

% Result     : Theorem 4.17s
% Output     : CNFRefutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :   53 (  92 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 ( 142 expanded)
%              Number of equality atoms :   23 (  48 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,D)
          & r1_xboole_0(B,D)
          & r1_xboole_0(C,D) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(A,B),C),D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(A_21,B_22)
      | k4_xboole_0(A_21,B_22) != A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_16,C_18,B_17] :
      ( ~ r1_xboole_0(A_16,C_18)
      | ~ r1_xboole_0(A_16,B_17)
      | r1_xboole_0(A_16,k2_xboole_0(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40,plain,(
    r1_xboole_0('#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_131,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = A_44
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_156,plain,(
    k4_xboole_0('#skF_1','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_40,c_131])).

tff(c_1566,plain,(
    ! [C_95,B_96,A_97] :
      ( k4_xboole_0(k2_xboole_0(C_95,B_96),A_97) = k2_xboole_0(k4_xboole_0(C_95,A_97),B_96)
      | ~ r1_xboole_0(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_110,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(A_40,B_41)
      | k4_xboole_0(A_40,B_41) != A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k2_xboole_0(A_13,B_14),C_15) = k2_xboole_0(A_13,k2_xboole_0(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_34,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_41,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_34])).

tff(c_114,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')),'#skF_4') != k2_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_110,c_41])).

tff(c_1574,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_1','#skF_4'),k2_xboole_0('#skF_2','#skF_3')) != k2_xboole_0('#skF_1',k2_xboole_0('#skF_2','#skF_3'))
    | ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1566,c_114])).

tff(c_1644,plain,(
    ~ r1_xboole_0('#skF_4',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_1574])).

tff(c_1659,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_3')
    | ~ r1_xboole_0('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_1644])).

tff(c_1813,plain,(
    ~ r1_xboole_0('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1659])).

tff(c_1817,plain,(
    k4_xboole_0('#skF_4','#skF_2') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_1813])).

tff(c_38,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_157,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_165,plain,(
    ! [A_7,B_8] : k2_xboole_0(k4_xboole_0(A_7,B_8),A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_8,c_157])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1641,plain,(
    ! [A_3,A_97] :
      ( k2_xboole_0(k4_xboole_0(A_3,A_97),A_3) = k4_xboole_0(A_3,A_97)
      | ~ r1_xboole_0(A_97,A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1566])).

tff(c_2400,plain,(
    ! [A_111,A_112] :
      ( k4_xboole_0(A_111,A_112) = A_111
      | ~ r1_xboole_0(A_112,A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_1641])).

tff(c_2469,plain,(
    k4_xboole_0('#skF_4','#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_2400])).

tff(c_2511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1817,c_2469])).

tff(c_2512,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1659])).

tff(c_2517,plain,(
    k4_xboole_0('#skF_4','#skF_3') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_2512])).

tff(c_36,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2745,plain,(
    ! [A_113,A_114] :
      ( k4_xboole_0(A_113,A_114) = A_113
      | ~ r1_xboole_0(A_114,A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_1641])).

tff(c_2811,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_2745])).

tff(c_2857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2517,c_2811])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.17/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.82  
% 4.17/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.82  %$ r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.17/1.82  
% 4.17/1.82  %Foreground sorts:
% 4.17/1.82  
% 4.17/1.82  
% 4.17/1.82  %Background operators:
% 4.17/1.82  
% 4.17/1.82  
% 4.17/1.82  %Foreground operators:
% 4.17/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.17/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.17/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.17/1.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.17/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.17/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.17/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.17/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.17/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.17/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.17/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.17/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.17/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.17/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.17/1.82  
% 4.17/1.84  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.17/1.84  tff(f_57, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.17/1.84  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (((r1_xboole_0(A, D) & r1_xboole_0(B, D)) & r1_xboole_0(C, D)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(A, B), C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_xboole_1)).
% 4.17/1.84  tff(f_67, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 4.17/1.84  tff(f_41, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 4.17/1.84  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.17/1.84  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.17/1.84  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.17/1.84  tff(c_26, plain, (![A_21, B_22]: (r1_xboole_0(A_21, B_22) | k4_xboole_0(A_21, B_22)!=A_21)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.17/1.84  tff(c_16, plain, (![A_16, C_18, B_17]: (~r1_xboole_0(A_16, C_18) | ~r1_xboole_0(A_16, B_17) | r1_xboole_0(A_16, k2_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.17/1.84  tff(c_40, plain, (r1_xboole_0('#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.17/1.84  tff(c_131, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=A_44 | ~r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.17/1.84  tff(c_156, plain, (k4_xboole_0('#skF_1', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_40, c_131])).
% 4.17/1.84  tff(c_1566, plain, (![C_95, B_96, A_97]: (k4_xboole_0(k2_xboole_0(C_95, B_96), A_97)=k2_xboole_0(k4_xboole_0(C_95, A_97), B_96) | ~r1_xboole_0(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.17/1.84  tff(c_110, plain, (![A_40, B_41]: (r1_xboole_0(A_40, B_41) | k4_xboole_0(A_40, B_41)!=A_40)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.17/1.84  tff(c_14, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k2_xboole_0(A_13, B_14), C_15)=k2_xboole_0(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.17/1.84  tff(c_34, plain, (~r1_xboole_0(k2_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.17/1.84  tff(c_41, plain, (~r1_xboole_0(k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_34])).
% 4.17/1.84  tff(c_114, plain, (k4_xboole_0(k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')), '#skF_4')!=k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_110, c_41])).
% 4.17/1.84  tff(c_1574, plain, (k2_xboole_0(k4_xboole_0('#skF_1', '#skF_4'), k2_xboole_0('#skF_2', '#skF_3'))!=k2_xboole_0('#skF_1', k2_xboole_0('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_4', k2_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1566, c_114])).
% 4.17/1.84  tff(c_1644, plain, (~r1_xboole_0('#skF_4', k2_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_1574])).
% 4.17/1.84  tff(c_1659, plain, (~r1_xboole_0('#skF_4', '#skF_3') | ~r1_xboole_0('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_1644])).
% 4.17/1.84  tff(c_1813, plain, (~r1_xboole_0('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_1659])).
% 4.17/1.84  tff(c_1817, plain, (k4_xboole_0('#skF_4', '#skF_2')!='#skF_4'), inference(resolution, [status(thm)], [c_26, c_1813])).
% 4.17/1.84  tff(c_38, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.17/1.84  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.17/1.84  tff(c_157, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.17/1.84  tff(c_165, plain, (![A_7, B_8]: (k2_xboole_0(k4_xboole_0(A_7, B_8), A_7)=A_7)), inference(resolution, [status(thm)], [c_8, c_157])).
% 4.17/1.84  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.17/1.84  tff(c_1641, plain, (![A_3, A_97]: (k2_xboole_0(k4_xboole_0(A_3, A_97), A_3)=k4_xboole_0(A_3, A_97) | ~r1_xboole_0(A_97, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1566])).
% 4.17/1.84  tff(c_2400, plain, (![A_111, A_112]: (k4_xboole_0(A_111, A_112)=A_111 | ~r1_xboole_0(A_112, A_111))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_1641])).
% 4.17/1.84  tff(c_2469, plain, (k4_xboole_0('#skF_4', '#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_2400])).
% 4.17/1.84  tff(c_2511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1817, c_2469])).
% 4.17/1.84  tff(c_2512, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_1659])).
% 4.17/1.84  tff(c_2517, plain, (k4_xboole_0('#skF_4', '#skF_3')!='#skF_4'), inference(resolution, [status(thm)], [c_26, c_2512])).
% 4.17/1.84  tff(c_36, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.17/1.84  tff(c_2745, plain, (![A_113, A_114]: (k4_xboole_0(A_113, A_114)=A_113 | ~r1_xboole_0(A_114, A_113))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_1641])).
% 4.17/1.84  tff(c_2811, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_36, c_2745])).
% 4.17/1.84  tff(c_2857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2517, c_2811])).
% 4.17/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.84  
% 4.17/1.84  Inference rules
% 4.17/1.84  ----------------------
% 4.17/1.84  #Ref     : 0
% 4.17/1.84  #Sup     : 750
% 4.17/1.84  #Fact    : 0
% 4.17/1.84  #Define  : 0
% 4.17/1.84  #Split   : 1
% 4.17/1.84  #Chain   : 0
% 4.17/1.84  #Close   : 0
% 4.17/1.84  
% 4.17/1.84  Ordering : KBO
% 4.17/1.84  
% 4.17/1.84  Simplification rules
% 4.17/1.84  ----------------------
% 4.17/1.84  #Subsume      : 4
% 4.17/1.84  #Demod        : 485
% 4.17/1.84  #Tautology    : 539
% 4.17/1.84  #SimpNegUnit  : 2
% 4.17/1.84  #BackRed      : 3
% 4.17/1.84  
% 4.17/1.84  #Partial instantiations: 0
% 4.17/1.84  #Strategies tried      : 1
% 4.17/1.84  
% 4.17/1.84  Timing (in seconds)
% 4.17/1.84  ----------------------
% 4.17/1.85  Preprocessing        : 0.37
% 4.17/1.85  Parsing              : 0.21
% 4.17/1.85  CNF conversion       : 0.02
% 4.17/1.85  Main loop            : 0.70
% 4.17/1.85  Inferencing          : 0.25
% 4.17/1.85  Reduction            : 0.27
% 4.17/1.85  Demodulation         : 0.21
% 4.17/1.85  BG Simplification    : 0.03
% 4.17/1.85  Subsumption          : 0.10
% 4.17/1.85  Abstraction          : 0.03
% 4.17/1.85  MUC search           : 0.00
% 4.17/1.85  Cooper               : 0.00
% 4.17/1.85  Total                : 1.11
% 4.17/1.85  Index Insertion      : 0.00
% 4.17/1.85  Index Deletion       : 0.00
% 4.17/1.85  Index Matching       : 0.00
% 4.17/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
