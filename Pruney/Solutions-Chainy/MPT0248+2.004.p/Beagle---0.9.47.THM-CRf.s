%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:04 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 118 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 237 expanded)
%              Number of equality atoms :   61 ( 211 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_30,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_57,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_28,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_39,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_10])).

tff(c_289,plain,(
    ! [B_41,A_42] :
      ( k1_tarski(B_41) = A_42
      | k1_xboole_0 = A_42
      | ~ r1_tarski(A_42,k1_tarski(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_295,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_53,c_289])).

tff(c_307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_39,c_295])).

tff(c_308,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_350,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_362,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_350])).

tff(c_12,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_398,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_426,plain,(
    ! [A_55,B_56] : k3_tarski(k2_tarski(A_55,B_56)) = k2_xboole_0(B_56,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_398])).

tff(c_26,plain,(
    ! [A_17,B_18] : k3_tarski(k2_tarski(A_17,B_18)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_453,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_26])).

tff(c_468,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_34])).

tff(c_507,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_10])).

tff(c_309,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( k1_tarski(B_16) = A_15
      | k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_tarski(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_787,plain,(
    ! [B_70,A_71] :
      ( k1_tarski(B_70) = A_71
      | A_71 = '#skF_2'
      | ~ r1_tarski(A_71,k1_tarski(B_70)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_20])).

tff(c_790,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_507,c_787])).

tff(c_800,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_790])).

tff(c_807,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_468])).

tff(c_813,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_807])).

tff(c_815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_308,c_813])).

tff(c_816,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_817,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_32,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_846,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_817,c_32])).

tff(c_826,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_34])).

tff(c_935,plain,(
    ! [A_81,B_82] : k3_tarski(k2_tarski(A_81,B_82)) = k2_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_997,plain,(
    ! [B_88,A_89] : k3_tarski(k2_tarski(B_88,A_89)) = k2_xboole_0(A_89,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_935])).

tff(c_1024,plain,(
    ! [B_90,A_91] : k2_xboole_0(B_90,A_91) = k2_xboole_0(A_91,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_997,c_26])).

tff(c_1075,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_826,c_1024])).

tff(c_1090,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1075,c_10])).

tff(c_1175,plain,(
    ! [B_98,A_99] :
      ( k1_tarski(B_98) = A_99
      | k1_xboole_0 = A_99
      | ~ r1_tarski(A_99,k1_tarski(B_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1178,plain,(
    ! [A_99] :
      ( k1_tarski('#skF_1') = A_99
      | k1_xboole_0 = A_99
      | ~ r1_tarski(A_99,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_817,c_1175])).

tff(c_1191,plain,(
    ! [A_100] :
      ( A_100 = '#skF_2'
      | k1_xboole_0 = A_100
      | ~ r1_tarski(A_100,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_1178])).

tff(c_1194,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1090,c_1191])).

tff(c_1205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_816,c_846,c_1194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 21:24:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.42  
% 2.63/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.42  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.63/1.42  
% 2.63/1.42  %Foreground sorts:
% 2.63/1.42  
% 2.63/1.42  
% 2.63/1.42  %Background operators:
% 2.63/1.42  
% 2.63/1.42  
% 2.63/1.42  %Foreground operators:
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.63/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.42  
% 2.88/1.43  tff(f_72, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.88/1.43  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.88/1.43  tff(f_51, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.88/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.88/1.43  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.88/1.43  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.88/1.43  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.88/1.43  tff(c_30, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.88/1.43  tff(c_57, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 2.88/1.43  tff(c_28, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.88/1.43  tff(c_39, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_28])).
% 2.88/1.43  tff(c_34, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.88/1.43  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.88/1.43  tff(c_53, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_10])).
% 2.88/1.43  tff(c_289, plain, (![B_41, A_42]: (k1_tarski(B_41)=A_42 | k1_xboole_0=A_42 | ~r1_tarski(A_42, k1_tarski(B_41)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.88/1.43  tff(c_295, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_53, c_289])).
% 2.88/1.43  tff(c_307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_39, c_295])).
% 2.88/1.43  tff(c_308, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.88/1.43  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.43  tff(c_350, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.88/1.43  tff(c_362, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_350])).
% 2.88/1.43  tff(c_12, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.88/1.43  tff(c_398, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.88/1.43  tff(c_426, plain, (![A_55, B_56]: (k3_tarski(k2_tarski(A_55, B_56))=k2_xboole_0(B_56, A_55))), inference(superposition, [status(thm), theory('equality')], [c_12, c_398])).
% 2.88/1.43  tff(c_26, plain, (![A_17, B_18]: (k3_tarski(k2_tarski(A_17, B_18))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.88/1.43  tff(c_453, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_426, c_26])).
% 2.88/1.43  tff(c_468, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_453, c_34])).
% 2.88/1.43  tff(c_507, plain, (r1_tarski('#skF_3', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_468, c_10])).
% 2.88/1.43  tff(c_309, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.88/1.43  tff(c_20, plain, (![B_16, A_15]: (k1_tarski(B_16)=A_15 | k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_tarski(B_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.88/1.43  tff(c_787, plain, (![B_70, A_71]: (k1_tarski(B_70)=A_71 | A_71='#skF_2' | ~r1_tarski(A_71, k1_tarski(B_70)))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_20])).
% 2.88/1.43  tff(c_790, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_507, c_787])).
% 2.88/1.43  tff(c_800, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_308, c_790])).
% 2.88/1.43  tff(c_807, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_800, c_468])).
% 2.88/1.43  tff(c_813, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_362, c_807])).
% 2.88/1.43  tff(c_815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_308, c_813])).
% 2.88/1.43  tff(c_816, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 2.88/1.43  tff(c_817, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 2.88/1.43  tff(c_32, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.88/1.43  tff(c_846, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_817, c_817, c_32])).
% 2.88/1.43  tff(c_826, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_817, c_34])).
% 2.88/1.43  tff(c_935, plain, (![A_81, B_82]: (k3_tarski(k2_tarski(A_81, B_82))=k2_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.88/1.43  tff(c_997, plain, (![B_88, A_89]: (k3_tarski(k2_tarski(B_88, A_89))=k2_xboole_0(A_89, B_88))), inference(superposition, [status(thm), theory('equality')], [c_12, c_935])).
% 2.88/1.43  tff(c_1024, plain, (![B_90, A_91]: (k2_xboole_0(B_90, A_91)=k2_xboole_0(A_91, B_90))), inference(superposition, [status(thm), theory('equality')], [c_997, c_26])).
% 2.88/1.43  tff(c_1075, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_826, c_1024])).
% 2.88/1.43  tff(c_1090, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1075, c_10])).
% 2.88/1.43  tff(c_1175, plain, (![B_98, A_99]: (k1_tarski(B_98)=A_99 | k1_xboole_0=A_99 | ~r1_tarski(A_99, k1_tarski(B_98)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.88/1.43  tff(c_1178, plain, (![A_99]: (k1_tarski('#skF_1')=A_99 | k1_xboole_0=A_99 | ~r1_tarski(A_99, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_817, c_1175])).
% 2.88/1.43  tff(c_1191, plain, (![A_100]: (A_100='#skF_2' | k1_xboole_0=A_100 | ~r1_tarski(A_100, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_817, c_1178])).
% 2.88/1.43  tff(c_1194, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1090, c_1191])).
% 2.88/1.43  tff(c_1205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_816, c_846, c_1194])).
% 2.88/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.43  
% 2.88/1.43  Inference rules
% 2.88/1.43  ----------------------
% 2.88/1.43  #Ref     : 0
% 2.88/1.43  #Sup     : 289
% 2.88/1.43  #Fact    : 0
% 2.88/1.43  #Define  : 0
% 2.88/1.43  #Split   : 3
% 2.88/1.43  #Chain   : 0
% 2.88/1.43  #Close   : 0
% 2.88/1.43  
% 2.88/1.43  Ordering : KBO
% 2.88/1.43  
% 2.88/1.43  Simplification rules
% 2.88/1.43  ----------------------
% 2.88/1.43  #Subsume      : 6
% 2.88/1.43  #Demod        : 159
% 2.88/1.43  #Tautology    : 217
% 2.88/1.43  #SimpNegUnit  : 9
% 2.88/1.43  #BackRed      : 9
% 2.88/1.43  
% 2.88/1.43  #Partial instantiations: 0
% 2.88/1.43  #Strategies tried      : 1
% 2.88/1.43  
% 2.88/1.43  Timing (in seconds)
% 2.88/1.43  ----------------------
% 2.88/1.44  Preprocessing        : 0.30
% 2.88/1.44  Parsing              : 0.16
% 2.88/1.44  CNF conversion       : 0.02
% 2.88/1.44  Main loop            : 0.37
% 2.88/1.44  Inferencing          : 0.13
% 2.88/1.44  Reduction            : 0.13
% 2.88/1.44  Demodulation         : 0.10
% 2.88/1.44  BG Simplification    : 0.02
% 2.88/1.44  Subsumption          : 0.06
% 2.88/1.44  Abstraction          : 0.02
% 2.88/1.44  MUC search           : 0.00
% 2.88/1.44  Cooper               : 0.00
% 2.88/1.44  Total                : 0.70
% 2.88/1.44  Index Insertion      : 0.00
% 2.88/1.44  Index Deletion       : 0.00
% 2.88/1.44  Index Matching       : 0.00
% 2.88/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
