%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:41 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 144 expanded)
%              Number of leaves         :   33 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :   62 ( 161 expanded)
%              Number of equality atoms :   23 (  76 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_64,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_20,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_49,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_5'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_48])).

tff(c_117,plain,(
    ! [B_46,A_47] :
      ( ~ v1_xboole_0(k2_xboole_0(B_46,A_47))
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_120,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_117])).

tff(c_122,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_120])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_126,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_122,c_4])).

tff(c_16,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_131,plain,(
    ! [A_13] : r1_xboole_0(A_13,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_16])).

tff(c_129,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_5'),'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_49])).

tff(c_145,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_204,plain,(
    ! [A_59,B_60] : k3_tarski(k2_tarski(A_59,B_60)) = k2_xboole_0(B_60,A_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_145])).

tff(c_46,plain,(
    ! [A_33,B_34] : k3_tarski(k2_tarski(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_227,plain,(
    ! [B_61,A_62] : k2_xboole_0(B_61,A_62) = k2_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_46])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_290,plain,(
    ! [A_63,B_64] : r1_tarski(A_63,k2_xboole_0(B_64,A_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_18])).

tff(c_302,plain,(
    r1_tarski('#skF_7','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_290])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_318,plain,(
    k3_xboole_0('#skF_7','#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_302,c_14])).

tff(c_8,plain,(
    ! [A_2,B_3,C_6] :
      ( ~ r1_xboole_0(A_2,B_3)
      | ~ r2_hidden(C_6,k3_xboole_0(A_2,B_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_322,plain,(
    ! [C_6] :
      ( ~ r1_xboole_0('#skF_7','#skF_7')
      | ~ r2_hidden(C_6,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_8])).

tff(c_326,plain,(
    ! [C_6] : ~ r2_hidden(C_6,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_322])).

tff(c_281,plain,(
    k2_xboole_0('#skF_7',k2_tarski('#skF_6','#skF_5')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_227])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ v1_xboole_0(k2_xboole_0(B_10,A_9))
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_344,plain,
    ( ~ v1_xboole_0('#skF_7')
    | v1_xboole_0(k2_tarski('#skF_6','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_12])).

tff(c_353,plain,(
    v1_xboole_0(k2_tarski('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_344])).

tff(c_130,plain,(
    ! [A_1] :
      ( A_1 = '#skF_7'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_4])).

tff(c_359,plain,(
    k2_tarski('#skF_6','#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_353,c_130])).

tff(c_24,plain,(
    ! [D_23,A_18] : r2_hidden(D_23,k2_tarski(A_18,D_23)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_375,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_24])).

tff(c_382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_326,c_375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.26  
% 2.15/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1
% 2.15/1.26  
% 2.15/1.26  %Foreground sorts:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Background operators:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Foreground operators:
% 2.15/1.26  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.15/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.15/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.15/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.26  
% 2.27/1.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.27/1.27  tff(f_68, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.27/1.27  tff(f_89, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.27/1.27  tff(f_58, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.27/1.27  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.27/1.27  tff(f_64, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.27/1.27  tff(f_85, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.27/1.27  tff(f_66, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.27/1.27  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.27/1.27  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.27/1.27  tff(f_77, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.27/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.27/1.27  tff(c_20, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.27/1.27  tff(c_48, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.27/1.27  tff(c_49, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_5'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_48])).
% 2.27/1.27  tff(c_117, plain, (![B_46, A_47]: (~v1_xboole_0(k2_xboole_0(B_46, A_47)) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.27/1.27  tff(c_120, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_49, c_117])).
% 2.27/1.27  tff(c_122, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_120])).
% 2.27/1.27  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.27/1.27  tff(c_126, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_122, c_4])).
% 2.27/1.27  tff(c_16, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.27/1.27  tff(c_131, plain, (![A_13]: (r1_xboole_0(A_13, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_16])).
% 2.27/1.27  tff(c_129, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_5'), '#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_49])).
% 2.27/1.27  tff(c_145, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.27/1.27  tff(c_204, plain, (![A_59, B_60]: (k3_tarski(k2_tarski(A_59, B_60))=k2_xboole_0(B_60, A_59))), inference(superposition, [status(thm), theory('equality')], [c_20, c_145])).
% 2.27/1.27  tff(c_46, plain, (![A_33, B_34]: (k3_tarski(k2_tarski(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.27/1.27  tff(c_227, plain, (![B_61, A_62]: (k2_xboole_0(B_61, A_62)=k2_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_204, c_46])).
% 2.27/1.27  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.27/1.27  tff(c_290, plain, (![A_63, B_64]: (r1_tarski(A_63, k2_xboole_0(B_64, A_63)))), inference(superposition, [status(thm), theory('equality')], [c_227, c_18])).
% 2.27/1.27  tff(c_302, plain, (r1_tarski('#skF_7', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_129, c_290])).
% 2.27/1.27  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.27/1.27  tff(c_318, plain, (k3_xboole_0('#skF_7', '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_302, c_14])).
% 2.27/1.27  tff(c_8, plain, (![A_2, B_3, C_6]: (~r1_xboole_0(A_2, B_3) | ~r2_hidden(C_6, k3_xboole_0(A_2, B_3)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.27/1.27  tff(c_322, plain, (![C_6]: (~r1_xboole_0('#skF_7', '#skF_7') | ~r2_hidden(C_6, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_318, c_8])).
% 2.27/1.27  tff(c_326, plain, (![C_6]: (~r2_hidden(C_6, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_322])).
% 2.27/1.27  tff(c_281, plain, (k2_xboole_0('#skF_7', k2_tarski('#skF_6', '#skF_5'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_129, c_227])).
% 2.27/1.27  tff(c_12, plain, (![B_10, A_9]: (~v1_xboole_0(k2_xboole_0(B_10, A_9)) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.27/1.27  tff(c_344, plain, (~v1_xboole_0('#skF_7') | v1_xboole_0(k2_tarski('#skF_6', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_281, c_12])).
% 2.27/1.27  tff(c_353, plain, (v1_xboole_0(k2_tarski('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_344])).
% 2.27/1.27  tff(c_130, plain, (![A_1]: (A_1='#skF_7' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_4])).
% 2.27/1.27  tff(c_359, plain, (k2_tarski('#skF_6', '#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_353, c_130])).
% 2.27/1.27  tff(c_24, plain, (![D_23, A_18]: (r2_hidden(D_23, k2_tarski(A_18, D_23)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.27/1.27  tff(c_375, plain, (r2_hidden('#skF_5', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_359, c_24])).
% 2.27/1.27  tff(c_382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_326, c_375])).
% 2.27/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.27  
% 2.27/1.27  Inference rules
% 2.27/1.27  ----------------------
% 2.27/1.27  #Ref     : 0
% 2.27/1.27  #Sup     : 84
% 2.27/1.27  #Fact    : 0
% 2.27/1.27  #Define  : 0
% 2.27/1.27  #Split   : 0
% 2.27/1.27  #Chain   : 0
% 2.27/1.27  #Close   : 0
% 2.27/1.27  
% 2.27/1.27  Ordering : KBO
% 2.27/1.27  
% 2.27/1.27  Simplification rules
% 2.27/1.27  ----------------------
% 2.27/1.27  #Subsume      : 0
% 2.27/1.27  #Demod        : 31
% 2.27/1.27  #Tautology    : 54
% 2.27/1.27  #SimpNegUnit  : 1
% 2.27/1.27  #BackRed      : 10
% 2.27/1.27  
% 2.27/1.27  #Partial instantiations: 0
% 2.27/1.27  #Strategies tried      : 1
% 2.27/1.27  
% 2.27/1.27  Timing (in seconds)
% 2.27/1.27  ----------------------
% 2.27/1.28  Preprocessing        : 0.31
% 2.27/1.28  Parsing              : 0.16
% 2.27/1.28  CNF conversion       : 0.02
% 2.27/1.28  Main loop            : 0.19
% 2.27/1.28  Inferencing          : 0.06
% 2.27/1.28  Reduction            : 0.07
% 2.27/1.28  Demodulation         : 0.06
% 2.27/1.28  BG Simplification    : 0.01
% 2.27/1.28  Subsumption          : 0.03
% 2.27/1.28  Abstraction          : 0.01
% 2.27/1.28  MUC search           : 0.00
% 2.27/1.28  Cooper               : 0.00
% 2.27/1.28  Total                : 0.53
% 2.27/1.28  Index Insertion      : 0.00
% 2.27/1.28  Index Deletion       : 0.00
% 2.27/1.28  Index Matching       : 0.00
% 2.27/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
