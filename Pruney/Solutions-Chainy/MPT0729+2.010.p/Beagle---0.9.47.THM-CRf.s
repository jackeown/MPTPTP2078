%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:59 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :   51 (  74 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   66 ( 105 expanded)
%              Number of equality atoms :   22 (  45 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( k1_ordinal1(A) = k1_ordinal1(B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

tff(f_58,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_56,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_16] : r2_hidden(A_16,k1_ordinal1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,(
    k1_ordinal1('#skF_2') = k1_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_tarski(A_15)) = k1_ordinal1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_155,plain,(
    ! [B_44,A_45] :
      ( k4_xboole_0(k2_xboole_0(B_44,k1_tarski(A_45)),k1_tarski(A_45)) = B_44
      | r2_hidden(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_180,plain,(
    ! [A_46] :
      ( k4_xboole_0(k1_ordinal1(A_46),k1_tarski(A_46)) = A_46
      | r2_hidden(A_46,A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_155])).

tff(c_198,plain,
    ( k4_xboole_0(k1_ordinal1('#skF_1'),k1_tarski('#skF_2')) = '#skF_2'
    | r2_hidden('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_180])).

tff(c_201,plain,(
    r2_hidden('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_216,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_201,c_28])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_216])).

tff(c_223,plain,(
    k4_xboole_0(k1_ordinal1('#skF_1'),k1_tarski('#skF_2')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14] :
      ( r2_hidden(A_12,k4_xboole_0(B_13,k1_tarski(C_14)))
      | C_14 = A_12
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_273,plain,(
    ! [A_53] :
      ( r2_hidden(A_53,'#skF_2')
      | A_53 = '#skF_2'
      | ~ r2_hidden(A_53,k1_ordinal1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_18])).

tff(c_283,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_273])).

tff(c_291,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_283])).

tff(c_39,plain,(
    ! [A_20] : r2_hidden(A_20,k1_ordinal1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    r2_hidden('#skF_2',k1_ordinal1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_39])).

tff(c_177,plain,(
    ! [A_15] :
      ( k4_xboole_0(k1_ordinal1(A_15),k1_tarski(A_15)) = A_15
      | r2_hidden(A_15,A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_155])).

tff(c_132,plain,(
    ! [A_41,B_42,C_43] :
      ( r2_hidden(A_41,k4_xboole_0(B_42,k1_tarski(C_43)))
      | C_43 = A_41
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_299,plain,(
    ! [B_54,C_55,A_56] :
      ( ~ r2_hidden(k4_xboole_0(B_54,k1_tarski(C_55)),A_56)
      | C_55 = A_56
      | ~ r2_hidden(A_56,B_54) ) ),
    inference(resolution,[status(thm)],[c_132,c_2])).

tff(c_1114,plain,(
    ! [A_102,A_103] :
      ( ~ r2_hidden(A_102,A_103)
      | A_103 = A_102
      | ~ r2_hidden(A_103,k1_ordinal1(A_102))
      | r2_hidden(A_102,A_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_299])).

tff(c_1120,plain,
    ( ~ r2_hidden('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1'
    | r2_hidden('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1114])).

tff(c_1129,plain,
    ( '#skF_2' = '#skF_1'
    | r2_hidden('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_1120])).

tff(c_1130,plain,(
    r2_hidden('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1129])).

tff(c_1139,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_1130,c_28])).

tff(c_1147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:03:34 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/2.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/2.06  
% 4.07/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.07/2.06  %$ r2_hidden > r1_tarski > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 4.07/2.06  
% 4.07/2.06  %Foreground sorts:
% 4.07/2.06  
% 4.07/2.06  
% 4.07/2.06  %Background operators:
% 4.07/2.06  
% 4.07/2.06  
% 4.07/2.06  %Foreground operators:
% 4.07/2.06  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 4.07/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.07/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.07/2.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.07/2.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.07/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.07/2.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.07/2.06  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.07/2.06  tff('#skF_2', type, '#skF_2': $i).
% 4.07/2.06  tff('#skF_1', type, '#skF_1': $i).
% 4.07/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.07/2.06  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.07/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.07/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.07/2.06  
% 4.18/2.08  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.18/2.08  tff(f_68, negated_conjecture, ~(![A, B]: ((k1_ordinal1(A) = k1_ordinal1(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_ordinal1)).
% 4.18/2.08  tff(f_58, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 4.18/2.08  tff(f_56, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 4.18/2.08  tff(f_47, axiom, (![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 4.18/2.08  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.18/2.08  tff(f_54, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 4.18/2.08  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 4.18/2.08  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.18/2.08  tff(c_30, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.18/2.08  tff(c_26, plain, (![A_16]: (r2_hidden(A_16, k1_ordinal1(A_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.18/2.08  tff(c_32, plain, (k1_ordinal1('#skF_2')=k1_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.18/2.08  tff(c_24, plain, (![A_15]: (k2_xboole_0(A_15, k1_tarski(A_15))=k1_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.18/2.08  tff(c_155, plain, (![B_44, A_45]: (k4_xboole_0(k2_xboole_0(B_44, k1_tarski(A_45)), k1_tarski(A_45))=B_44 | r2_hidden(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.18/2.08  tff(c_180, plain, (![A_46]: (k4_xboole_0(k1_ordinal1(A_46), k1_tarski(A_46))=A_46 | r2_hidden(A_46, A_46))), inference(superposition, [status(thm), theory('equality')], [c_24, c_155])).
% 4.18/2.08  tff(c_198, plain, (k4_xboole_0(k1_ordinal1('#skF_1'), k1_tarski('#skF_2'))='#skF_2' | r2_hidden('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32, c_180])).
% 4.18/2.08  tff(c_201, plain, (r2_hidden('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_198])).
% 4.18/2.08  tff(c_28, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.18/2.08  tff(c_216, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_201, c_28])).
% 4.18/2.08  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_216])).
% 4.18/2.08  tff(c_223, plain, (k4_xboole_0(k1_ordinal1('#skF_1'), k1_tarski('#skF_2'))='#skF_2'), inference(splitRight, [status(thm)], [c_198])).
% 4.18/2.08  tff(c_18, plain, (![A_12, B_13, C_14]: (r2_hidden(A_12, k4_xboole_0(B_13, k1_tarski(C_14))) | C_14=A_12 | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.18/2.08  tff(c_273, plain, (![A_53]: (r2_hidden(A_53, '#skF_2') | A_53='#skF_2' | ~r2_hidden(A_53, k1_ordinal1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_223, c_18])).
% 4.18/2.08  tff(c_283, plain, (r2_hidden('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_26, c_273])).
% 4.18/2.08  tff(c_291, plain, (r2_hidden('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_30, c_283])).
% 4.18/2.08  tff(c_39, plain, (![A_20]: (r2_hidden(A_20, k1_ordinal1(A_20)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.18/2.08  tff(c_42, plain, (r2_hidden('#skF_2', k1_ordinal1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_39])).
% 4.18/2.08  tff(c_177, plain, (![A_15]: (k4_xboole_0(k1_ordinal1(A_15), k1_tarski(A_15))=A_15 | r2_hidden(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_24, c_155])).
% 4.18/2.08  tff(c_132, plain, (![A_41, B_42, C_43]: (r2_hidden(A_41, k4_xboole_0(B_42, k1_tarski(C_43))) | C_43=A_41 | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.18/2.08  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.18/2.08  tff(c_299, plain, (![B_54, C_55, A_56]: (~r2_hidden(k4_xboole_0(B_54, k1_tarski(C_55)), A_56) | C_55=A_56 | ~r2_hidden(A_56, B_54))), inference(resolution, [status(thm)], [c_132, c_2])).
% 4.18/2.08  tff(c_1114, plain, (![A_102, A_103]: (~r2_hidden(A_102, A_103) | A_103=A_102 | ~r2_hidden(A_103, k1_ordinal1(A_102)) | r2_hidden(A_102, A_102))), inference(superposition, [status(thm), theory('equality')], [c_177, c_299])).
% 4.18/2.08  tff(c_1120, plain, (~r2_hidden('#skF_1', '#skF_2') | '#skF_2'='#skF_1' | r2_hidden('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_1114])).
% 4.18/2.08  tff(c_1129, plain, ('#skF_2'='#skF_1' | r2_hidden('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_1120])).
% 4.18/2.08  tff(c_1130, plain, (r2_hidden('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_30, c_1129])).
% 4.18/2.08  tff(c_1139, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_1130, c_28])).
% 4.18/2.08  tff(c_1147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1139])).
% 4.18/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.18/2.08  
% 4.18/2.08  Inference rules
% 4.18/2.08  ----------------------
% 4.18/2.08  #Ref     : 0
% 4.18/2.08  #Sup     : 247
% 4.18/2.08  #Fact    : 0
% 4.18/2.08  #Define  : 0
% 4.18/2.08  #Split   : 1
% 4.18/2.08  #Chain   : 0
% 4.18/2.08  #Close   : 0
% 4.18/2.08  
% 4.18/2.08  Ordering : KBO
% 4.18/2.08  
% 4.18/2.08  Simplification rules
% 4.18/2.08  ----------------------
% 4.18/2.08  #Subsume      : 82
% 4.18/2.08  #Demod        : 34
% 4.18/2.08  #Tautology    : 32
% 4.18/2.08  #SimpNegUnit  : 9
% 4.18/2.08  #BackRed      : 0
% 4.18/2.08  
% 4.18/2.08  #Partial instantiations: 0
% 4.18/2.08  #Strategies tried      : 1
% 4.18/2.08  
% 4.18/2.08  Timing (in seconds)
% 4.18/2.08  ----------------------
% 4.18/2.08  Preprocessing        : 0.45
% 4.18/2.08  Parsing              : 0.23
% 4.18/2.09  CNF conversion       : 0.03
% 4.18/2.09  Main loop            : 0.71
% 4.18/2.09  Inferencing          : 0.24
% 4.18/2.09  Reduction            : 0.21
% 4.18/2.09  Demodulation         : 0.14
% 4.18/2.09  BG Simplification    : 0.03
% 4.18/2.09  Subsumption          : 0.17
% 4.18/2.09  Abstraction          : 0.03
% 4.18/2.09  MUC search           : 0.00
% 4.18/2.09  Cooper               : 0.00
% 4.18/2.09  Total                : 1.21
% 4.18/2.09  Index Insertion      : 0.00
% 4.18/2.09  Index Deletion       : 0.00
% 4.18/2.09  Index Matching       : 0.00
% 4.18/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
