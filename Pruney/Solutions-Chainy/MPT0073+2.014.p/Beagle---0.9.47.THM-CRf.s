%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:26 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 116 expanded)
%              Number of leaves         :   19 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :   65 ( 183 expanded)
%              Number of equality atoms :   35 ( 106 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( ~ ( ~ r1_xboole_0(A,A)
            & A = k1_xboole_0 )
        & ~ ( A != k1_xboole_0
            & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_18,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_41,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_44,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_24])).

tff(c_71,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_6])).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_45,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_14])).

tff(c_20,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_70,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_20])).

tff(c_10,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42,plain,(
    ! [A_9] : k4_xboole_0(A_9,'#skF_4') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_10])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_43,plain,(
    ! [A_8] : k3_xboole_0(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_41,c_8])).

tff(c_73,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_88,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_73])).

tff(c_110,plain,(
    ! [A_26] : k4_xboole_0(A_26,A_26) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_88])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_115,plain,(
    ! [A_26] : k4_xboole_0(A_26,'#skF_4') = k3_xboole_0(A_26,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_12])).

tff(c_131,plain,(
    ! [A_27] : k3_xboole_0(A_27,A_27) = A_27 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_115])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_166,plain,(
    ! [A_30,C_31] :
      ( ~ r1_xboole_0(A_30,A_30)
      | ~ r2_hidden(C_31,A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_4])).

tff(c_174,plain,(
    ! [C_32] : ~ r2_hidden(C_32,'#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_166])).

tff(c_178,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_71,c_174])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_178])).

tff(c_183,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_205,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_220,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_205])).

tff(c_224,plain,(
    ! [A_40] : k4_xboole_0(A_40,A_40) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_220])).

tff(c_229,plain,(
    ! [A_40] : k4_xboole_0(A_40,k1_xboole_0) = k3_xboole_0(A_40,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_12])).

tff(c_245,plain,(
    ! [A_41] : k3_xboole_0(A_41,A_41) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_229])).

tff(c_267,plain,(
    ! [A_42,C_43] :
      ( ~ r1_xboole_0(A_42,A_42)
      | ~ r2_hidden(C_43,A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_4])).

tff(c_275,plain,(
    ! [C_44] : ~ r2_hidden(C_44,'#skF_3') ),
    inference(resolution,[status(thm)],[c_183,c_267])).

tff(c_279,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_275])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_279])).

tff(c_284,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_286,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_14])).

tff(c_285,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_291,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_285])).

tff(c_22,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_291,c_284,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.19  
% 1.89/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.19  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.89/1.19  
% 1.89/1.19  %Foreground sorts:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Background operators:
% 1.89/1.19  
% 1.89/1.19  
% 1.89/1.19  %Foreground operators:
% 1.89/1.19  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.19  
% 1.89/1.20  tff(f_68, negated_conjecture, ~(![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.89/1.20  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.89/1.20  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.89/1.20  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.89/1.20  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.89/1.20  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.89/1.20  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.89/1.20  tff(c_18, plain, (k1_xboole_0!='#skF_3' | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.89/1.20  tff(c_24, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_18])).
% 1.89/1.20  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.89/1.20  tff(c_16, plain, (r1_xboole_0('#skF_3', '#skF_3') | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.89/1.20  tff(c_41, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_16])).
% 1.89/1.20  tff(c_44, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_24])).
% 1.89/1.20  tff(c_71, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_6])).
% 1.89/1.20  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.89/1.20  tff(c_45, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_14])).
% 1.89/1.20  tff(c_20, plain, (r1_xboole_0('#skF_3', '#skF_3') | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.89/1.20  tff(c_70, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_20])).
% 1.89/1.20  tff(c_10, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.89/1.20  tff(c_42, plain, (![A_9]: (k4_xboole_0(A_9, '#skF_4')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_41, c_10])).
% 1.89/1.20  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.89/1.20  tff(c_43, plain, (![A_8]: (k3_xboole_0(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_41, c_8])).
% 1.89/1.20  tff(c_73, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.89/1.20  tff(c_88, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_73])).
% 1.89/1.20  tff(c_110, plain, (![A_26]: (k4_xboole_0(A_26, A_26)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_43, c_88])).
% 1.89/1.20  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.89/1.20  tff(c_115, plain, (![A_26]: (k4_xboole_0(A_26, '#skF_4')=k3_xboole_0(A_26, A_26))), inference(superposition, [status(thm), theory('equality')], [c_110, c_12])).
% 1.89/1.20  tff(c_131, plain, (![A_27]: (k3_xboole_0(A_27, A_27)=A_27)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_115])).
% 1.89/1.20  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.20  tff(c_166, plain, (![A_30, C_31]: (~r1_xboole_0(A_30, A_30) | ~r2_hidden(C_31, A_30))), inference(superposition, [status(thm), theory('equality')], [c_131, c_4])).
% 1.89/1.20  tff(c_174, plain, (![C_32]: (~r2_hidden(C_32, '#skF_3'))), inference(resolution, [status(thm)], [c_70, c_166])).
% 1.89/1.20  tff(c_178, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_71, c_174])).
% 1.89/1.20  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_178])).
% 1.89/1.20  tff(c_183, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_16])).
% 1.89/1.20  tff(c_205, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.89/1.20  tff(c_220, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_205])).
% 1.89/1.20  tff(c_224, plain, (![A_40]: (k4_xboole_0(A_40, A_40)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_220])).
% 1.89/1.20  tff(c_229, plain, (![A_40]: (k4_xboole_0(A_40, k1_xboole_0)=k3_xboole_0(A_40, A_40))), inference(superposition, [status(thm), theory('equality')], [c_224, c_12])).
% 1.89/1.20  tff(c_245, plain, (![A_41]: (k3_xboole_0(A_41, A_41)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_229])).
% 1.89/1.20  tff(c_267, plain, (![A_42, C_43]: (~r1_xboole_0(A_42, A_42) | ~r2_hidden(C_43, A_42))), inference(superposition, [status(thm), theory('equality')], [c_245, c_4])).
% 1.89/1.20  tff(c_275, plain, (![C_44]: (~r2_hidden(C_44, '#skF_3'))), inference(resolution, [status(thm)], [c_183, c_267])).
% 1.89/1.20  tff(c_279, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_275])).
% 1.89/1.20  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_279])).
% 1.89/1.20  tff(c_284, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_18])).
% 1.89/1.20  tff(c_286, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_284, c_14])).
% 1.89/1.20  tff(c_285, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_18])).
% 1.89/1.20  tff(c_291, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_284, c_285])).
% 1.89/1.20  tff(c_22, plain, (k1_xboole_0!='#skF_3' | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.89/1.20  tff(c_316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_286, c_291, c_284, c_22])).
% 1.89/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.20  
% 1.89/1.20  Inference rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Ref     : 0
% 1.89/1.20  #Sup     : 63
% 1.89/1.20  #Fact    : 0
% 1.89/1.20  #Define  : 0
% 1.89/1.20  #Split   : 2
% 1.89/1.20  #Chain   : 0
% 1.89/1.20  #Close   : 0
% 1.89/1.20  
% 1.89/1.20  Ordering : KBO
% 1.89/1.20  
% 1.89/1.20  Simplification rules
% 1.89/1.20  ----------------------
% 1.89/1.20  #Subsume      : 4
% 1.89/1.20  #Demod        : 25
% 1.89/1.20  #Tautology    : 43
% 1.89/1.20  #SimpNegUnit  : 3
% 1.89/1.20  #BackRed      : 5
% 1.89/1.20  
% 1.89/1.20  #Partial instantiations: 0
% 1.89/1.20  #Strategies tried      : 1
% 1.89/1.20  
% 1.89/1.20  Timing (in seconds)
% 1.89/1.20  ----------------------
% 1.89/1.21  Preprocessing        : 0.28
% 1.89/1.21  Parsing              : 0.14
% 1.89/1.21  CNF conversion       : 0.02
% 1.89/1.21  Main loop            : 0.17
% 1.89/1.21  Inferencing          : 0.07
% 1.89/1.21  Reduction            : 0.05
% 1.89/1.21  Demodulation         : 0.04
% 1.89/1.21  BG Simplification    : 0.01
% 1.89/1.21  Subsumption          : 0.02
% 1.89/1.21  Abstraction          : 0.01
% 1.89/1.21  MUC search           : 0.00
% 1.89/1.21  Cooper               : 0.00
% 1.89/1.21  Total                : 0.48
% 1.89/1.21  Index Insertion      : 0.00
% 1.89/1.21  Index Deletion       : 0.00
% 1.89/1.21  Index Matching       : 0.00
% 1.89/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
