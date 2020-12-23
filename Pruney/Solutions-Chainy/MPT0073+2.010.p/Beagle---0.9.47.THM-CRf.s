%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:26 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 139 expanded)
%              Number of leaves         :   14 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 233 expanded)
%              Number of equality atoms :   44 ( 153 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A] :
        ( ~ ( ~ r1_xboole_0(A,A)
            & A = k1_xboole_0 )
        & ~ ( A != k1_xboole_0
            & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_14,plain,
    ( k1_xboole_0 != '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_19,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_175,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_160])).

tff(c_179,plain,(
    ! [A_28] : k4_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_175])).

tff(c_10,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_184,plain,(
    ! [A_28] : k4_xboole_0(A_28,k1_xboole_0) = k3_xboole_0(A_28,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_10])).

tff(c_196,plain,(
    ! [A_28] : k3_xboole_0(A_28,A_28) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_184])).

tff(c_12,plain,
    ( r1_xboole_0('#skF_1','#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_39,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_19])).

tff(c_38,plain,(
    ! [A_4] : k4_xboole_0(A_4,'#skF_2') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8])).

tff(c_37,plain,(
    ! [A_3] : k3_xboole_0(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_6])).

tff(c_100,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_115,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_100])).

tff(c_119,plain,(
    ! [A_21] : k4_xboole_0(A_21,A_21) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_115])).

tff(c_124,plain,(
    ! [A_21] : k4_xboole_0(A_21,'#skF_2') = k3_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_10])).

tff(c_136,plain,(
    ! [A_21] : k3_xboole_0(A_21,A_21) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_124])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(A_13,B_14)
      | k3_xboole_0(A_13,B_14) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4])).

tff(c_16,plain,
    ( r1_xboole_0('#skF_1','#skF_1')
    | ~ r1_xboole_0('#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_61,plain,(
    ~ r1_xboole_0('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_71,plain,(
    k3_xboole_0('#skF_2','#skF_2') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_65,c_61])).

tff(c_76,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_71])).

tff(c_77,plain,(
    r1_xboole_0('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = '#skF_2'
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2])).

tff(c_95,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_77,c_82])).

tff(c_140,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_95])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_140])).

tff(c_143,plain,(
    r1_xboole_0('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_147,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_155,plain,(
    k3_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_143,c_147])).

tff(c_200,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_155])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19,c_200])).

tff(c_204,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_228,plain,(
    ! [A_3] : k3_xboole_0(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_204,c_6])).

tff(c_244,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(A_33,B_34)
      | k3_xboole_0(A_33,B_34) != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_4])).

tff(c_203,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_209,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_203])).

tff(c_18,plain,
    ( k1_xboole_0 != '#skF_1'
    | ~ r1_xboole_0('#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_238,plain,(
    ~ r1_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_209,c_204,c_18])).

tff(c_250,plain,(
    k3_xboole_0('#skF_1','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_244,c_238])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_250])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:12:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.73/1.16  
% 1.73/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.16  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.83/1.16  
% 1.83/1.16  %Foreground sorts:
% 1.83/1.16  
% 1.83/1.16  
% 1.83/1.16  %Background operators:
% 1.83/1.16  
% 1.83/1.16  
% 1.83/1.16  %Foreground operators:
% 1.83/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.83/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.83/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.83/1.16  
% 1.83/1.17  tff(f_48, negated_conjecture, ~(![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.83/1.17  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.83/1.17  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.83/1.17  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.83/1.17  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.83/1.17  tff(c_14, plain, (k1_xboole_0!='#skF_1' | k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.83/1.17  tff(c_19, plain, (k1_xboole_0!='#skF_1'), inference(splitLeft, [status(thm)], [c_14])).
% 1.83/1.17  tff(c_8, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.83/1.17  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.17  tff(c_160, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.17  tff(c_175, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_160])).
% 1.83/1.17  tff(c_179, plain, (![A_28]: (k4_xboole_0(A_28, A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_175])).
% 1.83/1.17  tff(c_10, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.17  tff(c_184, plain, (![A_28]: (k4_xboole_0(A_28, k1_xboole_0)=k3_xboole_0(A_28, A_28))), inference(superposition, [status(thm), theory('equality')], [c_179, c_10])).
% 1.83/1.17  tff(c_196, plain, (![A_28]: (k3_xboole_0(A_28, A_28)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_184])).
% 1.83/1.17  tff(c_12, plain, (r1_xboole_0('#skF_1', '#skF_1') | k1_xboole_0='#skF_2'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.83/1.17  tff(c_36, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_12])).
% 1.83/1.17  tff(c_39, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_19])).
% 1.83/1.17  tff(c_38, plain, (![A_4]: (k4_xboole_0(A_4, '#skF_2')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_8])).
% 1.83/1.17  tff(c_37, plain, (![A_3]: (k3_xboole_0(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_6])).
% 1.83/1.17  tff(c_100, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.83/1.17  tff(c_115, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_100])).
% 1.83/1.17  tff(c_119, plain, (![A_21]: (k4_xboole_0(A_21, A_21)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_115])).
% 1.83/1.17  tff(c_124, plain, (![A_21]: (k4_xboole_0(A_21, '#skF_2')=k3_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_119, c_10])).
% 1.83/1.17  tff(c_136, plain, (![A_21]: (k3_xboole_0(A_21, A_21)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_124])).
% 1.83/1.17  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.17  tff(c_65, plain, (![A_13, B_14]: (r1_xboole_0(A_13, B_14) | k3_xboole_0(A_13, B_14)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4])).
% 1.83/1.17  tff(c_16, plain, (r1_xboole_0('#skF_1', '#skF_1') | ~r1_xboole_0('#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.83/1.17  tff(c_61, plain, (~r1_xboole_0('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_16])).
% 1.83/1.17  tff(c_71, plain, (k3_xboole_0('#skF_2', '#skF_2')!='#skF_2'), inference(resolution, [status(thm)], [c_65, c_61])).
% 1.83/1.17  tff(c_76, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37, c_71])).
% 1.83/1.17  tff(c_77, plain, (r1_xboole_0('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_16])).
% 1.83/1.17  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.17  tff(c_82, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)='#skF_2' | ~r1_xboole_0(A_17, B_18))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2])).
% 1.83/1.17  tff(c_95, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_77, c_82])).
% 1.83/1.17  tff(c_140, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_95])).
% 1.83/1.17  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_140])).
% 1.83/1.17  tff(c_143, plain, (r1_xboole_0('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_12])).
% 1.83/1.17  tff(c_147, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.83/1.17  tff(c_155, plain, (k3_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_143, c_147])).
% 1.83/1.17  tff(c_200, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_155])).
% 1.83/1.17  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19, c_200])).
% 1.83/1.17  tff(c_204, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_14])).
% 1.83/1.17  tff(c_228, plain, (![A_3]: (k3_xboole_0(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_204, c_6])).
% 1.83/1.17  tff(c_244, plain, (![A_33, B_34]: (r1_xboole_0(A_33, B_34) | k3_xboole_0(A_33, B_34)!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_4])).
% 1.83/1.17  tff(c_203, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_14])).
% 1.83/1.17  tff(c_209, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_204, c_203])).
% 1.83/1.17  tff(c_18, plain, (k1_xboole_0!='#skF_1' | ~r1_xboole_0('#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.83/1.17  tff(c_238, plain, (~r1_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_209, c_204, c_18])).
% 1.83/1.17  tff(c_250, plain, (k3_xboole_0('#skF_1', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_244, c_238])).
% 1.83/1.17  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_228, c_250])).
% 1.83/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.17  
% 1.83/1.17  Inference rules
% 1.83/1.17  ----------------------
% 1.83/1.17  #Ref     : 0
% 1.83/1.17  #Sup     : 53
% 1.83/1.17  #Fact    : 0
% 1.83/1.17  #Define  : 0
% 1.83/1.17  #Split   : 3
% 1.83/1.17  #Chain   : 0
% 1.83/1.17  #Close   : 0
% 1.83/1.17  
% 1.83/1.17  Ordering : KBO
% 1.83/1.17  
% 1.83/1.17  Simplification rules
% 1.83/1.17  ----------------------
% 1.83/1.17  #Subsume      : 3
% 1.83/1.17  #Demod        : 32
% 1.83/1.17  #Tautology    : 43
% 1.83/1.17  #SimpNegUnit  : 3
% 1.83/1.17  #BackRed      : 6
% 1.83/1.17  
% 1.83/1.17  #Partial instantiations: 0
% 1.83/1.17  #Strategies tried      : 1
% 1.83/1.17  
% 1.83/1.17  Timing (in seconds)
% 1.83/1.17  ----------------------
% 1.83/1.18  Preprocessing        : 0.25
% 1.83/1.18  Parsing              : 0.13
% 1.83/1.18  CNF conversion       : 0.01
% 1.83/1.18  Main loop            : 0.15
% 1.83/1.18  Inferencing          : 0.06
% 1.83/1.18  Reduction            : 0.05
% 1.83/1.18  Demodulation         : 0.03
% 1.83/1.18  BG Simplification    : 0.01
% 1.83/1.18  Subsumption          : 0.02
% 1.83/1.18  Abstraction          : 0.01
% 1.83/1.18  MUC search           : 0.00
% 1.83/1.18  Cooper               : 0.00
% 1.83/1.18  Total                : 0.43
% 1.83/1.18  Index Insertion      : 0.00
% 1.83/1.18  Index Deletion       : 0.00
% 1.83/1.18  Index Matching       : 0.00
% 1.83/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
