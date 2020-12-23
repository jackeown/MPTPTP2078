%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:49 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   50 (  85 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   71 ( 169 expanded)
%              Number of equality atoms :   25 (  45 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_209,plain,(
    ! [D_51,A_52,B_53] :
      ( ~ r2_hidden(D_51,'#skF_2'(A_52,B_53))
      | ~ r2_hidden(D_51,B_53)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_596,plain,(
    ! [A_88,B_89,B_90] :
      ( ~ r2_hidden('#skF_1'('#skF_2'(A_88,B_89),B_90),B_89)
      | ~ r2_hidden(A_88,B_89)
      | r1_xboole_0('#skF_2'(A_88,B_89),B_90) ) ),
    inference(resolution,[status(thm)],[c_10,c_209])).

tff(c_663,plain,(
    ! [A_97,B_98] :
      ( ~ r2_hidden(A_97,B_98)
      | r1_xboole_0('#skF_2'(A_97,B_98),B_98) ) ),
    inference(resolution,[status(thm)],[c_8,c_596])).

tff(c_45,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_2'(A_28,B_29),B_29)
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [B_19] :
      ( ~ r1_xboole_0(B_19,'#skF_3')
      | ~ r2_hidden(B_19,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_50,plain,(
    ! [A_28] :
      ( ~ r1_xboole_0('#skF_2'(A_28,'#skF_3'),'#skF_3')
      | ~ r2_hidden(A_28,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_45,c_20])).

tff(c_676,plain,(
    ! [A_99] : ~ r2_hidden(A_99,'#skF_3') ),
    inference(resolution,[status(thm)],[c_663,c_50])).

tff(c_709,plain,(
    ! [B_101] : r1_xboole_0('#skF_3',B_101) ),
    inference(resolution,[status(thm)],[c_10,c_676])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_718,plain,(
    ! [B_102] : k3_xboole_0('#skF_3',B_102) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_709,c_2])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_51,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_69,plain,(
    ! [A_32] : k4_xboole_0(A_32,A_32) = k3_xboole_0(A_32,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_51])).

tff(c_79,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_115,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,B_39)
      | ~ r2_hidden(C_40,A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_163,plain,(
    ! [C_47,B_48,A_49] :
      ( ~ r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | k3_xboole_0(A_49,B_48) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_115])).

tff(c_277,plain,(
    ! [A_62,B_63,A_64] :
      ( ~ r2_hidden('#skF_1'(A_62,B_63),A_64)
      | k3_xboole_0(A_64,A_62) != k1_xboole_0
      | r1_xboole_0(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_10,c_163])).

tff(c_306,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,A_67) != k1_xboole_0
      | r1_xboole_0(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_10,c_277])).

tff(c_310,plain,(
    ! [B_69] : r1_xboole_0(k1_xboole_0,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_306])).

tff(c_317,plain,(
    ! [B_69] : k3_xboole_0(k1_xboole_0,B_69) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_310,c_2])).

tff(c_286,plain,(
    ! [B_65,A_66] :
      ( k3_xboole_0(B_65,A_66) != k1_xboole_0
      | r1_xboole_0(A_66,B_65) ) ),
    inference(resolution,[status(thm)],[c_8,c_277])).

tff(c_360,plain,(
    ! [A_73,B_74] :
      ( k3_xboole_0(A_73,B_74) = k1_xboole_0
      | k3_xboole_0(B_74,A_73) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_286,c_2])).

tff(c_363,plain,(
    ! [B_69] : k3_xboole_0(B_69,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_360])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_75,plain,(
    ! [A_32] : k4_xboole_0(A_32,k3_xboole_0(A_32,k1_xboole_0)) = k3_xboole_0(A_32,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_14])).

tff(c_371,plain,(
    ! [A_32] : k4_xboole_0(A_32,k1_xboole_0) = k3_xboole_0(A_32,A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_75])).

tff(c_373,plain,(
    ! [A_32] : k3_xboole_0(A_32,A_32) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_371])).

tff(c_730,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_718,c_373])).

tff(c_756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_730])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.52  
% 2.60/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.52  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.60/1.52  
% 2.60/1.52  %Foreground sorts:
% 2.60/1.52  
% 2.60/1.52  
% 2.60/1.52  %Background operators:
% 2.60/1.52  
% 2.60/1.52  
% 2.60/1.52  %Foreground operators:
% 2.60/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.60/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.60/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.60/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.60/1.52  
% 2.77/1.53  tff(f_75, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.77/1.53  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.77/1.53  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 2.77/1.53  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.77/1.53  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.77/1.53  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.77/1.53  tff(c_22, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.77/1.53  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.77/1.53  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.77/1.53  tff(c_209, plain, (![D_51, A_52, B_53]: (~r2_hidden(D_51, '#skF_2'(A_52, B_53)) | ~r2_hidden(D_51, B_53) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.77/1.53  tff(c_596, plain, (![A_88, B_89, B_90]: (~r2_hidden('#skF_1'('#skF_2'(A_88, B_89), B_90), B_89) | ~r2_hidden(A_88, B_89) | r1_xboole_0('#skF_2'(A_88, B_89), B_90))), inference(resolution, [status(thm)], [c_10, c_209])).
% 2.77/1.53  tff(c_663, plain, (![A_97, B_98]: (~r2_hidden(A_97, B_98) | r1_xboole_0('#skF_2'(A_97, B_98), B_98))), inference(resolution, [status(thm)], [c_8, c_596])).
% 2.77/1.53  tff(c_45, plain, (![A_28, B_29]: (r2_hidden('#skF_2'(A_28, B_29), B_29) | ~r2_hidden(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.77/1.53  tff(c_20, plain, (![B_19]: (~r1_xboole_0(B_19, '#skF_3') | ~r2_hidden(B_19, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.77/1.53  tff(c_50, plain, (![A_28]: (~r1_xboole_0('#skF_2'(A_28, '#skF_3'), '#skF_3') | ~r2_hidden(A_28, '#skF_3'))), inference(resolution, [status(thm)], [c_45, c_20])).
% 2.77/1.53  tff(c_676, plain, (![A_99]: (~r2_hidden(A_99, '#skF_3'))), inference(resolution, [status(thm)], [c_663, c_50])).
% 2.77/1.53  tff(c_709, plain, (![B_101]: (r1_xboole_0('#skF_3', B_101))), inference(resolution, [status(thm)], [c_10, c_676])).
% 2.77/1.53  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.53  tff(c_718, plain, (![B_102]: (k3_xboole_0('#skF_3', B_102)=k1_xboole_0)), inference(resolution, [status(thm)], [c_709, c_2])).
% 2.77/1.53  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.77/1.53  tff(c_51, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.77/1.53  tff(c_69, plain, (![A_32]: (k4_xboole_0(A_32, A_32)=k3_xboole_0(A_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_51])).
% 2.77/1.53  tff(c_79, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_69, c_12])).
% 2.77/1.53  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.53  tff(c_115, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, B_39) | ~r2_hidden(C_40, A_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.77/1.53  tff(c_163, plain, (![C_47, B_48, A_49]: (~r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | k3_xboole_0(A_49, B_48)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_115])).
% 2.77/1.53  tff(c_277, plain, (![A_62, B_63, A_64]: (~r2_hidden('#skF_1'(A_62, B_63), A_64) | k3_xboole_0(A_64, A_62)!=k1_xboole_0 | r1_xboole_0(A_62, B_63))), inference(resolution, [status(thm)], [c_10, c_163])).
% 2.77/1.53  tff(c_306, plain, (![A_67, B_68]: (k3_xboole_0(A_67, A_67)!=k1_xboole_0 | r1_xboole_0(A_67, B_68))), inference(resolution, [status(thm)], [c_10, c_277])).
% 2.77/1.53  tff(c_310, plain, (![B_69]: (r1_xboole_0(k1_xboole_0, B_69))), inference(superposition, [status(thm), theory('equality')], [c_79, c_306])).
% 2.77/1.53  tff(c_317, plain, (![B_69]: (k3_xboole_0(k1_xboole_0, B_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_310, c_2])).
% 2.77/1.53  tff(c_286, plain, (![B_65, A_66]: (k3_xboole_0(B_65, A_66)!=k1_xboole_0 | r1_xboole_0(A_66, B_65))), inference(resolution, [status(thm)], [c_8, c_277])).
% 2.77/1.53  tff(c_360, plain, (![A_73, B_74]: (k3_xboole_0(A_73, B_74)=k1_xboole_0 | k3_xboole_0(B_74, A_73)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_286, c_2])).
% 2.77/1.53  tff(c_363, plain, (![B_69]: (k3_xboole_0(B_69, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_317, c_360])).
% 2.77/1.53  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.77/1.53  tff(c_75, plain, (![A_32]: (k4_xboole_0(A_32, k3_xboole_0(A_32, k1_xboole_0))=k3_xboole_0(A_32, A_32))), inference(superposition, [status(thm), theory('equality')], [c_69, c_14])).
% 2.77/1.53  tff(c_371, plain, (![A_32]: (k4_xboole_0(A_32, k1_xboole_0)=k3_xboole_0(A_32, A_32))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_75])).
% 2.77/1.53  tff(c_373, plain, (![A_32]: (k3_xboole_0(A_32, A_32)=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_371])).
% 2.77/1.53  tff(c_730, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_718, c_373])).
% 2.77/1.53  tff(c_756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_730])).
% 2.77/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.53  
% 2.77/1.53  Inference rules
% 2.77/1.53  ----------------------
% 2.77/1.53  #Ref     : 0
% 2.77/1.53  #Sup     : 170
% 2.77/1.53  #Fact    : 0
% 2.77/1.53  #Define  : 0
% 2.77/1.53  #Split   : 0
% 2.77/1.53  #Chain   : 0
% 2.77/1.53  #Close   : 0
% 2.77/1.53  
% 2.77/1.53  Ordering : KBO
% 2.77/1.53  
% 2.77/1.53  Simplification rules
% 2.77/1.53  ----------------------
% 2.77/1.53  #Subsume      : 23
% 2.77/1.53  #Demod        : 67
% 2.77/1.53  #Tautology    : 84
% 2.77/1.53  #SimpNegUnit  : 1
% 2.77/1.53  #BackRed      : 5
% 2.77/1.53  
% 2.77/1.53  #Partial instantiations: 0
% 2.77/1.53  #Strategies tried      : 1
% 2.77/1.53  
% 2.77/1.53  Timing (in seconds)
% 2.77/1.53  ----------------------
% 2.77/1.54  Preprocessing        : 0.37
% 2.77/1.54  Parsing              : 0.22
% 2.77/1.54  CNF conversion       : 0.02
% 2.77/1.54  Main loop            : 0.30
% 2.77/1.54  Inferencing          : 0.12
% 2.77/1.54  Reduction            : 0.08
% 2.77/1.54  Demodulation         : 0.06
% 2.77/1.54  BG Simplification    : 0.02
% 2.77/1.54  Subsumption          : 0.06
% 2.77/1.54  Abstraction          : 0.01
% 2.77/1.54  MUC search           : 0.00
% 2.77/1.54  Cooper               : 0.00
% 2.77/1.54  Total                : 0.70
% 2.77/1.54  Index Insertion      : 0.00
% 2.77/1.54  Index Deletion       : 0.00
% 2.77/1.54  Index Matching       : 0.00
% 2.77/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
