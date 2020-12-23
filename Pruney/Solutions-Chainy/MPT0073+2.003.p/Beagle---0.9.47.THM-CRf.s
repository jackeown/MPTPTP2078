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
% DateTime   : Thu Dec  3 09:43:25 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 127 expanded)
%              Number of leaves         :   21 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :   75 ( 201 expanded)
%              Number of equality atoms :   35 ( 108 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ~ ( ~ r1_xboole_0(A,A)
            & A = k1_xboole_0 )
        & ~ ( A != k1_xboole_0
            & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_24,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_48,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_52,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_30])).

tff(c_20,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_53,plain,(
    ! [A_17] : r1_xboole_0(A_17,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_20])).

tff(c_26,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_58,plain,(
    ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_58])).

tff(c_62,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_49,plain,(
    ! [A_14] : k4_xboole_0(A_14,'#skF_4') = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_50,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_14])).

tff(c_113,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_128,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_113])).

tff(c_143,plain,(
    ! [A_39] : k4_xboole_0(A_39,A_39) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_128])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_148,plain,(
    ! [A_39] : k4_xboole_0(A_39,'#skF_4') = k3_xboole_0(A_39,A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_18])).

tff(c_178,plain,(
    ! [A_42] : k3_xboole_0(A_42,A_42) = A_42 ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_148])).

tff(c_12,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_203,plain,(
    ! [A_43,C_44] :
      ( ~ r1_xboole_0(A_43,A_43)
      | ~ r2_hidden(C_44,A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_12])).

tff(c_215,plain,(
    ! [C_45] : ~ r2_hidden(C_45,'#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_203])).

tff(c_220,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_215])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_51,plain,(
    ! [A_5] :
      ( A_5 = '#skF_4'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6])).

tff(c_223,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_220,c_51])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_223])).

tff(c_228,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_250,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k4_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_265,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_250])).

tff(c_269,plain,(
    ! [A_54] : k4_xboole_0(A_54,A_54) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_265])).

tff(c_274,plain,(
    ! [A_54] : k4_xboole_0(A_54,k1_xboole_0) = k3_xboole_0(A_54,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_18])).

tff(c_286,plain,(
    ! [A_54] : k3_xboole_0(A_54,A_54) = A_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_274])).

tff(c_309,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,k3_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_350,plain,(
    ! [A_62,C_63] :
      ( ~ r1_xboole_0(A_62,A_62)
      | ~ r2_hidden(C_63,A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_309])).

tff(c_362,plain,(
    ! [C_64] : ~ r2_hidden(C_64,'#skF_3') ),
    inference(resolution,[status(thm)],[c_228,c_350])).

tff(c_367,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_362])).

tff(c_370,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_367,c_6])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_370])).

tff(c_375,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_377,plain,(
    ! [A_17] : r1_xboole_0(A_17,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_20])).

tff(c_376,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_382,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_376])).

tff(c_28,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_382,c_375,c_28])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.31  
% 2.18/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.32  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.18/1.32  
% 2.18/1.32  %Foreground sorts:
% 2.18/1.32  
% 2.18/1.32  
% 2.18/1.32  %Background operators:
% 2.18/1.32  
% 2.18/1.32  
% 2.18/1.32  %Foreground operators:
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.18/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.18/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.18/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.32  
% 2.18/1.33  tff(f_74, negated_conjecture, ~(![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.18/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.18/1.33  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.18/1.33  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.18/1.33  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.18/1.33  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.18/1.33  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.18/1.33  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.18/1.33  tff(c_24, plain, (k1_xboole_0!='#skF_3' | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.33  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_24])).
% 2.18/1.33  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.18/1.33  tff(c_22, plain, (r1_xboole_0('#skF_3', '#skF_3') | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.33  tff(c_48, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_22])).
% 2.18/1.33  tff(c_52, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_30])).
% 2.18/1.33  tff(c_20, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.18/1.33  tff(c_53, plain, (![A_17]: (r1_xboole_0(A_17, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_20])).
% 2.18/1.33  tff(c_26, plain, (r1_xboole_0('#skF_3', '#skF_3') | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.33  tff(c_58, plain, (~r1_xboole_0('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_26])).
% 2.18/1.33  tff(c_61, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_58])).
% 2.18/1.33  tff(c_62, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.18/1.33  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.33  tff(c_49, plain, (![A_14]: (k4_xboole_0(A_14, '#skF_4')=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_16])).
% 2.18/1.33  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.18/1.33  tff(c_50, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_14])).
% 2.18/1.33  tff(c_113, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.18/1.33  tff(c_128, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_113])).
% 2.18/1.33  tff(c_143, plain, (![A_39]: (k4_xboole_0(A_39, A_39)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_128])).
% 2.18/1.33  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.18/1.33  tff(c_148, plain, (![A_39]: (k4_xboole_0(A_39, '#skF_4')=k3_xboole_0(A_39, A_39))), inference(superposition, [status(thm), theory('equality')], [c_143, c_18])).
% 2.18/1.33  tff(c_178, plain, (![A_42]: (k3_xboole_0(A_42, A_42)=A_42)), inference(demodulation, [status(thm), theory('equality')], [c_49, c_148])).
% 2.18/1.33  tff(c_12, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.18/1.33  tff(c_203, plain, (![A_43, C_44]: (~r1_xboole_0(A_43, A_43) | ~r2_hidden(C_44, A_43))), inference(superposition, [status(thm), theory('equality')], [c_178, c_12])).
% 2.18/1.33  tff(c_215, plain, (![C_45]: (~r2_hidden(C_45, '#skF_3'))), inference(resolution, [status(thm)], [c_62, c_203])).
% 2.18/1.33  tff(c_220, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_215])).
% 2.18/1.33  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.18/1.33  tff(c_51, plain, (![A_5]: (A_5='#skF_4' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6])).
% 2.18/1.33  tff(c_223, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_220, c_51])).
% 2.18/1.33  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_223])).
% 2.18/1.33  tff(c_228, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 2.18/1.33  tff(c_250, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k4_xboole_0(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.18/1.33  tff(c_265, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_250])).
% 2.18/1.33  tff(c_269, plain, (![A_54]: (k4_xboole_0(A_54, A_54)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_265])).
% 2.18/1.33  tff(c_274, plain, (![A_54]: (k4_xboole_0(A_54, k1_xboole_0)=k3_xboole_0(A_54, A_54))), inference(superposition, [status(thm), theory('equality')], [c_269, c_18])).
% 2.18/1.33  tff(c_286, plain, (![A_54]: (k3_xboole_0(A_54, A_54)=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_274])).
% 2.18/1.33  tff(c_309, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, k3_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.18/1.33  tff(c_350, plain, (![A_62, C_63]: (~r1_xboole_0(A_62, A_62) | ~r2_hidden(C_63, A_62))), inference(superposition, [status(thm), theory('equality')], [c_286, c_309])).
% 2.18/1.33  tff(c_362, plain, (![C_64]: (~r2_hidden(C_64, '#skF_3'))), inference(resolution, [status(thm)], [c_228, c_350])).
% 2.18/1.33  tff(c_367, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_362])).
% 2.18/1.33  tff(c_370, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_367, c_6])).
% 2.18/1.33  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_370])).
% 2.18/1.33  tff(c_375, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_24])).
% 2.18/1.33  tff(c_377, plain, (![A_17]: (r1_xboole_0(A_17, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_375, c_20])).
% 2.18/1.33  tff(c_376, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.18/1.33  tff(c_382, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_375, c_376])).
% 2.18/1.33  tff(c_28, plain, (k1_xboole_0!='#skF_3' | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.33  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_377, c_382, c_375, c_28])).
% 2.18/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.33  
% 2.18/1.33  Inference rules
% 2.18/1.33  ----------------------
% 2.18/1.33  #Ref     : 0
% 2.18/1.33  #Sup     : 82
% 2.18/1.33  #Fact    : 0
% 2.18/1.33  #Define  : 0
% 2.18/1.33  #Split   : 3
% 2.18/1.33  #Chain   : 0
% 2.18/1.33  #Close   : 0
% 2.18/1.33  
% 2.18/1.33  Ordering : KBO
% 2.18/1.33  
% 2.18/1.33  Simplification rules
% 2.18/1.33  ----------------------
% 2.18/1.33  #Subsume      : 5
% 2.18/1.33  #Demod        : 30
% 2.18/1.33  #Tautology    : 52
% 2.18/1.33  #SimpNegUnit  : 3
% 2.18/1.33  #BackRed      : 6
% 2.18/1.33  
% 2.18/1.33  #Partial instantiations: 0
% 2.18/1.33  #Strategies tried      : 1
% 2.18/1.33  
% 2.18/1.33  Timing (in seconds)
% 2.18/1.33  ----------------------
% 2.18/1.33  Preprocessing        : 0.31
% 2.18/1.33  Parsing              : 0.17
% 2.18/1.33  CNF conversion       : 0.02
% 2.18/1.33  Main loop            : 0.20
% 2.18/1.33  Inferencing          : 0.08
% 2.18/1.33  Reduction            : 0.06
% 2.18/1.33  Demodulation         : 0.04
% 2.18/1.33  BG Simplification    : 0.01
% 2.18/1.33  Subsumption          : 0.02
% 2.18/1.33  Abstraction          : 0.01
% 2.18/1.33  MUC search           : 0.00
% 2.18/1.33  Cooper               : 0.00
% 2.18/1.33  Total                : 0.54
% 2.18/1.33  Index Insertion      : 0.00
% 2.18/1.33  Index Deletion       : 0.00
% 2.18/1.33  Index Matching       : 0.00
% 2.18/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
