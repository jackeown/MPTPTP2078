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
% DateTime   : Thu Dec  3 09:43:27 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   56 (  83 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   77 ( 145 expanded)
%              Number of equality atoms :   18 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_6 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_50,plain,(
    r1_tarski('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_162,plain,(
    ! [C_53,B_54,A_55] :
      ( r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_165,plain,(
    ! [A_1,B_2,B_54] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_54)
      | ~ r1_tarski(A_1,B_54)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_162])).

tff(c_243,plain,(
    ! [A_67,B_68,B_69] :
      ( r2_hidden('#skF_1'(A_67,B_68),B_69)
      | ~ r1_tarski(A_67,B_69)
      | r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_162])).

tff(c_42,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_48,plain,(
    r1_xboole_0('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_63,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_71,plain,(
    k3_xboole_0('#skF_8','#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_63])).

tff(c_111,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k3_xboole_0(A_43,B_44)) = k4_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_123,plain,(
    k4_xboole_0('#skF_8',k1_xboole_0) = k4_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_111])).

tff(c_126,plain,(
    k4_xboole_0('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_123])).

tff(c_134,plain,(
    ! [D_45,B_46,A_47] :
      ( ~ r2_hidden(D_45,B_46)
      | ~ r2_hidden(D_45,k4_xboole_0(A_47,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_137,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,'#skF_9')
      | ~ r2_hidden(D_45,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_134])).

tff(c_307,plain,(
    ! [A_72,B_73] :
      ( ~ r2_hidden('#skF_1'(A_72,B_73),'#skF_8')
      | ~ r1_tarski(A_72,'#skF_9')
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_243,c_137])).

tff(c_320,plain,(
    ! [A_74,B_75] :
      ( ~ r1_tarski(A_74,'#skF_9')
      | ~ r1_tarski(A_74,'#skF_8')
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_165,c_307])).

tff(c_331,plain,(
    ! [B_75] :
      ( ~ r1_tarski('#skF_7','#skF_8')
      | r1_tarski('#skF_7',B_75) ) ),
    inference(resolution,[status(thm)],[c_50,c_320])).

tff(c_339,plain,(
    ! [B_75] : r1_tarski('#skF_7',B_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_331])).

tff(c_456,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_4'(A_90,B_91),B_91)
      | r2_hidden('#skF_5'(A_90,B_91),A_90)
      | B_91 = A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_76,plain,(
    ! [A_30,B_31,C_32] :
      ( ~ r1_xboole_0(A_30,B_31)
      | ~ r2_hidden(C_32,k3_xboole_0(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_79,plain,(
    ! [C_32] :
      ( ~ r1_xboole_0('#skF_8','#skF_9')
      | ~ r2_hidden(C_32,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_76])).

tff(c_81,plain,(
    ! [C_32] : ~ r2_hidden(C_32,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_79])).

tff(c_544,plain,(
    ! [B_92] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_92),B_92)
      | k1_xboole_0 = B_92 ) ),
    inference(resolution,[status(thm)],[c_456,c_81])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_599,plain,(
    ! [B_96,B_97] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_96),B_97)
      | ~ r1_tarski(B_96,B_97)
      | k1_xboole_0 = B_96 ) ),
    inference(resolution,[status(thm)],[c_544,c_2])).

tff(c_651,plain,(
    ! [B_98] :
      ( ~ r1_tarski(B_98,k1_xboole_0)
      | k1_xboole_0 = B_98 ) ),
    inference(resolution,[status(thm)],[c_599,c_81])).

tff(c_655,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_339,c_651])).

tff(c_671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_655])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.36  
% 2.64/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_6 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.64/1.36  
% 2.64/1.36  %Foreground sorts:
% 2.64/1.36  
% 2.64/1.36  
% 2.64/1.36  %Background operators:
% 2.64/1.36  
% 2.64/1.36  
% 2.64/1.36  %Foreground operators:
% 2.64/1.36  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.64/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.64/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.64/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.64/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.64/1.36  tff('#skF_9', type, '#skF_9': $i).
% 2.64/1.36  tff('#skF_8', type, '#skF_8': $i).
% 2.64/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.64/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.64/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.64/1.36  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.64/1.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.64/1.36  
% 2.64/1.37  tff(f_80, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.64/1.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.64/1.37  tff(f_69, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.64/1.37  tff(f_46, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.64/1.37  tff(f_71, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.64/1.37  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.64/1.37  tff(f_53, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 2.64/1.37  tff(f_67, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.64/1.37  tff(c_46, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.64/1.37  tff(c_52, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.64/1.37  tff(c_50, plain, (r1_tarski('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.64/1.37  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.64/1.37  tff(c_162, plain, (![C_53, B_54, A_55]: (r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.64/1.37  tff(c_165, plain, (![A_1, B_2, B_54]: (r2_hidden('#skF_1'(A_1, B_2), B_54) | ~r1_tarski(A_1, B_54) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_162])).
% 2.64/1.37  tff(c_243, plain, (![A_67, B_68, B_69]: (r2_hidden('#skF_1'(A_67, B_68), B_69) | ~r1_tarski(A_67, B_69) | r1_tarski(A_67, B_68))), inference(resolution, [status(thm)], [c_6, c_162])).
% 2.64/1.37  tff(c_42, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.64/1.37  tff(c_48, plain, (r1_xboole_0('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.64/1.37  tff(c_63, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.64/1.37  tff(c_71, plain, (k3_xboole_0('#skF_8', '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_63])).
% 2.64/1.37  tff(c_111, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k3_xboole_0(A_43, B_44))=k4_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.64/1.37  tff(c_123, plain, (k4_xboole_0('#skF_8', k1_xboole_0)=k4_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_71, c_111])).
% 2.64/1.37  tff(c_126, plain, (k4_xboole_0('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_123])).
% 2.64/1.37  tff(c_134, plain, (![D_45, B_46, A_47]: (~r2_hidden(D_45, B_46) | ~r2_hidden(D_45, k4_xboole_0(A_47, B_46)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.64/1.37  tff(c_137, plain, (![D_45]: (~r2_hidden(D_45, '#skF_9') | ~r2_hidden(D_45, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_134])).
% 2.64/1.37  tff(c_307, plain, (![A_72, B_73]: (~r2_hidden('#skF_1'(A_72, B_73), '#skF_8') | ~r1_tarski(A_72, '#skF_9') | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_243, c_137])).
% 2.64/1.37  tff(c_320, plain, (![A_74, B_75]: (~r1_tarski(A_74, '#skF_9') | ~r1_tarski(A_74, '#skF_8') | r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_165, c_307])).
% 2.64/1.37  tff(c_331, plain, (![B_75]: (~r1_tarski('#skF_7', '#skF_8') | r1_tarski('#skF_7', B_75))), inference(resolution, [status(thm)], [c_50, c_320])).
% 2.64/1.37  tff(c_339, plain, (![B_75]: (r1_tarski('#skF_7', B_75))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_331])).
% 2.64/1.37  tff(c_456, plain, (![A_90, B_91]: (r2_hidden('#skF_4'(A_90, B_91), B_91) | r2_hidden('#skF_5'(A_90, B_91), A_90) | B_91=A_90)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.64/1.37  tff(c_76, plain, (![A_30, B_31, C_32]: (~r1_xboole_0(A_30, B_31) | ~r2_hidden(C_32, k3_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.64/1.37  tff(c_79, plain, (![C_32]: (~r1_xboole_0('#skF_8', '#skF_9') | ~r2_hidden(C_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_71, c_76])).
% 2.64/1.37  tff(c_81, plain, (![C_32]: (~r2_hidden(C_32, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_79])).
% 2.64/1.37  tff(c_544, plain, (![B_92]: (r2_hidden('#skF_4'(k1_xboole_0, B_92), B_92) | k1_xboole_0=B_92)), inference(resolution, [status(thm)], [c_456, c_81])).
% 2.64/1.37  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.64/1.37  tff(c_599, plain, (![B_96, B_97]: (r2_hidden('#skF_4'(k1_xboole_0, B_96), B_97) | ~r1_tarski(B_96, B_97) | k1_xboole_0=B_96)), inference(resolution, [status(thm)], [c_544, c_2])).
% 2.64/1.37  tff(c_651, plain, (![B_98]: (~r1_tarski(B_98, k1_xboole_0) | k1_xboole_0=B_98)), inference(resolution, [status(thm)], [c_599, c_81])).
% 2.64/1.37  tff(c_655, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_339, c_651])).
% 2.64/1.37  tff(c_671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_655])).
% 2.64/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.37  
% 2.64/1.37  Inference rules
% 2.64/1.37  ----------------------
% 2.64/1.37  #Ref     : 0
% 2.64/1.37  #Sup     : 129
% 2.64/1.37  #Fact    : 0
% 2.64/1.37  #Define  : 0
% 2.64/1.37  #Split   : 3
% 2.64/1.37  #Chain   : 0
% 2.64/1.37  #Close   : 0
% 2.64/1.37  
% 2.64/1.37  Ordering : KBO
% 2.64/1.37  
% 2.64/1.37  Simplification rules
% 2.64/1.37  ----------------------
% 2.64/1.37  #Subsume      : 15
% 2.64/1.37  #Demod        : 19
% 2.64/1.37  #Tautology    : 31
% 2.64/1.37  #SimpNegUnit  : 3
% 2.64/1.37  #BackRed      : 0
% 2.64/1.37  
% 2.64/1.37  #Partial instantiations: 0
% 2.64/1.37  #Strategies tried      : 1
% 2.64/1.37  
% 2.64/1.37  Timing (in seconds)
% 2.64/1.37  ----------------------
% 2.64/1.38  Preprocessing        : 0.29
% 2.64/1.38  Parsing              : 0.15
% 2.64/1.38  CNF conversion       : 0.02
% 2.64/1.38  Main loop            : 0.29
% 2.64/1.38  Inferencing          : 0.11
% 2.64/1.38  Reduction            : 0.08
% 2.64/1.38  Demodulation         : 0.05
% 2.64/1.38  BG Simplification    : 0.02
% 2.64/1.38  Subsumption          : 0.06
% 2.64/1.38  Abstraction          : 0.01
% 2.64/1.38  MUC search           : 0.00
% 2.64/1.38  Cooper               : 0.00
% 2.64/1.38  Total                : 0.61
% 2.64/1.38  Index Insertion      : 0.00
% 2.64/1.38  Index Deletion       : 0.00
% 2.64/1.38  Index Matching       : 0.00
% 2.64/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
