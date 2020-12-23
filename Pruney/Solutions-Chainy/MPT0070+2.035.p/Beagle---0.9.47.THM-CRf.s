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
% DateTime   : Thu Dec  3 09:43:22 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   49 (  62 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  63 expanded)
%              Number of equality atoms :   29 (  38 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_63,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_65,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_71,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_83,plain,(
    ! [A_34,B_35] :
      ( r1_xboole_0(A_34,B_35)
      | k3_xboole_0(A_34,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_90,plain,(
    k3_xboole_0('#skF_3','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_83,c_30])).

tff(c_26,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_104,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_122,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_104])).

tff(c_126,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_122])).

tff(c_533,plain,(
    ! [A_64,B_65,C_66] : k2_xboole_0(k4_xboole_0(A_64,B_65),k3_xboole_0(A_64,C_66)) = k4_xboole_0(A_64,k4_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_569,plain,(
    ! [A_16,C_66] : k4_xboole_0(A_16,k4_xboole_0(A_16,C_66)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_16,C_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_533])).

tff(c_698,plain,(
    ! [A_71,C_72] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_71,C_72)) = k3_xboole_0(A_71,C_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_569])).

tff(c_34,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_70,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_78,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_70])).

tff(c_32,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_91,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = k1_xboole_0
      | ~ r1_xboole_0(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_103,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_91])).

tff(c_191,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k3_xboole_0(A_44,B_45)) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_212,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_191])).

tff(c_222,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_212])).

tff(c_651,plain,(
    ! [C_70] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_70)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3',C_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_533])).

tff(c_666,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3','#skF_5')) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_651])).

tff(c_685,plain,(
    k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_3','#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_666])).

tff(c_704,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_698,c_685])).

tff(c_742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_704])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.33  
% 2.45/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.33  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.45/1.33  
% 2.45/1.33  %Foreground sorts:
% 2.45/1.33  
% 2.45/1.33  
% 2.45/1.33  %Background operators:
% 2.45/1.33  
% 2.45/1.33  
% 2.45/1.33  %Foreground operators:
% 2.45/1.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.45/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.45/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.45/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.45/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.45/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.45/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.45/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.45/1.33  
% 2.45/1.34  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.45/1.34  tff(f_78, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.45/1.34  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.45/1.34  tff(f_63, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.45/1.34  tff(f_65, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.45/1.34  tff(f_71, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 2.45/1.34  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.45/1.34  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.45/1.34  tff(c_83, plain, (![A_34, B_35]: (r1_xboole_0(A_34, B_35) | k3_xboole_0(A_34, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.45/1.34  tff(c_30, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.34  tff(c_90, plain, (k3_xboole_0('#skF_3', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_83, c_30])).
% 2.45/1.34  tff(c_26, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.45/1.34  tff(c_20, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.45/1.34  tff(c_22, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.45/1.34  tff(c_104, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.45/1.34  tff(c_122, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_104])).
% 2.45/1.34  tff(c_126, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_122])).
% 2.45/1.34  tff(c_533, plain, (![A_64, B_65, C_66]: (k2_xboole_0(k4_xboole_0(A_64, B_65), k3_xboole_0(A_64, C_66))=k4_xboole_0(A_64, k4_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.45/1.34  tff(c_569, plain, (![A_16, C_66]: (k4_xboole_0(A_16, k4_xboole_0(A_16, C_66))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_16, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_533])).
% 2.45/1.34  tff(c_698, plain, (![A_71, C_72]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_71, C_72))=k3_xboole_0(A_71, C_72))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_569])).
% 2.45/1.34  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.34  tff(c_70, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.45/1.34  tff(c_78, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_70])).
% 2.45/1.34  tff(c_32, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.45/1.34  tff(c_91, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=k1_xboole_0 | ~r1_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.45/1.34  tff(c_103, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_91])).
% 2.45/1.34  tff(c_191, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k3_xboole_0(A_44, B_45))=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.45/1.34  tff(c_212, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_103, c_191])).
% 2.45/1.34  tff(c_222, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_212])).
% 2.45/1.34  tff(c_651, plain, (![C_70]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_70))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', C_70)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_533])).
% 2.45/1.34  tff(c_666, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', '#skF_5'))=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_222, c_651])).
% 2.45/1.34  tff(c_685, plain, (k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_3', '#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_78, c_666])).
% 2.45/1.34  tff(c_704, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_698, c_685])).
% 2.45/1.34  tff(c_742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_704])).
% 2.45/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.34  
% 2.45/1.34  Inference rules
% 2.45/1.34  ----------------------
% 2.45/1.34  #Ref     : 0
% 2.45/1.34  #Sup     : 179
% 2.45/1.34  #Fact    : 0
% 2.45/1.34  #Define  : 0
% 2.45/1.34  #Split   : 1
% 2.45/1.34  #Chain   : 0
% 2.45/1.34  #Close   : 0
% 2.45/1.34  
% 2.45/1.34  Ordering : KBO
% 2.45/1.34  
% 2.45/1.34  Simplification rules
% 2.45/1.34  ----------------------
% 2.45/1.34  #Subsume      : 11
% 2.45/1.34  #Demod        : 89
% 2.45/1.34  #Tautology    : 106
% 2.45/1.34  #SimpNegUnit  : 7
% 2.45/1.34  #BackRed      : 1
% 2.45/1.34  
% 2.45/1.34  #Partial instantiations: 0
% 2.45/1.34  #Strategies tried      : 1
% 2.45/1.34  
% 2.45/1.34  Timing (in seconds)
% 2.45/1.34  ----------------------
% 2.45/1.34  Preprocessing        : 0.28
% 2.45/1.34  Parsing              : 0.16
% 2.45/1.34  CNF conversion       : 0.02
% 2.45/1.34  Main loop            : 0.31
% 2.45/1.34  Inferencing          : 0.13
% 2.45/1.34  Reduction            : 0.10
% 2.45/1.34  Demodulation         : 0.07
% 2.45/1.34  BG Simplification    : 0.01
% 2.45/1.34  Subsumption          : 0.05
% 2.45/1.34  Abstraction          : 0.01
% 2.45/1.34  MUC search           : 0.00
% 2.45/1.34  Cooper               : 0.00
% 2.45/1.34  Total                : 0.62
% 2.45/1.34  Index Insertion      : 0.00
% 2.45/1.34  Index Deletion       : 0.00
% 2.45/1.35  Index Matching       : 0.00
% 2.45/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
