%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:23 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 142 expanded)
%              Number of leaves         :   22 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :   76 ( 183 expanded)
%              Number of equality atoms :   36 (  89 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(B,C) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_20,plain,(
    ~ r1_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_87,plain,(
    ! [A_30,B_31] : k4_xboole_0(A_30,k4_xboole_0(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_105,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_87])).

tff(c_109,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_105])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_43,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_51,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_43])).

tff(c_102,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_87])).

tff(c_108,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_102])).

tff(c_130,plain,(
    ! [A_35] : k4_xboole_0(A_35,A_35) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_105])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_135,plain,(
    ! [A_35] : k4_xboole_0(A_35,k1_xboole_0) = k3_xboole_0(A_35,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_16])).

tff(c_147,plain,(
    ! [A_35] : k3_xboole_0(A_35,A_35) = A_35 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_135])).

tff(c_205,plain,(
    ! [A_40,B_41,C_42] : k4_xboole_0(k3_xboole_0(A_40,B_41),C_42) = k3_xboole_0(A_40,k4_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_796,plain,(
    ! [A_56,C_57] : k3_xboole_0(A_56,k4_xboole_0(A_56,C_57)) = k4_xboole_0(A_56,C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_205])).

tff(c_22,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_56,plain,(
    ! [A_24,B_25,C_26] :
      ( ~ r1_xboole_0(A_24,B_25)
      | ~ r2_hidden(C_26,k3_xboole_0(A_24,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    ! [A_28,B_29] :
      ( ~ r1_xboole_0(A_28,B_29)
      | k3_xboole_0(A_28,B_29) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_77,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_506,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,k4_xboole_0(A_50,B_51)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_16])).

tff(c_563,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_506])).

tff(c_579,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_563])).

tff(c_806,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_579])).

tff(c_232,plain,(
    ! [C_42] : k3_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_42)) = k4_xboole_0('#skF_3',C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_205])).

tff(c_887,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_806,c_232])).

tff(c_894,plain,(
    k4_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_887])).

tff(c_1012,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_894,c_16])).

tff(c_1016,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_1012])).

tff(c_63,plain,(
    ! [A_10,C_26] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_26,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_56])).

tff(c_65,plain,(
    ! [C_26] : ~ r2_hidden(C_26,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_300,plain,(
    ! [A_45,B_46] : k3_xboole_0(A_45,k4_xboole_0(B_46,k3_xboole_0(A_45,B_46))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_205])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_315,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_1'(A_45,k4_xboole_0(B_46,k3_xboole_0(A_45,B_46))),k1_xboole_0)
      | r1_xboole_0(A_45,k4_xboole_0(B_46,k3_xboole_0(A_45,B_46))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_2])).

tff(c_350,plain,(
    ! [A_45,B_46] : r1_xboole_0(A_45,k4_xboole_0(B_46,k3_xboole_0(A_45,B_46))) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_315])).

tff(c_1024,plain,(
    r1_xboole_0('#skF_3',k4_xboole_0('#skF_5',k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_350])).

tff(c_1040,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1024])).

tff(c_1042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_1040])).

tff(c_1043,plain,(
    ! [A_10] : ~ r1_xboole_0(A_10,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_1169,plain,(
    ! [A_70,B_71] :
      ( ~ r1_xboole_0(A_70,B_71)
      | k3_xboole_0(A_70,B_71) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_1173,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_1169])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1180,plain,(
    ! [C_5] :
      ( ~ r1_xboole_0('#skF_4','#skF_5')
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1173,c_4])).

tff(c_1184,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1180])).

tff(c_1355,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_1'(A_78,B_79),k3_xboole_0(A_78,B_79))
      | r1_xboole_0(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1382,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_1'(A_10,k1_xboole_0),k1_xboole_0)
      | r1_xboole_0(A_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1355])).

tff(c_1390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1043,c_1184,c_1382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:19:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.43  
% 2.72/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.72/1.43  
% 2.72/1.43  %Foreground sorts:
% 2.72/1.43  
% 2.72/1.43  
% 2.72/1.43  %Background operators:
% 2.72/1.43  
% 2.72/1.43  
% 2.72/1.43  %Foreground operators:
% 2.72/1.43  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.72/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.72/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.72/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.72/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.72/1.43  
% 2.72/1.45  tff(f_66, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.72/1.45  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.72/1.45  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.72/1.45  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.72/1.45  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.72/1.45  tff(f_59, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.72/1.45  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.72/1.45  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.72/1.45  tff(c_20, plain, (~r1_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.72/1.45  tff(c_14, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.72/1.45  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.72/1.45  tff(c_87, plain, (![A_30, B_31]: (k4_xboole_0(A_30, k4_xboole_0(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.72/1.45  tff(c_105, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_87])).
% 2.72/1.45  tff(c_109, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_105])).
% 2.72/1.45  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.72/1.45  tff(c_43, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.72/1.45  tff(c_51, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_43])).
% 2.72/1.45  tff(c_102, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_51, c_87])).
% 2.72/1.45  tff(c_108, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_102])).
% 2.72/1.45  tff(c_130, plain, (![A_35]: (k4_xboole_0(A_35, A_35)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_105])).
% 2.72/1.45  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.72/1.45  tff(c_135, plain, (![A_35]: (k4_xboole_0(A_35, k1_xboole_0)=k3_xboole_0(A_35, A_35))), inference(superposition, [status(thm), theory('equality')], [c_130, c_16])).
% 2.72/1.45  tff(c_147, plain, (![A_35]: (k3_xboole_0(A_35, A_35)=A_35)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_135])).
% 2.72/1.45  tff(c_205, plain, (![A_40, B_41, C_42]: (k4_xboole_0(k3_xboole_0(A_40, B_41), C_42)=k3_xboole_0(A_40, k4_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.72/1.45  tff(c_796, plain, (![A_56, C_57]: (k3_xboole_0(A_56, k4_xboole_0(A_56, C_57))=k4_xboole_0(A_56, C_57))), inference(superposition, [status(thm), theory('equality')], [c_147, c_205])).
% 2.72/1.45  tff(c_22, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.72/1.45  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.72/1.45  tff(c_56, plain, (![A_24, B_25, C_26]: (~r1_xboole_0(A_24, B_25) | ~r2_hidden(C_26, k3_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.45  tff(c_73, plain, (![A_28, B_29]: (~r1_xboole_0(A_28, B_29) | k3_xboole_0(A_28, B_29)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_56])).
% 2.72/1.45  tff(c_77, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_73])).
% 2.72/1.45  tff(c_506, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k3_xboole_0(A_50, k4_xboole_0(A_50, B_51)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_16])).
% 2.72/1.45  tff(c_563, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_77, c_506])).
% 2.72/1.45  tff(c_579, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_563])).
% 2.72/1.45  tff(c_806, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_796, c_579])).
% 2.72/1.45  tff(c_232, plain, (![C_42]: (k3_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_42))=k4_xboole_0('#skF_3', C_42))), inference(superposition, [status(thm), theory('equality')], [c_108, c_205])).
% 2.72/1.45  tff(c_887, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_806, c_232])).
% 2.72/1.45  tff(c_894, plain, (k4_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_887])).
% 2.72/1.45  tff(c_1012, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_894, c_16])).
% 2.72/1.45  tff(c_1016, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_109, c_1012])).
% 2.72/1.45  tff(c_63, plain, (![A_10, C_26]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_26, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_56])).
% 2.72/1.45  tff(c_65, plain, (![C_26]: (~r2_hidden(C_26, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_63])).
% 2.72/1.45  tff(c_300, plain, (![A_45, B_46]: (k3_xboole_0(A_45, k4_xboole_0(B_46, k3_xboole_0(A_45, B_46)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_109, c_205])).
% 2.72/1.45  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), k3_xboole_0(A_1, B_2)) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.45  tff(c_315, plain, (![A_45, B_46]: (r2_hidden('#skF_1'(A_45, k4_xboole_0(B_46, k3_xboole_0(A_45, B_46))), k1_xboole_0) | r1_xboole_0(A_45, k4_xboole_0(B_46, k3_xboole_0(A_45, B_46))))), inference(superposition, [status(thm), theory('equality')], [c_300, c_2])).
% 2.72/1.45  tff(c_350, plain, (![A_45, B_46]: (r1_xboole_0(A_45, k4_xboole_0(B_46, k3_xboole_0(A_45, B_46))))), inference(negUnitSimplification, [status(thm)], [c_65, c_315])).
% 2.72/1.45  tff(c_1024, plain, (r1_xboole_0('#skF_3', k4_xboole_0('#skF_5', k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1016, c_350])).
% 2.72/1.45  tff(c_1040, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1024])).
% 2.72/1.45  tff(c_1042, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_1040])).
% 2.72/1.45  tff(c_1043, plain, (![A_10]: (~r1_xboole_0(A_10, k1_xboole_0))), inference(splitRight, [status(thm)], [c_63])).
% 2.72/1.45  tff(c_1169, plain, (![A_70, B_71]: (~r1_xboole_0(A_70, B_71) | k3_xboole_0(A_70, B_71)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_56])).
% 2.72/1.45  tff(c_1173, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_1169])).
% 2.72/1.45  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.45  tff(c_1180, plain, (![C_5]: (~r1_xboole_0('#skF_4', '#skF_5') | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1173, c_4])).
% 2.72/1.45  tff(c_1184, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1180])).
% 2.72/1.45  tff(c_1355, plain, (![A_78, B_79]: (r2_hidden('#skF_1'(A_78, B_79), k3_xboole_0(A_78, B_79)) | r1_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.45  tff(c_1382, plain, (![A_10]: (r2_hidden('#skF_1'(A_10, k1_xboole_0), k1_xboole_0) | r1_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1355])).
% 2.72/1.45  tff(c_1390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1043, c_1184, c_1382])).
% 2.72/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.45  
% 2.72/1.45  Inference rules
% 2.72/1.45  ----------------------
% 2.72/1.45  #Ref     : 0
% 2.72/1.45  #Sup     : 341
% 2.72/1.45  #Fact    : 0
% 2.72/1.45  #Define  : 0
% 2.72/1.45  #Split   : 3
% 2.72/1.45  #Chain   : 0
% 2.72/1.45  #Close   : 0
% 2.72/1.45  
% 2.72/1.45  Ordering : KBO
% 2.72/1.45  
% 2.72/1.45  Simplification rules
% 2.72/1.45  ----------------------
% 2.72/1.45  #Subsume      : 7
% 2.72/1.45  #Demod        : 255
% 2.72/1.45  #Tautology    : 198
% 2.72/1.45  #SimpNegUnit  : 12
% 2.72/1.45  #BackRed      : 3
% 2.72/1.45  
% 2.72/1.45  #Partial instantiations: 0
% 2.72/1.45  #Strategies tried      : 1
% 2.72/1.45  
% 2.72/1.45  Timing (in seconds)
% 2.72/1.45  ----------------------
% 2.72/1.45  Preprocessing        : 0.28
% 2.72/1.45  Parsing              : 0.16
% 2.72/1.45  CNF conversion       : 0.02
% 2.72/1.45  Main loop            : 0.39
% 2.72/1.45  Inferencing          : 0.15
% 2.72/1.45  Reduction            : 0.14
% 2.72/1.45  Demodulation         : 0.11
% 2.72/1.45  BG Simplification    : 0.02
% 2.72/1.45  Subsumption          : 0.05
% 2.72/1.45  Abstraction          : 0.02
% 2.72/1.45  MUC search           : 0.00
% 2.72/1.45  Cooper               : 0.00
% 2.72/1.45  Total                : 0.70
% 2.72/1.45  Index Insertion      : 0.00
% 2.72/1.45  Index Deletion       : 0.00
% 2.72/1.45  Index Matching       : 0.00
% 2.72/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
