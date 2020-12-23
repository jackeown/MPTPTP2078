%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:19 EST 2020

% Result     : Theorem 5.86s
% Output     : CNFRefutation 5.86s
% Verified   : 
% Statistics : Number of formulae       :   63 (  82 expanded)
%              Number of leaves         :   31 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 117 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k11_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_3 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_81,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1246,plain,(
    ! [A_164,B_165,C_166] :
      ( ~ r1_xboole_0(A_164,B_165)
      | ~ r2_hidden(C_166,k3_xboole_0(A_164,B_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1253,plain,(
    ! [A_6,C_166] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_166,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1246])).

tff(c_1256,plain,(
    ! [C_166] : ~ r2_hidden(C_166,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1253])).

tff(c_48,plain,
    ( k11_relat_1('#skF_12','#skF_11') = k1_xboole_0
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_71,plain,(
    ~ r2_hidden('#skF_11',k1_relat_1('#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,
    ( r2_hidden('#skF_11',k1_relat_1('#skF_12'))
    | k11_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_79,plain,(
    k11_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_54])).

tff(c_46,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_863,plain,(
    ! [A_148,B_149] :
      ( r2_hidden(k4_tarski('#skF_3'(A_148,B_149),'#skF_4'(A_148,B_149)),A_148)
      | r2_hidden('#skF_5'(A_148,B_149),B_149)
      | k1_relat_1(A_148) = B_149 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r1_xboole_0(A_58,B_59)
      | ~ r2_hidden(C_60,k3_xboole_0(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,(
    ! [A_6,C_60] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_60,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_72])).

tff(c_77,plain,(
    ! [C_60] : ~ r2_hidden(C_60,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_75])).

tff(c_935,plain,(
    ! [B_149] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_149),B_149)
      | k1_relat_1(k1_xboole_0) = B_149 ) ),
    inference(resolution,[status(thm)],[c_863,c_77])).

tff(c_961,plain,(
    ! [B_150] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_150),B_150)
      | k1_xboole_0 = B_150 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_935])).

tff(c_110,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden(k4_tarski(A_78,B_79),C_80)
      | ~ r2_hidden(B_79,k11_relat_1(C_80,A_78))
      | ~ v1_relat_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [C_30,A_15,D_33] :
      ( r2_hidden(C_30,k1_relat_1(A_15))
      | ~ r2_hidden(k4_tarski(C_30,D_33),A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_134,plain,(
    ! [A_78,C_80,B_79] :
      ( r2_hidden(A_78,k1_relat_1(C_80))
      | ~ r2_hidden(B_79,k11_relat_1(C_80,A_78))
      | ~ v1_relat_1(C_80) ) ),
    inference(resolution,[status(thm)],[c_110,c_16])).

tff(c_1144,plain,(
    ! [A_160,C_161] :
      ( r2_hidden(A_160,k1_relat_1(C_161))
      | ~ v1_relat_1(C_161)
      | k11_relat_1(C_161,A_160) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_961,c_134])).

tff(c_1204,plain,
    ( ~ v1_relat_1('#skF_12')
    | k11_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1144,c_71])).

tff(c_1234,plain,(
    k11_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1204])).

tff(c_1236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_1234])).

tff(c_1238,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_12')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1237,plain,(
    k11_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1426,plain,(
    ! [C_201,A_202] :
      ( r2_hidden(k4_tarski(C_201,'#skF_6'(A_202,k1_relat_1(A_202),C_201)),A_202)
      | ~ r2_hidden(C_201,k1_relat_1(A_202)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_40,plain,(
    ! [B_54,C_55,A_53] :
      ( r2_hidden(B_54,k11_relat_1(C_55,A_53))
      | ~ r2_hidden(k4_tarski(A_53,B_54),C_55)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6349,plain,(
    ! [A_392,C_393] :
      ( r2_hidden('#skF_6'(A_392,k1_relat_1(A_392),C_393),k11_relat_1(A_392,C_393))
      | ~ v1_relat_1(A_392)
      | ~ r2_hidden(C_393,k1_relat_1(A_392)) ) ),
    inference(resolution,[status(thm)],[c_1426,c_40])).

tff(c_6406,plain,
    ( r2_hidden('#skF_6'('#skF_12',k1_relat_1('#skF_12'),'#skF_11'),k1_xboole_0)
    | ~ v1_relat_1('#skF_12')
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1237,c_6349])).

tff(c_6414,plain,(
    r2_hidden('#skF_6'('#skF_12',k1_relat_1('#skF_12'),'#skF_11'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1238,c_46,c_6406])).

tff(c_6416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1256,c_6414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.86/2.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.86/2.14  
% 5.86/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.86/2.15  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k11_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_3 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4 > #skF_10
% 5.86/2.15  
% 5.86/2.15  %Foreground sorts:
% 5.86/2.15  
% 5.86/2.15  
% 5.86/2.15  %Background operators:
% 5.86/2.15  
% 5.86/2.15  
% 5.86/2.15  %Foreground operators:
% 5.86/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.86/2.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.86/2.15  tff('#skF_11', type, '#skF_11': $i).
% 5.86/2.15  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 5.86/2.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.86/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.86/2.15  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.86/2.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.86/2.15  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 5.86/2.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.86/2.15  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 5.86/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.86/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.86/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.86/2.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.86/2.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.86/2.15  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 5.86/2.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.86/2.15  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 5.86/2.15  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.86/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.86/2.15  tff('#skF_12', type, '#skF_12': $i).
% 5.86/2.15  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.86/2.15  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 5.86/2.15  
% 5.86/2.16  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.86/2.16  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 5.86/2.16  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.86/2.16  tff(f_89, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 5.86/2.16  tff(f_81, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.86/2.16  tff(f_64, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 5.86/2.16  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 5.86/2.16  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.86/2.16  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.86/2.16  tff(c_1246, plain, (![A_164, B_165, C_166]: (~r1_xboole_0(A_164, B_165) | ~r2_hidden(C_166, k3_xboole_0(A_164, B_165)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.86/2.16  tff(c_1253, plain, (![A_6, C_166]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_166, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1246])).
% 5.86/2.16  tff(c_1256, plain, (![C_166]: (~r2_hidden(C_166, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1253])).
% 5.86/2.16  tff(c_48, plain, (k11_relat_1('#skF_12', '#skF_11')=k1_xboole_0 | ~r2_hidden('#skF_11', k1_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.86/2.16  tff(c_71, plain, (~r2_hidden('#skF_11', k1_relat_1('#skF_12'))), inference(splitLeft, [status(thm)], [c_48])).
% 5.86/2.16  tff(c_54, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_12')) | k11_relat_1('#skF_12', '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.86/2.16  tff(c_79, plain, (k11_relat_1('#skF_12', '#skF_11')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_71, c_54])).
% 5.86/2.16  tff(c_46, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.86/2.16  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.86/2.16  tff(c_863, plain, (![A_148, B_149]: (r2_hidden(k4_tarski('#skF_3'(A_148, B_149), '#skF_4'(A_148, B_149)), A_148) | r2_hidden('#skF_5'(A_148, B_149), B_149) | k1_relat_1(A_148)=B_149)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.86/2.16  tff(c_72, plain, (![A_58, B_59, C_60]: (~r1_xboole_0(A_58, B_59) | ~r2_hidden(C_60, k3_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.86/2.16  tff(c_75, plain, (![A_6, C_60]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_72])).
% 5.86/2.16  tff(c_77, plain, (![C_60]: (~r2_hidden(C_60, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_75])).
% 5.86/2.16  tff(c_935, plain, (![B_149]: (r2_hidden('#skF_5'(k1_xboole_0, B_149), B_149) | k1_relat_1(k1_xboole_0)=B_149)), inference(resolution, [status(thm)], [c_863, c_77])).
% 5.86/2.16  tff(c_961, plain, (![B_150]: (r2_hidden('#skF_5'(k1_xboole_0, B_150), B_150) | k1_xboole_0=B_150)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_935])).
% 5.86/2.16  tff(c_110, plain, (![A_78, B_79, C_80]: (r2_hidden(k4_tarski(A_78, B_79), C_80) | ~r2_hidden(B_79, k11_relat_1(C_80, A_78)) | ~v1_relat_1(C_80))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.86/2.16  tff(c_16, plain, (![C_30, A_15, D_33]: (r2_hidden(C_30, k1_relat_1(A_15)) | ~r2_hidden(k4_tarski(C_30, D_33), A_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.86/2.16  tff(c_134, plain, (![A_78, C_80, B_79]: (r2_hidden(A_78, k1_relat_1(C_80)) | ~r2_hidden(B_79, k11_relat_1(C_80, A_78)) | ~v1_relat_1(C_80))), inference(resolution, [status(thm)], [c_110, c_16])).
% 5.86/2.16  tff(c_1144, plain, (![A_160, C_161]: (r2_hidden(A_160, k1_relat_1(C_161)) | ~v1_relat_1(C_161) | k11_relat_1(C_161, A_160)=k1_xboole_0)), inference(resolution, [status(thm)], [c_961, c_134])).
% 5.86/2.16  tff(c_1204, plain, (~v1_relat_1('#skF_12') | k11_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_1144, c_71])).
% 5.86/2.16  tff(c_1234, plain, (k11_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1204])).
% 5.86/2.16  tff(c_1236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_1234])).
% 5.86/2.16  tff(c_1238, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_12'))), inference(splitRight, [status(thm)], [c_48])).
% 5.86/2.16  tff(c_1237, plain, (k11_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 5.86/2.16  tff(c_1426, plain, (![C_201, A_202]: (r2_hidden(k4_tarski(C_201, '#skF_6'(A_202, k1_relat_1(A_202), C_201)), A_202) | ~r2_hidden(C_201, k1_relat_1(A_202)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.86/2.16  tff(c_40, plain, (![B_54, C_55, A_53]: (r2_hidden(B_54, k11_relat_1(C_55, A_53)) | ~r2_hidden(k4_tarski(A_53, B_54), C_55) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.86/2.16  tff(c_6349, plain, (![A_392, C_393]: (r2_hidden('#skF_6'(A_392, k1_relat_1(A_392), C_393), k11_relat_1(A_392, C_393)) | ~v1_relat_1(A_392) | ~r2_hidden(C_393, k1_relat_1(A_392)))), inference(resolution, [status(thm)], [c_1426, c_40])).
% 5.86/2.16  tff(c_6406, plain, (r2_hidden('#skF_6'('#skF_12', k1_relat_1('#skF_12'), '#skF_11'), k1_xboole_0) | ~v1_relat_1('#skF_12') | ~r2_hidden('#skF_11', k1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_1237, c_6349])).
% 5.86/2.16  tff(c_6414, plain, (r2_hidden('#skF_6'('#skF_12', k1_relat_1('#skF_12'), '#skF_11'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1238, c_46, c_6406])).
% 5.86/2.16  tff(c_6416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1256, c_6414])).
% 5.86/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.86/2.16  
% 5.86/2.16  Inference rules
% 5.86/2.16  ----------------------
% 5.86/2.16  #Ref     : 0
% 5.86/2.16  #Sup     : 1379
% 5.86/2.16  #Fact    : 0
% 5.86/2.16  #Define  : 0
% 5.86/2.16  #Split   : 3
% 5.86/2.16  #Chain   : 0
% 5.86/2.16  #Close   : 0
% 5.86/2.16  
% 5.86/2.16  Ordering : KBO
% 5.86/2.16  
% 5.86/2.16  Simplification rules
% 5.86/2.16  ----------------------
% 5.86/2.16  #Subsume      : 403
% 5.86/2.16  #Demod        : 589
% 5.86/2.16  #Tautology    : 199
% 5.86/2.16  #SimpNegUnit  : 149
% 5.86/2.16  #BackRed      : 0
% 5.86/2.16  
% 5.86/2.16  #Partial instantiations: 0
% 5.86/2.16  #Strategies tried      : 1
% 5.86/2.16  
% 5.86/2.16  Timing (in seconds)
% 5.86/2.16  ----------------------
% 5.86/2.16  Preprocessing        : 0.29
% 5.86/2.16  Parsing              : 0.15
% 5.86/2.16  CNF conversion       : 0.03
% 5.86/2.16  Main loop            : 1.10
% 5.86/2.16  Inferencing          : 0.36
% 5.86/2.16  Reduction            : 0.29
% 5.86/2.16  Demodulation         : 0.20
% 5.86/2.16  BG Simplification    : 0.04
% 5.86/2.16  Subsumption          : 0.32
% 5.86/2.16  Abstraction          : 0.05
% 5.86/2.16  MUC search           : 0.00
% 5.86/2.16  Cooper               : 0.00
% 5.86/2.16  Total                : 1.42
% 5.86/2.16  Index Insertion      : 0.00
% 5.86/2.16  Index Deletion       : 0.00
% 5.86/2.16  Index Matching       : 0.00
% 5.86/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
