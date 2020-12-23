%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:19 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 4.95s
% Verified   : 
% Statistics : Number of formulae       :   53 (  76 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 ( 118 expanded)
%              Number of equality atoms :   13 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1413,plain,(
    ! [C_112,A_113] :
      ( r2_hidden(k4_tarski(C_112,'#skF_6'(A_113,k1_relat_1(A_113),C_112)),A_113)
      | ~ r2_hidden(C_112,k1_relat_1(A_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1426,plain,(
    ! [A_114,C_115] :
      ( ~ v1_xboole_0(A_114)
      | ~ r2_hidden(C_115,k1_relat_1(A_114)) ) ),
    inference(resolution,[status(thm)],[c_1413,c_2])).

tff(c_1460,plain,(
    ! [A_117] :
      ( ~ v1_xboole_0(A_117)
      | k1_relat_1(A_117) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_1426])).

tff(c_1468,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1460])).

tff(c_1425,plain,(
    ! [A_113,C_112] :
      ( ~ v1_xboole_0(A_113)
      | ~ r2_hidden(C_112,k1_relat_1(A_113)) ) ),
    inference(resolution,[status(thm)],[c_1413,c_2])).

tff(c_1475,plain,(
    ! [C_112] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_112,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1468,c_1425])).

tff(c_1484,plain,(
    ! [C_112] : ~ r2_hidden(C_112,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1475])).

tff(c_34,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_52,plain,(
    k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_26,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_56,plain,(
    ! [A_40,B_41,C_42] :
      ( r2_hidden(k4_tarski(A_40,B_41),C_42)
      | ~ r2_hidden(B_41,k11_relat_1(C_42,A_40))
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [C_22,A_7,D_25] :
      ( r2_hidden(C_22,k1_relat_1(A_7))
      | ~ r2_hidden(k4_tarski(C_22,D_25),A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1173,plain,(
    ! [A_89,C_90,B_91] :
      ( r2_hidden(A_89,k1_relat_1(C_90))
      | ~ r2_hidden(B_91,k11_relat_1(C_90,A_89))
      | ~ v1_relat_1(C_90) ) ),
    inference(resolution,[status(thm)],[c_56,c_12])).

tff(c_1309,plain,(
    ! [A_101,C_102] :
      ( r2_hidden(A_101,k1_relat_1(C_102))
      | ~ v1_relat_1(C_102)
      | k11_relat_1(C_102,A_101) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_1173])).

tff(c_28,plain,
    ( k11_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_53,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_28])).

tff(c_1349,plain,
    ( ~ v1_relat_1('#skF_8')
    | k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1309,c_53])).

tff(c_1383,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1349])).

tff(c_1385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1383])).

tff(c_1386,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1387,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_24,plain,(
    ! [B_27,C_28,A_26] :
      ( r2_hidden(B_27,k11_relat_1(C_28,A_26))
      | ~ r2_hidden(k4_tarski(A_26,B_27),C_28)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3924,plain,(
    ! [A_191,C_192] :
      ( r2_hidden('#skF_6'(A_191,k1_relat_1(A_191),C_192),k11_relat_1(A_191,C_192))
      | ~ v1_relat_1(A_191)
      | ~ r2_hidden(C_192,k1_relat_1(A_191)) ) ),
    inference(resolution,[status(thm)],[c_1413,c_24])).

tff(c_3962,plain,
    ( r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0)
    | ~ v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1387,c_3924])).

tff(c_3968,plain,(
    r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1386,c_26,c_3962])).

tff(c_3970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1484,c_3968])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n022.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 13:37:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.87/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.89  
% 4.87/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/1.90  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_8 > #skF_5 > #skF_4
% 4.95/1.90  
% 4.95/1.90  %Foreground sorts:
% 4.95/1.90  
% 4.95/1.90  
% 4.95/1.90  %Background operators:
% 4.95/1.90  
% 4.95/1.90  
% 4.95/1.90  %Foreground operators:
% 4.95/1.90  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.95/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.95/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.95/1.90  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.95/1.90  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.95/1.90  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.95/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.95/1.90  tff('#skF_7', type, '#skF_7': $i).
% 4.95/1.90  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.95/1.90  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 4.95/1.90  tff('#skF_8', type, '#skF_8': $i).
% 4.95/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.95/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.95/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.95/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.95/1.90  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.95/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.95/1.90  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.95/1.90  
% 4.95/1.91  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.95/1.91  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.95/1.91  tff(f_48, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 4.95/1.91  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.95/1.91  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 4.95/1.91  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 4.95/1.91  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.95/1.91  tff(c_8, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.95/1.91  tff(c_1413, plain, (![C_112, A_113]: (r2_hidden(k4_tarski(C_112, '#skF_6'(A_113, k1_relat_1(A_113), C_112)), A_113) | ~r2_hidden(C_112, k1_relat_1(A_113)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.95/1.91  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.95/1.91  tff(c_1426, plain, (![A_114, C_115]: (~v1_xboole_0(A_114) | ~r2_hidden(C_115, k1_relat_1(A_114)))), inference(resolution, [status(thm)], [c_1413, c_2])).
% 4.95/1.91  tff(c_1460, plain, (![A_117]: (~v1_xboole_0(A_117) | k1_relat_1(A_117)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1426])).
% 4.95/1.91  tff(c_1468, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1460])).
% 4.95/1.91  tff(c_1425, plain, (![A_113, C_112]: (~v1_xboole_0(A_113) | ~r2_hidden(C_112, k1_relat_1(A_113)))), inference(resolution, [status(thm)], [c_1413, c_2])).
% 4.95/1.91  tff(c_1475, plain, (![C_112]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_112, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1468, c_1425])).
% 4.95/1.91  tff(c_1484, plain, (![C_112]: (~r2_hidden(C_112, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1475])).
% 4.95/1.91  tff(c_34, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8')) | k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.95/1.91  tff(c_52, plain, (k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 4.95/1.91  tff(c_26, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.95/1.91  tff(c_56, plain, (![A_40, B_41, C_42]: (r2_hidden(k4_tarski(A_40, B_41), C_42) | ~r2_hidden(B_41, k11_relat_1(C_42, A_40)) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.95/1.91  tff(c_12, plain, (![C_22, A_7, D_25]: (r2_hidden(C_22, k1_relat_1(A_7)) | ~r2_hidden(k4_tarski(C_22, D_25), A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.95/1.91  tff(c_1173, plain, (![A_89, C_90, B_91]: (r2_hidden(A_89, k1_relat_1(C_90)) | ~r2_hidden(B_91, k11_relat_1(C_90, A_89)) | ~v1_relat_1(C_90))), inference(resolution, [status(thm)], [c_56, c_12])).
% 4.95/1.91  tff(c_1309, plain, (![A_101, C_102]: (r2_hidden(A_101, k1_relat_1(C_102)) | ~v1_relat_1(C_102) | k11_relat_1(C_102, A_101)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1173])).
% 4.95/1.91  tff(c_28, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.95/1.91  tff(c_53, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_52, c_28])).
% 4.95/1.91  tff(c_1349, plain, (~v1_relat_1('#skF_8') | k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_1309, c_53])).
% 4.95/1.91  tff(c_1383, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1349])).
% 4.95/1.91  tff(c_1385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1383])).
% 4.95/1.91  tff(c_1386, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_34])).
% 4.95/1.91  tff(c_1387, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 4.95/1.91  tff(c_24, plain, (![B_27, C_28, A_26]: (r2_hidden(B_27, k11_relat_1(C_28, A_26)) | ~r2_hidden(k4_tarski(A_26, B_27), C_28) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.95/1.91  tff(c_3924, plain, (![A_191, C_192]: (r2_hidden('#skF_6'(A_191, k1_relat_1(A_191), C_192), k11_relat_1(A_191, C_192)) | ~v1_relat_1(A_191) | ~r2_hidden(C_192, k1_relat_1(A_191)))), inference(resolution, [status(thm)], [c_1413, c_24])).
% 4.95/1.91  tff(c_3962, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0) | ~v1_relat_1('#skF_8') | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1387, c_3924])).
% 4.95/1.91  tff(c_3968, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1386, c_26, c_3962])).
% 4.95/1.91  tff(c_3970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1484, c_3968])).
% 4.95/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/1.91  
% 4.95/1.91  Inference rules
% 4.95/1.91  ----------------------
% 4.95/1.91  #Ref     : 0
% 4.95/1.91  #Sup     : 990
% 4.95/1.91  #Fact    : 0
% 4.95/1.91  #Define  : 0
% 4.95/1.91  #Split   : 3
% 4.95/1.91  #Chain   : 0
% 4.95/1.91  #Close   : 0
% 4.95/1.91  
% 4.95/1.91  Ordering : KBO
% 4.95/1.91  
% 4.95/1.91  Simplification rules
% 4.95/1.91  ----------------------
% 4.95/1.91  #Subsume      : 344
% 4.95/1.91  #Demod        : 813
% 4.95/1.91  #Tautology    : 324
% 4.95/1.91  #SimpNegUnit  : 24
% 4.95/1.91  #BackRed      : 0
% 4.95/1.91  
% 4.95/1.91  #Partial instantiations: 0
% 4.95/1.91  #Strategies tried      : 1
% 4.95/1.91  
% 4.95/1.91  Timing (in seconds)
% 4.95/1.91  ----------------------
% 4.95/1.91  Preprocessing        : 0.29
% 4.95/1.91  Parsing              : 0.15
% 4.95/1.91  CNF conversion       : 0.02
% 4.95/1.91  Main loop            : 0.86
% 4.95/1.91  Inferencing          : 0.28
% 4.95/1.91  Reduction            : 0.24
% 4.95/1.91  Demodulation         : 0.17
% 4.95/1.91  BG Simplification    : 0.04
% 4.95/1.91  Subsumption          : 0.24
% 5.02/1.91  Abstraction          : 0.04
% 5.02/1.91  MUC search           : 0.00
% 5.02/1.91  Cooper               : 0.00
% 5.02/1.91  Total                : 1.18
% 5.02/1.91  Index Insertion      : 0.00
% 5.02/1.91  Index Deletion       : 0.00
% 5.02/1.91  Index Matching       : 0.00
% 5.02/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
