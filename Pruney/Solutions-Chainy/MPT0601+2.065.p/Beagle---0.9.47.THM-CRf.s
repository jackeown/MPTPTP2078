%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:22 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   53 (  71 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   66 ( 108 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_1 > #skF_5 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_8,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_152,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ r1_xboole_0(A_58,B_59)
      | ~ r2_hidden(C_60,k3_xboole_0(A_58,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_158,plain,(
    ! [A_61,B_62] :
      ( ~ r1_xboole_0(A_61,B_62)
      | k3_xboole_0(A_61,B_62) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_152])).

tff(c_164,plain,(
    ! [A_66] : k3_xboole_0(A_66,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_158])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_169,plain,(
    ! [A_66,C_5] :
      ( ~ r1_xboole_0(A_66,k1_xboole_0)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_4])).

tff(c_174,plain,(
    ! [C_5] : ~ r2_hidden(C_5,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_169])).

tff(c_28,plain,
    ( k11_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_37,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,
    ( r2_hidden('#skF_7',k1_relat_1('#skF_8'))
    | k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    k11_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_34])).

tff(c_26,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_81,plain,(
    ! [A_48,B_49,C_50] :
      ( r2_hidden(k4_tarski(A_48,B_49),C_50)
      | ~ r2_hidden(B_49,k11_relat_1(C_50,A_48))
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12,plain,(
    ! [C_24,A_9,D_27] :
      ( r2_hidden(C_24,k1_relat_1(A_9))
      | ~ r2_hidden(k4_tarski(C_24,D_27),A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_102,plain,(
    ! [A_53,C_54,B_55] :
      ( r2_hidden(A_53,k1_relat_1(C_54))
      | ~ r2_hidden(B_55,k11_relat_1(C_54,A_53))
      | ~ v1_relat_1(C_54) ) ),
    inference(resolution,[status(thm)],[c_81,c_12])).

tff(c_111,plain,(
    ! [A_56,C_57] :
      ( r2_hidden(A_56,k1_relat_1(C_57))
      | ~ v1_relat_1(C_57)
      | k11_relat_1(C_57,A_56) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_102])).

tff(c_126,plain,
    ( ~ v1_relat_1('#skF_8')
    | k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_37])).

tff(c_132,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_126])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_132])).

tff(c_136,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_135,plain,(
    k11_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_244,plain,(
    ! [C_83,A_84] :
      ( r2_hidden(k4_tarski(C_83,'#skF_6'(A_84,k1_relat_1(A_84),C_83)),A_84)
      | ~ r2_hidden(C_83,k1_relat_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [B_29,C_30,A_28] :
      ( r2_hidden(B_29,k11_relat_1(C_30,A_28))
      | ~ r2_hidden(k4_tarski(A_28,B_29),C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1957,plain,(
    ! [A_169,C_170] :
      ( r2_hidden('#skF_6'(A_169,k1_relat_1(A_169),C_170),k11_relat_1(A_169,C_170))
      | ~ v1_relat_1(A_169)
      | ~ r2_hidden(C_170,k1_relat_1(A_169)) ) ),
    inference(resolution,[status(thm)],[c_244,c_24])).

tff(c_2008,plain,
    ( r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0)
    | ~ v1_relat_1('#skF_8')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_1957])).

tff(c_2014,plain,(
    r2_hidden('#skF_6'('#skF_8',k1_relat_1('#skF_8'),'#skF_7'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_26,c_2008])).

tff(c_2016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_2014])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.75  
% 3.41/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.75  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k11_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 3.41/1.75  
% 3.41/1.75  %Foreground sorts:
% 3.41/1.75  
% 3.41/1.75  
% 3.41/1.75  %Background operators:
% 3.41/1.75  
% 3.41/1.75  
% 3.41/1.75  %Foreground operators:
% 3.41/1.75  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.41/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.41/1.75  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.41/1.75  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.41/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.75  tff('#skF_7', type, '#skF_7': $i).
% 3.41/1.75  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.41/1.75  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.41/1.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.41/1.75  tff('#skF_8', type, '#skF_8': $i).
% 3.41/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.41/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.41/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.41/1.75  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.41/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.41/1.75  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.41/1.75  
% 3.41/1.76  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.41/1.76  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.41/1.76  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.41/1.76  tff(f_71, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.41/1.76  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.41/1.76  tff(f_57, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.41/1.76  tff(c_8, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.41/1.76  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.41/1.76  tff(c_152, plain, (![A_58, B_59, C_60]: (~r1_xboole_0(A_58, B_59) | ~r2_hidden(C_60, k3_xboole_0(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.41/1.76  tff(c_158, plain, (![A_61, B_62]: (~r1_xboole_0(A_61, B_62) | k3_xboole_0(A_61, B_62)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_152])).
% 3.41/1.76  tff(c_164, plain, (![A_66]: (k3_xboole_0(A_66, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_158])).
% 3.41/1.76  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.41/1.76  tff(c_169, plain, (![A_66, C_5]: (~r1_xboole_0(A_66, k1_xboole_0) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_164, c_4])).
% 3.41/1.76  tff(c_174, plain, (![C_5]: (~r2_hidden(C_5, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_169])).
% 3.41/1.76  tff(c_28, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.41/1.76  tff(c_37, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_28])).
% 3.41/1.76  tff(c_34, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8')) | k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.41/1.76  tff(c_38, plain, (k11_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_37, c_34])).
% 3.41/1.76  tff(c_26, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.41/1.76  tff(c_81, plain, (![A_48, B_49, C_50]: (r2_hidden(k4_tarski(A_48, B_49), C_50) | ~r2_hidden(B_49, k11_relat_1(C_50, A_48)) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.41/1.76  tff(c_12, plain, (![C_24, A_9, D_27]: (r2_hidden(C_24, k1_relat_1(A_9)) | ~r2_hidden(k4_tarski(C_24, D_27), A_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.41/1.76  tff(c_102, plain, (![A_53, C_54, B_55]: (r2_hidden(A_53, k1_relat_1(C_54)) | ~r2_hidden(B_55, k11_relat_1(C_54, A_53)) | ~v1_relat_1(C_54))), inference(resolution, [status(thm)], [c_81, c_12])).
% 3.41/1.76  tff(c_111, plain, (![A_56, C_57]: (r2_hidden(A_56, k1_relat_1(C_57)) | ~v1_relat_1(C_57) | k11_relat_1(C_57, A_56)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_102])).
% 3.41/1.76  tff(c_126, plain, (~v1_relat_1('#skF_8') | k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_37])).
% 3.41/1.76  tff(c_132, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_126])).
% 3.41/1.76  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_132])).
% 3.41/1.76  tff(c_136, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_28])).
% 3.41/1.76  tff(c_135, plain, (k11_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 3.41/1.76  tff(c_244, plain, (![C_83, A_84]: (r2_hidden(k4_tarski(C_83, '#skF_6'(A_84, k1_relat_1(A_84), C_83)), A_84) | ~r2_hidden(C_83, k1_relat_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.41/1.76  tff(c_24, plain, (![B_29, C_30, A_28]: (r2_hidden(B_29, k11_relat_1(C_30, A_28)) | ~r2_hidden(k4_tarski(A_28, B_29), C_30) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.41/1.76  tff(c_1957, plain, (![A_169, C_170]: (r2_hidden('#skF_6'(A_169, k1_relat_1(A_169), C_170), k11_relat_1(A_169, C_170)) | ~v1_relat_1(A_169) | ~r2_hidden(C_170, k1_relat_1(A_169)))), inference(resolution, [status(thm)], [c_244, c_24])).
% 3.41/1.76  tff(c_2008, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0) | ~v1_relat_1('#skF_8') | ~r2_hidden('#skF_7', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_1957])).
% 3.41/1.76  tff(c_2014, plain, (r2_hidden('#skF_6'('#skF_8', k1_relat_1('#skF_8'), '#skF_7'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_136, c_26, c_2008])).
% 3.41/1.76  tff(c_2016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_2014])).
% 3.41/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.76  
% 3.41/1.76  Inference rules
% 3.41/1.76  ----------------------
% 3.41/1.76  #Ref     : 0
% 3.41/1.76  #Sup     : 447
% 3.41/1.76  #Fact    : 0
% 3.41/1.76  #Define  : 0
% 3.41/1.76  #Split   : 4
% 3.41/1.76  #Chain   : 0
% 3.41/1.76  #Close   : 0
% 3.41/1.76  
% 3.41/1.76  Ordering : KBO
% 3.41/1.76  
% 3.41/1.76  Simplification rules
% 3.41/1.76  ----------------------
% 3.41/1.76  #Subsume      : 149
% 3.41/1.76  #Demod        : 230
% 3.41/1.76  #Tautology    : 82
% 3.41/1.76  #SimpNegUnit  : 77
% 3.41/1.76  #BackRed      : 1
% 3.41/1.76  
% 3.41/1.76  #Partial instantiations: 0
% 3.41/1.76  #Strategies tried      : 1
% 3.41/1.76  
% 3.41/1.76  Timing (in seconds)
% 3.41/1.76  ----------------------
% 3.41/1.76  Preprocessing        : 0.41
% 3.41/1.76  Parsing              : 0.25
% 3.41/1.76  CNF conversion       : 0.02
% 3.41/1.76  Main loop            : 0.53
% 3.41/1.76  Inferencing          : 0.20
% 3.41/1.76  Reduction            : 0.14
% 3.41/1.76  Demodulation         : 0.09
% 3.41/1.76  BG Simplification    : 0.03
% 3.41/1.76  Subsumption          : 0.12
% 3.41/1.76  Abstraction          : 0.03
% 3.41/1.76  MUC search           : 0.00
% 3.41/1.76  Cooper               : 0.00
% 3.41/1.76  Total                : 0.97
% 3.41/1.76  Index Insertion      : 0.00
% 3.41/1.76  Index Deletion       : 0.00
% 3.41/1.76  Index Matching       : 0.00
% 3.41/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
