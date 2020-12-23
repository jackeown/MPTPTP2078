%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:26 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   56 (  68 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :    6
%              Number of atoms          :   58 (  89 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
         => ( r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_11',k3_relat_1('#skF_12'))
    | ~ r2_hidden('#skF_10',k3_relat_1('#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_94,plain,(
    ~ r2_hidden('#skF_10',k3_relat_1('#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_42,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_107,plain,(
    ! [A_63] :
      ( k2_xboole_0(k1_relat_1(A_63),k2_relat_1(A_63)) = k3_relat_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_116,plain,(
    ! [A_63] :
      ( r1_tarski(k1_relat_1(A_63),k3_relat_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_10])).

tff(c_40,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_123,plain,(
    ! [C_65,A_66,D_67] :
      ( r2_hidden(C_65,k1_relat_1(A_66))
      | ~ r2_hidden(k4_tarski(C_65,D_67),A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_127,plain,(
    r2_hidden('#skF_10',k1_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_40,c_123])).

tff(c_129,plain,(
    ! [C_69,B_70,A_71] :
      ( r2_hidden(C_69,B_70)
      | ~ r2_hidden(C_69,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_154,plain,(
    ! [B_73] :
      ( r2_hidden('#skF_10',B_73)
      | ~ r1_tarski(k1_relat_1('#skF_12'),B_73) ) ),
    inference(resolution,[status(thm)],[c_127,c_129])).

tff(c_158,plain,
    ( r2_hidden('#skF_10',k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_116,c_154])).

tff(c_173,plain,(
    r2_hidden('#skF_10',k3_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_158])).

tff(c_175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_173])).

tff(c_176,plain,(
    ~ r2_hidden('#skF_11',k3_relat_1('#skF_12')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_244,plain,(
    ! [A_84] :
      ( k2_xboole_0(k1_relat_1(A_84),k2_relat_1(A_84)) = k3_relat_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    ! [B_51,A_52] : k2_xboole_0(B_51,A_52) = k2_xboole_0(A_52,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_59,plain,(
    ! [A_52,B_51] : r1_tarski(A_52,k2_xboole_0(B_51,A_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_250,plain,(
    ! [A_84] :
      ( r1_tarski(k2_relat_1(A_84),k3_relat_1(A_84))
      | ~ v1_relat_1(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_59])).

tff(c_351,plain,(
    ! [C_96,A_97,D_98] :
      ( r2_hidden(C_96,k2_relat_1(A_97))
      | ~ r2_hidden(k4_tarski(D_98,C_96),A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_359,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_12')) ),
    inference(resolution,[status(thm)],[c_40,c_351])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_379,plain,(
    ! [B_102] :
      ( r2_hidden('#skF_11',B_102)
      | ~ r1_tarski(k2_relat_1('#skF_12'),B_102) ) ),
    inference(resolution,[status(thm)],[c_359,c_4])).

tff(c_383,plain,
    ( r2_hidden('#skF_11',k3_relat_1('#skF_12'))
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_250,c_379])).

tff(c_398,plain,(
    r2_hidden('#skF_11',k3_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_383])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.29  
% 2.11/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.29  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4
% 2.11/1.29  
% 2.11/1.29  %Foreground sorts:
% 2.11/1.29  
% 2.11/1.29  
% 2.11/1.29  %Background operators:
% 2.11/1.29  
% 2.11/1.29  
% 2.11/1.29  %Foreground operators:
% 2.11/1.29  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.11/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.29  tff('#skF_11', type, '#skF_11': $i).
% 2.11/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.11/1.29  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.11/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.11/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.29  tff('#skF_10', type, '#skF_10': $i).
% 2.11/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.11/1.29  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.11/1.29  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.11/1.29  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.11/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.11/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.29  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.11/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.11/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.11/1.29  tff('#skF_12', type, '#skF_12': $i).
% 2.11/1.29  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.11/1.29  
% 2.11/1.30  tff(f_65, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 2.11/1.30  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.11/1.30  tff(f_36, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.11/1.30  tff(f_44, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.11/1.30  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.11/1.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.11/1.30  tff(f_52, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.11/1.30  tff(c_38, plain, (~r2_hidden('#skF_11', k3_relat_1('#skF_12')) | ~r2_hidden('#skF_10', k3_relat_1('#skF_12'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.11/1.30  tff(c_94, plain, (~r2_hidden('#skF_10', k3_relat_1('#skF_12'))), inference(splitLeft, [status(thm)], [c_38])).
% 2.11/1.30  tff(c_42, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.11/1.30  tff(c_107, plain, (![A_63]: (k2_xboole_0(k1_relat_1(A_63), k2_relat_1(A_63))=k3_relat_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.30  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.11/1.30  tff(c_116, plain, (![A_63]: (r1_tarski(k1_relat_1(A_63), k3_relat_1(A_63)) | ~v1_relat_1(A_63))), inference(superposition, [status(thm), theory('equality')], [c_107, c_10])).
% 2.11/1.30  tff(c_40, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.11/1.30  tff(c_123, plain, (![C_65, A_66, D_67]: (r2_hidden(C_65, k1_relat_1(A_66)) | ~r2_hidden(k4_tarski(C_65, D_67), A_66))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.11/1.30  tff(c_127, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_40, c_123])).
% 2.11/1.30  tff(c_129, plain, (![C_69, B_70, A_71]: (r2_hidden(C_69, B_70) | ~r2_hidden(C_69, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.11/1.30  tff(c_154, plain, (![B_73]: (r2_hidden('#skF_10', B_73) | ~r1_tarski(k1_relat_1('#skF_12'), B_73))), inference(resolution, [status(thm)], [c_127, c_129])).
% 2.11/1.30  tff(c_158, plain, (r2_hidden('#skF_10', k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_116, c_154])).
% 2.11/1.30  tff(c_173, plain, (r2_hidden('#skF_10', k3_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_158])).
% 2.11/1.30  tff(c_175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_173])).
% 2.11/1.30  tff(c_176, plain, (~r2_hidden('#skF_11', k3_relat_1('#skF_12'))), inference(splitRight, [status(thm)], [c_38])).
% 2.11/1.30  tff(c_244, plain, (![A_84]: (k2_xboole_0(k1_relat_1(A_84), k2_relat_1(A_84))=k3_relat_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.30  tff(c_44, plain, (![B_51, A_52]: (k2_xboole_0(B_51, A_52)=k2_xboole_0(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.30  tff(c_59, plain, (![A_52, B_51]: (r1_tarski(A_52, k2_xboole_0(B_51, A_52)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_10])).
% 2.11/1.30  tff(c_250, plain, (![A_84]: (r1_tarski(k2_relat_1(A_84), k3_relat_1(A_84)) | ~v1_relat_1(A_84))), inference(superposition, [status(thm), theory('equality')], [c_244, c_59])).
% 2.11/1.30  tff(c_351, plain, (![C_96, A_97, D_98]: (r2_hidden(C_96, k2_relat_1(A_97)) | ~r2_hidden(k4_tarski(D_98, C_96), A_97))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.11/1.30  tff(c_359, plain, (r2_hidden('#skF_11', k2_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_40, c_351])).
% 2.11/1.30  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.11/1.30  tff(c_379, plain, (![B_102]: (r2_hidden('#skF_11', B_102) | ~r1_tarski(k2_relat_1('#skF_12'), B_102))), inference(resolution, [status(thm)], [c_359, c_4])).
% 2.11/1.30  tff(c_383, plain, (r2_hidden('#skF_11', k3_relat_1('#skF_12')) | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_250, c_379])).
% 2.11/1.30  tff(c_398, plain, (r2_hidden('#skF_11', k3_relat_1('#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_383])).
% 2.11/1.30  tff(c_400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_398])).
% 2.11/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.30  
% 2.11/1.30  Inference rules
% 2.11/1.30  ----------------------
% 2.11/1.30  #Ref     : 0
% 2.11/1.30  #Sup     : 79
% 2.11/1.30  #Fact    : 0
% 2.11/1.30  #Define  : 0
% 2.11/1.30  #Split   : 1
% 2.11/1.30  #Chain   : 0
% 2.11/1.30  #Close   : 0
% 2.11/1.30  
% 2.11/1.30  Ordering : KBO
% 2.11/1.30  
% 2.11/1.30  Simplification rules
% 2.11/1.30  ----------------------
% 2.11/1.30  #Subsume      : 1
% 2.11/1.30  #Demod        : 19
% 2.11/1.30  #Tautology    : 28
% 2.11/1.30  #SimpNegUnit  : 2
% 2.11/1.30  #BackRed      : 0
% 2.11/1.30  
% 2.11/1.30  #Partial instantiations: 0
% 2.11/1.30  #Strategies tried      : 1
% 2.11/1.30  
% 2.11/1.30  Timing (in seconds)
% 2.11/1.30  ----------------------
% 2.11/1.30  Preprocessing        : 0.29
% 2.11/1.30  Parsing              : 0.15
% 2.11/1.30  CNF conversion       : 0.03
% 2.11/1.30  Main loop            : 0.25
% 2.11/1.30  Inferencing          : 0.09
% 2.11/1.30  Reduction            : 0.08
% 2.11/1.30  Demodulation         : 0.06
% 2.11/1.30  BG Simplification    : 0.01
% 2.11/1.30  Subsumption          : 0.05
% 2.11/1.30  Abstraction          : 0.01
% 2.11/1.30  MUC search           : 0.00
% 2.11/1.30  Cooper               : 0.00
% 2.11/1.30  Total                : 0.57
% 2.11/1.30  Index Insertion      : 0.00
% 2.11/1.30  Index Deletion       : 0.00
% 2.11/1.30  Index Matching       : 0.00
% 2.11/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
