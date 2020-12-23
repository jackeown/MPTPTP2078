%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:20 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.35s
% Verified   : 
% Statistics : Number of formulae       :   51 (  66 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 110 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
                & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_54,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_9'))
    | ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_99,plain,(
    ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_58,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_64,plain,(
    ! [A_50,B_51] :
      ( k2_xboole_0(A_50,B_51) = B_51
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_75,plain,(
    k2_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_56,c_64])).

tff(c_1497,plain,(
    ! [A_164,B_165] :
      ( k2_xboole_0(k1_relat_1(A_164),k1_relat_1(B_165)) = k1_relat_1(k2_xboole_0(A_164,B_165))
      | ~ v1_relat_1(B_165)
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1565,plain,(
    ! [A_166,B_167] :
      ( r1_tarski(k1_relat_1(A_166),k1_relat_1(k2_xboole_0(A_166,B_167)))
      | ~ v1_relat_1(B_167)
      | ~ v1_relat_1(A_166) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1497,c_36])).

tff(c_1597,plain,
    ( r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_9'))
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_1565])).

tff(c_1610,plain,(
    r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_1597])).

tff(c_1612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_1610])).

tff(c_1613,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3198,plain,(
    ! [A_269,C_270] :
      ( r2_hidden(k4_tarski('#skF_7'(A_269,k2_relat_1(A_269),C_270),C_270),A_269)
      | ~ r2_hidden(C_270,k2_relat_1(A_269)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1733,plain,(
    ! [D_181,A_182,B_183] :
      ( ~ r2_hidden(D_181,A_182)
      | r2_hidden(D_181,k2_xboole_0(A_182,B_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1746,plain,(
    ! [D_181] :
      ( ~ r2_hidden(D_181,'#skF_8')
      | r2_hidden(D_181,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_1733])).

tff(c_1887,plain,(
    ! [C_193,A_194,D_195] :
      ( r2_hidden(C_193,k2_relat_1(A_194))
      | ~ r2_hidden(k4_tarski(D_195,C_193),A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1901,plain,(
    ! [C_193,D_195] :
      ( r2_hidden(C_193,k2_relat_1('#skF_9'))
      | ~ r2_hidden(k4_tarski(D_195,C_193),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1746,c_1887])).

tff(c_3223,plain,(
    ! [C_271] :
      ( r2_hidden(C_271,k2_relat_1('#skF_9'))
      | ~ r2_hidden(C_271,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_3198,c_1901])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5102,plain,(
    ! [A_363] :
      ( r1_tarski(A_363,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_1'(A_363,k2_relat_1('#skF_9')),k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_3223,c_4])).

tff(c_5114,plain,(
    r1_tarski(k2_relat_1('#skF_8'),k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_6,c_5102])).

tff(c_5120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1613,c_1613,c_5114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:12:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.35/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.04  
% 5.35/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.04  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 5.35/2.04  
% 5.35/2.04  %Foreground sorts:
% 5.35/2.04  
% 5.35/2.04  
% 5.35/2.04  %Background operators:
% 5.35/2.04  
% 5.35/2.04  
% 5.35/2.04  %Foreground operators:
% 5.35/2.04  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.35/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.35/2.04  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.35/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.35/2.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.35/2.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.35/2.04  tff('#skF_9', type, '#skF_9': $i).
% 5.35/2.04  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.35/2.04  tff('#skF_8', type, '#skF_8': $i).
% 5.35/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/2.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.35/2.04  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.35/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/2.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.35/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.35/2.04  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.35/2.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.35/2.04  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.35/2.04  
% 5.35/2.05  tff(f_90, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 5.35/2.05  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.35/2.05  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 5.35/2.05  tff(f_57, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 5.35/2.05  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.35/2.05  tff(f_71, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 5.35/2.05  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 5.35/2.05  tff(c_54, plain, (~r1_tarski(k2_relat_1('#skF_8'), k2_relat_1('#skF_9')) | ~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.35/2.05  tff(c_99, plain, (~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_54])).
% 5.35/2.05  tff(c_60, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.35/2.05  tff(c_58, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.35/2.05  tff(c_56, plain, (r1_tarski('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.35/2.05  tff(c_64, plain, (![A_50, B_51]: (k2_xboole_0(A_50, B_51)=B_51 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.35/2.05  tff(c_75, plain, (k2_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(resolution, [status(thm)], [c_56, c_64])).
% 5.35/2.05  tff(c_1497, plain, (![A_164, B_165]: (k2_xboole_0(k1_relat_1(A_164), k1_relat_1(B_165))=k1_relat_1(k2_xboole_0(A_164, B_165)) | ~v1_relat_1(B_165) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.35/2.05  tff(c_36, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.35/2.05  tff(c_1565, plain, (![A_166, B_167]: (r1_tarski(k1_relat_1(A_166), k1_relat_1(k2_xboole_0(A_166, B_167))) | ~v1_relat_1(B_167) | ~v1_relat_1(A_166))), inference(superposition, [status(thm), theory('equality')], [c_1497, c_36])).
% 5.35/2.05  tff(c_1597, plain, (r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_9')) | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_75, c_1565])).
% 5.35/2.05  tff(c_1610, plain, (r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_1597])).
% 5.35/2.05  tff(c_1612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_1610])).
% 5.35/2.05  tff(c_1613, plain, (~r1_tarski(k2_relat_1('#skF_8'), k2_relat_1('#skF_9'))), inference(splitRight, [status(thm)], [c_54])).
% 5.35/2.05  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.05  tff(c_3198, plain, (![A_269, C_270]: (r2_hidden(k4_tarski('#skF_7'(A_269, k2_relat_1(A_269), C_270), C_270), A_269) | ~r2_hidden(C_270, k2_relat_1(A_269)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.35/2.05  tff(c_1733, plain, (![D_181, A_182, B_183]: (~r2_hidden(D_181, A_182) | r2_hidden(D_181, k2_xboole_0(A_182, B_183)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.35/2.05  tff(c_1746, plain, (![D_181]: (~r2_hidden(D_181, '#skF_8') | r2_hidden(D_181, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_1733])).
% 5.35/2.05  tff(c_1887, plain, (![C_193, A_194, D_195]: (r2_hidden(C_193, k2_relat_1(A_194)) | ~r2_hidden(k4_tarski(D_195, C_193), A_194))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.35/2.05  tff(c_1901, plain, (![C_193, D_195]: (r2_hidden(C_193, k2_relat_1('#skF_9')) | ~r2_hidden(k4_tarski(D_195, C_193), '#skF_8'))), inference(resolution, [status(thm)], [c_1746, c_1887])).
% 5.35/2.05  tff(c_3223, plain, (![C_271]: (r2_hidden(C_271, k2_relat_1('#skF_9')) | ~r2_hidden(C_271, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_3198, c_1901])).
% 5.35/2.05  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.35/2.05  tff(c_5102, plain, (![A_363]: (r1_tarski(A_363, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_1'(A_363, k2_relat_1('#skF_9')), k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_3223, c_4])).
% 5.35/2.05  tff(c_5114, plain, (r1_tarski(k2_relat_1('#skF_8'), k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_6, c_5102])).
% 5.35/2.05  tff(c_5120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1613, c_1613, c_5114])).
% 5.35/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/2.05  
% 5.35/2.05  Inference rules
% 5.35/2.05  ----------------------
% 5.35/2.05  #Ref     : 0
% 5.35/2.05  #Sup     : 1237
% 5.35/2.05  #Fact    : 0
% 5.35/2.05  #Define  : 0
% 5.35/2.05  #Split   : 10
% 5.35/2.05  #Chain   : 0
% 5.35/2.05  #Close   : 0
% 5.35/2.05  
% 5.35/2.05  Ordering : KBO
% 5.35/2.05  
% 5.35/2.05  Simplification rules
% 5.35/2.05  ----------------------
% 5.35/2.05  #Subsume      : 264
% 5.35/2.05  #Demod        : 462
% 5.35/2.05  #Tautology    : 438
% 5.35/2.05  #SimpNegUnit  : 2
% 5.35/2.05  #BackRed      : 0
% 5.35/2.05  
% 5.35/2.05  #Partial instantiations: 0
% 5.35/2.05  #Strategies tried      : 1
% 5.35/2.05  
% 5.35/2.05  Timing (in seconds)
% 5.35/2.05  ----------------------
% 5.35/2.05  Preprocessing        : 0.31
% 5.35/2.05  Parsing              : 0.17
% 5.35/2.06  CNF conversion       : 0.03
% 5.35/2.06  Main loop            : 0.99
% 5.35/2.06  Inferencing          : 0.33
% 5.35/2.06  Reduction            : 0.32
% 5.35/2.06  Demodulation         : 0.23
% 5.35/2.06  BG Simplification    : 0.04
% 5.35/2.06  Subsumption          : 0.24
% 5.35/2.06  Abstraction          : 0.05
% 5.35/2.06  MUC search           : 0.00
% 5.35/2.06  Cooper               : 0.00
% 5.35/2.06  Total                : 1.34
% 5.35/2.06  Index Insertion      : 0.00
% 5.35/2.06  Index Deletion       : 0.00
% 5.35/2.06  Index Matching       : 0.00
% 5.35/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
