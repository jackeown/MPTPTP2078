%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:09 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   52 (  97 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 158 expanded)
%              Number of equality atoms :   21 (  36 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_6 > #skF_2 > #skF_4 > #skF_5 > #skF_7 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_44,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_32,plain,
    ( k5_relat_1('#skF_8',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_55,plain,(
    k5_relat_1(k1_xboole_0,'#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_36,plain,(
    ! [A_109] :
      ( v1_relat_1(A_109)
      | ~ v1_xboole_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_36])).

tff(c_253,plain,(
    ! [A_165,B_166,C_167] :
      ( r2_hidden(k4_tarski('#skF_3'(A_165,B_166,C_167),'#skF_5'(A_165,B_166,C_167)),A_165)
      | r2_hidden(k4_tarski('#skF_6'(A_165,B_166,C_167),'#skF_7'(A_165,B_166,C_167)),C_167)
      | k5_relat_1(A_165,B_166) = C_167
      | ~ v1_relat_1(C_167)
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    ! [A_111,B_112,C_113] :
      ( ~ r1_xboole_0(A_111,B_112)
      | ~ r2_hidden(C_113,k3_xboole_0(A_111,B_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_51,plain,(
    ! [A_6,C_113] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_113,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_48])).

tff(c_53,plain,(
    ! [C_113] : ~ r2_hidden(C_113,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_51])).

tff(c_331,plain,(
    ! [A_165,B_166] :
      ( r2_hidden(k4_tarski('#skF_3'(A_165,B_166,k1_xboole_0),'#skF_5'(A_165,B_166,k1_xboole_0)),A_165)
      | k5_relat_1(A_165,B_166) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_166)
      | ~ v1_relat_1(A_165) ) ),
    inference(resolution,[status(thm)],[c_253,c_53])).

tff(c_359,plain,(
    ! [A_168,B_169] :
      ( r2_hidden(k4_tarski('#skF_3'(A_168,B_169,k1_xboole_0),'#skF_5'(A_168,B_169,k1_xboole_0)),A_168)
      | k5_relat_1(A_168,B_169) = k1_xboole_0
      | ~ v1_relat_1(B_169)
      | ~ v1_relat_1(A_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_331])).

tff(c_397,plain,(
    ! [B_169] :
      ( k5_relat_1(k1_xboole_0,B_169) = k1_xboole_0
      | ~ v1_relat_1(B_169)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_359,c_53])).

tff(c_521,plain,(
    ! [B_173] :
      ( k5_relat_1(k1_xboole_0,B_173) = k1_xboole_0
      | ~ v1_relat_1(B_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_397])).

tff(c_527,plain,(
    k5_relat_1(k1_xboole_0,'#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_521])).

tff(c_532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_527])).

tff(c_533,plain,(
    k5_relat_1('#skF_8',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_876,plain,(
    ! [A_222,B_223,C_224] :
      ( r2_hidden(k4_tarski('#skF_5'(A_222,B_223,C_224),'#skF_4'(A_222,B_223,C_224)),B_223)
      | r2_hidden(k4_tarski('#skF_6'(A_222,B_223,C_224),'#skF_7'(A_222,B_223,C_224)),C_224)
      | k5_relat_1(A_222,B_223) = C_224
      | ~ v1_relat_1(C_224)
      | ~ v1_relat_1(B_223)
      | ~ v1_relat_1(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_938,plain,(
    ! [A_222,B_223] :
      ( r2_hidden(k4_tarski('#skF_5'(A_222,B_223,k1_xboole_0),'#skF_4'(A_222,B_223,k1_xboole_0)),B_223)
      | k5_relat_1(A_222,B_223) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_223)
      | ~ v1_relat_1(A_222) ) ),
    inference(resolution,[status(thm)],[c_876,c_53])).

tff(c_967,plain,(
    ! [A_228,B_229] :
      ( r2_hidden(k4_tarski('#skF_5'(A_228,B_229,k1_xboole_0),'#skF_4'(A_228,B_229,k1_xboole_0)),B_229)
      | k5_relat_1(A_228,B_229) = k1_xboole_0
      | ~ v1_relat_1(B_229)
      | ~ v1_relat_1(A_228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_938])).

tff(c_997,plain,(
    ! [A_228] :
      ( k5_relat_1(A_228,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_228) ) ),
    inference(resolution,[status(thm)],[c_967,c_53])).

tff(c_1013,plain,(
    ! [A_230] :
      ( k5_relat_1(A_230,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_997])).

tff(c_1019,plain,(
    k5_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_1013])).

tff(c_1025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_533,c_1019])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 14:51:27 EST 2020
% 0.17/0.32  % CPUTime    : 
% 0.17/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.50  
% 3.26/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.50  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_6 > #skF_2 > #skF_4 > #skF_5 > #skF_7 > #skF_8 > #skF_3 > #skF_1
% 3.26/1.50  
% 3.26/1.50  %Foreground sorts:
% 3.26/1.50  
% 3.26/1.50  
% 3.26/1.50  %Background operators:
% 3.26/1.50  
% 3.26/1.50  
% 3.26/1.50  %Foreground operators:
% 3.26/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.50  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.26/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.26/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.26/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.26/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.26/1.50  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.26/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.26/1.50  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.26/1.50  tff('#skF_8', type, '#skF_8': $i).
% 3.26/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.26/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.26/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.26/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.26/1.50  
% 3.26/1.52  tff(f_73, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.26/1.52  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.26/1.52  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.26/1.52  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 3.26/1.52  tff(f_44, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.26/1.52  tff(f_42, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.26/1.52  tff(f_40, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.26/1.52  tff(c_32, plain, (k5_relat_1('#skF_8', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.26/1.52  tff(c_55, plain, (k5_relat_1(k1_xboole_0, '#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 3.26/1.52  tff(c_34, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.26/1.52  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.26/1.52  tff(c_36, plain, (![A_109]: (v1_relat_1(A_109) | ~v1_xboole_0(A_109))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.26/1.52  tff(c_40, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_36])).
% 3.26/1.52  tff(c_253, plain, (![A_165, B_166, C_167]: (r2_hidden(k4_tarski('#skF_3'(A_165, B_166, C_167), '#skF_5'(A_165, B_166, C_167)), A_165) | r2_hidden(k4_tarski('#skF_6'(A_165, B_166, C_167), '#skF_7'(A_165, B_166, C_167)), C_167) | k5_relat_1(A_165, B_166)=C_167 | ~v1_relat_1(C_167) | ~v1_relat_1(B_166) | ~v1_relat_1(A_165))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.26/1.52  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.26/1.52  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.26/1.52  tff(c_48, plain, (![A_111, B_112, C_113]: (~r1_xboole_0(A_111, B_112) | ~r2_hidden(C_113, k3_xboole_0(A_111, B_112)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.26/1.52  tff(c_51, plain, (![A_6, C_113]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_113, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_48])).
% 3.26/1.52  tff(c_53, plain, (![C_113]: (~r2_hidden(C_113, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_51])).
% 3.26/1.52  tff(c_331, plain, (![A_165, B_166]: (r2_hidden(k4_tarski('#skF_3'(A_165, B_166, k1_xboole_0), '#skF_5'(A_165, B_166, k1_xboole_0)), A_165) | k5_relat_1(A_165, B_166)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_166) | ~v1_relat_1(A_165))), inference(resolution, [status(thm)], [c_253, c_53])).
% 3.26/1.52  tff(c_359, plain, (![A_168, B_169]: (r2_hidden(k4_tarski('#skF_3'(A_168, B_169, k1_xboole_0), '#skF_5'(A_168, B_169, k1_xboole_0)), A_168) | k5_relat_1(A_168, B_169)=k1_xboole_0 | ~v1_relat_1(B_169) | ~v1_relat_1(A_168))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_331])).
% 3.26/1.52  tff(c_397, plain, (![B_169]: (k5_relat_1(k1_xboole_0, B_169)=k1_xboole_0 | ~v1_relat_1(B_169) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_359, c_53])).
% 3.26/1.52  tff(c_521, plain, (![B_173]: (k5_relat_1(k1_xboole_0, B_173)=k1_xboole_0 | ~v1_relat_1(B_173))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_397])).
% 3.26/1.52  tff(c_527, plain, (k5_relat_1(k1_xboole_0, '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_521])).
% 3.26/1.52  tff(c_532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_527])).
% 3.26/1.52  tff(c_533, plain, (k5_relat_1('#skF_8', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.26/1.52  tff(c_876, plain, (![A_222, B_223, C_224]: (r2_hidden(k4_tarski('#skF_5'(A_222, B_223, C_224), '#skF_4'(A_222, B_223, C_224)), B_223) | r2_hidden(k4_tarski('#skF_6'(A_222, B_223, C_224), '#skF_7'(A_222, B_223, C_224)), C_224) | k5_relat_1(A_222, B_223)=C_224 | ~v1_relat_1(C_224) | ~v1_relat_1(B_223) | ~v1_relat_1(A_222))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.26/1.52  tff(c_938, plain, (![A_222, B_223]: (r2_hidden(k4_tarski('#skF_5'(A_222, B_223, k1_xboole_0), '#skF_4'(A_222, B_223, k1_xboole_0)), B_223) | k5_relat_1(A_222, B_223)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_223) | ~v1_relat_1(A_222))), inference(resolution, [status(thm)], [c_876, c_53])).
% 3.26/1.52  tff(c_967, plain, (![A_228, B_229]: (r2_hidden(k4_tarski('#skF_5'(A_228, B_229, k1_xboole_0), '#skF_4'(A_228, B_229, k1_xboole_0)), B_229) | k5_relat_1(A_228, B_229)=k1_xboole_0 | ~v1_relat_1(B_229) | ~v1_relat_1(A_228))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_938])).
% 3.26/1.52  tff(c_997, plain, (![A_228]: (k5_relat_1(A_228, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_228))), inference(resolution, [status(thm)], [c_967, c_53])).
% 3.26/1.52  tff(c_1013, plain, (![A_230]: (k5_relat_1(A_230, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_230))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_997])).
% 3.26/1.52  tff(c_1019, plain, (k5_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_1013])).
% 3.26/1.52  tff(c_1025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_533, c_1019])).
% 3.26/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.52  
% 3.26/1.52  Inference rules
% 3.26/1.52  ----------------------
% 3.26/1.52  #Ref     : 0
% 3.26/1.52  #Sup     : 193
% 3.26/1.52  #Fact    : 0
% 3.26/1.52  #Define  : 0
% 3.26/1.52  #Split   : 1
% 3.26/1.52  #Chain   : 0
% 3.26/1.52  #Close   : 0
% 3.26/1.52  
% 3.26/1.52  Ordering : KBO
% 3.26/1.52  
% 3.26/1.52  Simplification rules
% 3.26/1.52  ----------------------
% 3.26/1.52  #Subsume      : 29
% 3.26/1.52  #Demod        : 90
% 3.26/1.52  #Tautology    : 12
% 3.26/1.52  #SimpNegUnit  : 7
% 3.26/1.52  #BackRed      : 0
% 3.26/1.52  
% 3.26/1.52  #Partial instantiations: 0
% 3.26/1.52  #Strategies tried      : 1
% 3.26/1.52  
% 3.26/1.52  Timing (in seconds)
% 3.26/1.52  ----------------------
% 3.26/1.52  Preprocessing        : 0.32
% 3.26/1.52  Parsing              : 0.16
% 3.26/1.52  CNF conversion       : 0.03
% 3.26/1.52  Main loop            : 0.44
% 3.26/1.52  Inferencing          : 0.17
% 3.26/1.52  Reduction            : 0.10
% 3.26/1.52  Demodulation         : 0.08
% 3.26/1.52  BG Simplification    : 0.02
% 3.26/1.52  Subsumption          : 0.11
% 3.26/1.52  Abstraction          : 0.02
% 3.26/1.52  MUC search           : 0.00
% 3.26/1.52  Cooper               : 0.00
% 3.26/1.52  Total                : 0.80
% 3.26/1.52  Index Insertion      : 0.00
% 3.26/1.52  Index Deletion       : 0.00
% 3.26/1.52  Index Matching       : 0.00
% 3.26/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
