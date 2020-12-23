%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:52 EST 2020

% Result     : Theorem 8.53s
% Output     : CNFRefutation 8.53s
% Verified   : 
% Statistics : Number of formulae       :   44 (  67 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :   66 ( 145 expanded)
%              Number of equality atoms :   17 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_40,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_654,plain,(
    ! [A_105,B_106,C_107] :
      ( r2_hidden('#skF_2'(A_105,B_106,C_107),B_106)
      | r2_hidden('#skF_2'(A_105,B_106,C_107),A_105)
      | r2_hidden('#skF_3'(A_105,B_106,C_107),C_107)
      | k2_xboole_0(A_105,B_106) = C_107 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | r2_hidden('#skF_3'(A_8,B_9,C_10),C_10)
      | k2_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4315,plain,(
    ! [A_296,B_297] :
      ( r2_hidden('#skF_2'(A_296,B_297,A_296),B_297)
      | r2_hidden('#skF_3'(A_296,B_297,A_296),A_296)
      | k2_xboole_0(A_296,B_297) = A_296 ) ),
    inference(resolution,[status(thm)],[c_654,c_24])).

tff(c_867,plain,(
    ! [A_117,B_118,C_119] :
      ( r2_hidden('#skF_2'(A_117,B_118,C_119),B_118)
      | r2_hidden('#skF_2'(A_117,B_118,C_119),A_117)
      | ~ r2_hidden('#skF_3'(A_117,B_118,C_119),A_117)
      | k2_xboole_0(A_117,B_118) = C_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9,C_10),C_10)
      | ~ r2_hidden('#skF_3'(A_8,B_9,C_10),A_8)
      | k2_xboole_0(A_8,B_9) = C_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_914,plain,(
    ! [A_117,B_118] :
      ( r2_hidden('#skF_2'(A_117,B_118,A_117),B_118)
      | ~ r2_hidden('#skF_3'(A_117,B_118,A_117),A_117)
      | k2_xboole_0(A_117,B_118) = A_117 ) ),
    inference(resolution,[status(thm)],[c_867,c_20])).

tff(c_4397,plain,(
    ! [A_298,B_299] :
      ( r2_hidden('#skF_2'(A_298,B_299,A_298),B_299)
      | k2_xboole_0(A_298,B_299) = A_298 ) ),
    inference(resolution,[status(thm)],[c_4315,c_914])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4706,plain,(
    ! [A_311,B_312,B_313] :
      ( r2_hidden('#skF_2'(A_311,B_312,A_311),B_313)
      | ~ r1_tarski(B_312,B_313)
      | k2_xboole_0(A_311,B_312) = A_311 ) ),
    inference(resolution,[status(thm)],[c_4397,c_4])).

tff(c_4746,plain,(
    ! [B_313,B_312] :
      ( r2_hidden('#skF_3'(B_313,B_312,B_313),B_313)
      | ~ r1_tarski(B_312,B_313)
      | k2_xboole_0(B_313,B_312) = B_313 ) ),
    inference(resolution,[status(thm)],[c_4706,c_24])).

tff(c_5850,plain,(
    ! [B_358,B_359] :
      ( ~ r2_hidden('#skF_3'(B_358,B_359,B_358),B_358)
      | ~ r1_tarski(B_359,B_358)
      | k2_xboole_0(B_358,B_359) = B_358 ) ),
    inference(resolution,[status(thm)],[c_4706,c_20])).

tff(c_5941,plain,(
    ! [B_360,B_361] :
      ( ~ r1_tarski(B_360,B_361)
      | k2_xboole_0(B_361,B_360) = B_361 ) ),
    inference(resolution,[status(thm)],[c_4746,c_5850])).

tff(c_6012,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_5941])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_202,plain,(
    ! [C_54,A_55,B_56] :
      ( k2_xboole_0(k10_relat_1(C_54,A_55),k10_relat_1(C_54,B_56)) = k10_relat_1(C_54,k2_xboole_0(A_55,B_56))
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_509,plain,(
    ! [C_89,A_90,B_91] :
      ( r1_tarski(k10_relat_1(C_89,A_90),k10_relat_1(C_89,k2_xboole_0(A_90,B_91)))
      | ~ v1_relat_1(C_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_34])).

tff(c_520,plain,(
    ! [C_89,B_2,A_1] :
      ( r1_tarski(k10_relat_1(C_89,B_2),k10_relat_1(C_89,k2_xboole_0(A_1,B_2)))
      | ~ v1_relat_1(C_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_509])).

tff(c_8927,plain,(
    ! [C_384] :
      ( r1_tarski(k10_relat_1(C_384,'#skF_4'),k10_relat_1(C_384,'#skF_5'))
      | ~ v1_relat_1(C_384) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6012,c_520])).

tff(c_38,plain,(
    ~ r1_tarski(k10_relat_1('#skF_6','#skF_4'),k10_relat_1('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8937,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8927,c_38])).

tff(c_8945,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8937])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.53/2.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.53/2.83  
% 8.53/2.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.53/2.83  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 8.53/2.83  
% 8.53/2.83  %Foreground sorts:
% 8.53/2.83  
% 8.53/2.83  
% 8.53/2.83  %Background operators:
% 8.53/2.83  
% 8.53/2.83  
% 8.53/2.83  %Foreground operators:
% 8.53/2.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.53/2.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.53/2.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.53/2.83  tff('#skF_5', type, '#skF_5': $i).
% 8.53/2.83  tff('#skF_6', type, '#skF_6': $i).
% 8.53/2.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.53/2.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.53/2.83  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.53/2.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.53/2.83  tff('#skF_4', type, '#skF_4': $i).
% 8.53/2.83  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.53/2.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.53/2.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.53/2.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.53/2.83  
% 8.53/2.85  tff(f_62, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_relat_1)).
% 8.53/2.85  tff(f_43, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 8.53/2.85  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.53/2.85  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.53/2.85  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 8.53/2.85  tff(f_51, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.53/2.85  tff(c_42, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.53/2.85  tff(c_40, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.53/2.85  tff(c_654, plain, (![A_105, B_106, C_107]: (r2_hidden('#skF_2'(A_105, B_106, C_107), B_106) | r2_hidden('#skF_2'(A_105, B_106, C_107), A_105) | r2_hidden('#skF_3'(A_105, B_106, C_107), C_107) | k2_xboole_0(A_105, B_106)=C_107)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.53/2.85  tff(c_24, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | r2_hidden('#skF_3'(A_8, B_9, C_10), C_10) | k2_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.53/2.85  tff(c_4315, plain, (![A_296, B_297]: (r2_hidden('#skF_2'(A_296, B_297, A_296), B_297) | r2_hidden('#skF_3'(A_296, B_297, A_296), A_296) | k2_xboole_0(A_296, B_297)=A_296)), inference(resolution, [status(thm)], [c_654, c_24])).
% 8.53/2.85  tff(c_867, plain, (![A_117, B_118, C_119]: (r2_hidden('#skF_2'(A_117, B_118, C_119), B_118) | r2_hidden('#skF_2'(A_117, B_118, C_119), A_117) | ~r2_hidden('#skF_3'(A_117, B_118, C_119), A_117) | k2_xboole_0(A_117, B_118)=C_119)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.53/2.85  tff(c_20, plain, (![A_8, B_9, C_10]: (~r2_hidden('#skF_2'(A_8, B_9, C_10), C_10) | ~r2_hidden('#skF_3'(A_8, B_9, C_10), A_8) | k2_xboole_0(A_8, B_9)=C_10)), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.53/2.85  tff(c_914, plain, (![A_117, B_118]: (r2_hidden('#skF_2'(A_117, B_118, A_117), B_118) | ~r2_hidden('#skF_3'(A_117, B_118, A_117), A_117) | k2_xboole_0(A_117, B_118)=A_117)), inference(resolution, [status(thm)], [c_867, c_20])).
% 8.53/2.85  tff(c_4397, plain, (![A_298, B_299]: (r2_hidden('#skF_2'(A_298, B_299, A_298), B_299) | k2_xboole_0(A_298, B_299)=A_298)), inference(resolution, [status(thm)], [c_4315, c_914])).
% 8.53/2.85  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.53/2.85  tff(c_4706, plain, (![A_311, B_312, B_313]: (r2_hidden('#skF_2'(A_311, B_312, A_311), B_313) | ~r1_tarski(B_312, B_313) | k2_xboole_0(A_311, B_312)=A_311)), inference(resolution, [status(thm)], [c_4397, c_4])).
% 8.53/2.85  tff(c_4746, plain, (![B_313, B_312]: (r2_hidden('#skF_3'(B_313, B_312, B_313), B_313) | ~r1_tarski(B_312, B_313) | k2_xboole_0(B_313, B_312)=B_313)), inference(resolution, [status(thm)], [c_4706, c_24])).
% 8.53/2.85  tff(c_5850, plain, (![B_358, B_359]: (~r2_hidden('#skF_3'(B_358, B_359, B_358), B_358) | ~r1_tarski(B_359, B_358) | k2_xboole_0(B_358, B_359)=B_358)), inference(resolution, [status(thm)], [c_4706, c_20])).
% 8.53/2.85  tff(c_5941, plain, (![B_360, B_361]: (~r1_tarski(B_360, B_361) | k2_xboole_0(B_361, B_360)=B_361)), inference(resolution, [status(thm)], [c_4746, c_5850])).
% 8.53/2.85  tff(c_6012, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_40, c_5941])).
% 8.53/2.85  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.53/2.85  tff(c_202, plain, (![C_54, A_55, B_56]: (k2_xboole_0(k10_relat_1(C_54, A_55), k10_relat_1(C_54, B_56))=k10_relat_1(C_54, k2_xboole_0(A_55, B_56)) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.53/2.85  tff(c_34, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.53/2.85  tff(c_509, plain, (![C_89, A_90, B_91]: (r1_tarski(k10_relat_1(C_89, A_90), k10_relat_1(C_89, k2_xboole_0(A_90, B_91))) | ~v1_relat_1(C_89))), inference(superposition, [status(thm), theory('equality')], [c_202, c_34])).
% 8.53/2.85  tff(c_520, plain, (![C_89, B_2, A_1]: (r1_tarski(k10_relat_1(C_89, B_2), k10_relat_1(C_89, k2_xboole_0(A_1, B_2))) | ~v1_relat_1(C_89))), inference(superposition, [status(thm), theory('equality')], [c_2, c_509])).
% 8.53/2.85  tff(c_8927, plain, (![C_384]: (r1_tarski(k10_relat_1(C_384, '#skF_4'), k10_relat_1(C_384, '#skF_5')) | ~v1_relat_1(C_384))), inference(superposition, [status(thm), theory('equality')], [c_6012, c_520])).
% 8.53/2.85  tff(c_38, plain, (~r1_tarski(k10_relat_1('#skF_6', '#skF_4'), k10_relat_1('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.53/2.85  tff(c_8937, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_8927, c_38])).
% 8.53/2.85  tff(c_8945, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_8937])).
% 8.53/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.53/2.85  
% 8.53/2.85  Inference rules
% 8.53/2.85  ----------------------
% 8.53/2.85  #Ref     : 0
% 8.53/2.85  #Sup     : 2339
% 8.53/2.85  #Fact    : 6
% 8.53/2.85  #Define  : 0
% 8.53/2.85  #Split   : 1
% 8.53/2.85  #Chain   : 0
% 8.53/2.85  #Close   : 0
% 8.53/2.85  
% 8.53/2.85  Ordering : KBO
% 8.53/2.85  
% 8.53/2.85  Simplification rules
% 8.53/2.85  ----------------------
% 8.53/2.85  #Subsume      : 808
% 8.53/2.85  #Demod        : 414
% 8.53/2.85  #Tautology    : 239
% 8.53/2.85  #SimpNegUnit  : 0
% 8.53/2.85  #BackRed      : 0
% 8.53/2.85  
% 8.53/2.85  #Partial instantiations: 0
% 8.53/2.85  #Strategies tried      : 1
% 8.53/2.85  
% 8.53/2.85  Timing (in seconds)
% 8.53/2.85  ----------------------
% 8.53/2.85  Preprocessing        : 0.29
% 8.53/2.85  Parsing              : 0.15
% 8.53/2.85  CNF conversion       : 0.02
% 8.53/2.85  Main loop            : 1.77
% 8.53/2.85  Inferencing          : 0.47
% 8.53/2.85  Reduction            : 0.53
% 8.53/2.85  Demodulation         : 0.42
% 8.53/2.85  BG Simplification    : 0.06
% 8.53/2.85  Subsumption          : 0.60
% 8.53/2.85  Abstraction          : 0.08
% 8.53/2.85  MUC search           : 0.00
% 8.53/2.85  Cooper               : 0.00
% 8.53/2.85  Total                : 2.09
% 8.53/2.85  Index Insertion      : 0.00
% 8.53/2.85  Index Deletion       : 0.00
% 8.53/2.85  Index Matching       : 0.00
% 8.53/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
