%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:19 EST 2020

% Result     : Theorem 4.61s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :   54 (  69 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 101 expanded)
%              Number of equality atoms :   10 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_45,plain,(
    ! [A_36,B_37] :
      ( ~ r2_hidden(A_36,B_37)
      | ~ r1_xboole_0(k1_tarski(A_36),B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,(
    ! [A_36] : ~ r2_hidden(A_36,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_45])).

tff(c_36,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_62,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_28,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_45,B_46,C_47] :
      ( r2_hidden(k4_tarski(A_45,B_46),C_47)
      | ~ r2_hidden(B_46,k11_relat_1(C_47,A_45))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [C_24,A_9,D_27] :
      ( r2_hidden(C_24,k1_relat_1(A_9))
      | ~ r2_hidden(k4_tarski(C_24,D_27),A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1273,plain,(
    ! [A_103,C_104,B_105] :
      ( r2_hidden(A_103,k1_relat_1(C_104))
      | ~ r2_hidden(B_105,k11_relat_1(C_104,A_103))
      | ~ v1_relat_1(C_104) ) ),
    inference(resolution,[status(thm)],[c_66,c_14])).

tff(c_1298,plain,(
    ! [A_106,C_107] :
      ( r2_hidden(A_106,k1_relat_1(C_107))
      | ~ v1_relat_1(C_107)
      | v1_xboole_0(k11_relat_1(C_107,A_106)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1273])).

tff(c_30,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_63,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_1338,plain,
    ( ~ v1_relat_1('#skF_7')
    | v1_xboole_0(k11_relat_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1298,c_63])).

tff(c_1372,plain,(
    v1_xboole_0(k11_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1338])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1395,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1372,c_6])).

tff(c_1405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1395])).

tff(c_1406,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1406])).

tff(c_1409,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1410,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1516,plain,(
    ! [C_131,A_132] :
      ( r2_hidden(k4_tarski(C_131,'#skF_5'(A_132,k1_relat_1(A_132),C_131)),A_132)
      | ~ r2_hidden(C_131,k1_relat_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    ! [B_29,C_30,A_28] :
      ( r2_hidden(B_29,k11_relat_1(C_30,A_28))
      | ~ r2_hidden(k4_tarski(A_28,B_29),C_30)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3034,plain,(
    ! [A_187,C_188] :
      ( r2_hidden('#skF_5'(A_187,k1_relat_1(A_187),C_188),k11_relat_1(A_187,C_188))
      | ~ v1_relat_1(A_187)
      | ~ r2_hidden(C_188,k1_relat_1(A_187)) ) ),
    inference(resolution,[status(thm)],[c_1516,c_26])).

tff(c_3063,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1410,c_3034])).

tff(c_3069,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1409,c_28,c_3063])).

tff(c_3071,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_3069])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:00:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.61/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.89  
% 4.61/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.89  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 4.61/1.89  
% 4.61/1.89  %Foreground sorts:
% 4.61/1.89  
% 4.61/1.89  
% 4.61/1.89  %Background operators:
% 4.61/1.89  
% 4.61/1.89  
% 4.61/1.89  %Foreground operators:
% 4.61/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.61/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.61/1.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.61/1.89  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.61/1.89  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.61/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.61/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.61/1.89  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.61/1.89  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 4.61/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.61/1.89  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.61/1.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.61/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.61/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.61/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.61/1.89  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.61/1.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.61/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.61/1.89  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.61/1.89  
% 4.61/1.91  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.61/1.91  tff(f_42, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 4.61/1.91  tff(f_64, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 4.61/1.91  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.61/1.91  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 4.61/1.91  tff(f_50, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 4.61/1.91  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.61/1.91  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.61/1.91  tff(c_45, plain, (![A_36, B_37]: (~r2_hidden(A_36, B_37) | ~r1_xboole_0(k1_tarski(A_36), B_37))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.61/1.91  tff(c_50, plain, (![A_36]: (~r2_hidden(A_36, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_45])).
% 4.61/1.91  tff(c_36, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.61/1.91  tff(c_62, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 4.61/1.91  tff(c_28, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.61/1.91  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.61/1.91  tff(c_66, plain, (![A_45, B_46, C_47]: (r2_hidden(k4_tarski(A_45, B_46), C_47) | ~r2_hidden(B_46, k11_relat_1(C_47, A_45)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.61/1.91  tff(c_14, plain, (![C_24, A_9, D_27]: (r2_hidden(C_24, k1_relat_1(A_9)) | ~r2_hidden(k4_tarski(C_24, D_27), A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.61/1.91  tff(c_1273, plain, (![A_103, C_104, B_105]: (r2_hidden(A_103, k1_relat_1(C_104)) | ~r2_hidden(B_105, k11_relat_1(C_104, A_103)) | ~v1_relat_1(C_104))), inference(resolution, [status(thm)], [c_66, c_14])).
% 4.61/1.91  tff(c_1298, plain, (![A_106, C_107]: (r2_hidden(A_106, k1_relat_1(C_107)) | ~v1_relat_1(C_107) | v1_xboole_0(k11_relat_1(C_107, A_106)))), inference(resolution, [status(thm)], [c_4, c_1273])).
% 4.61/1.91  tff(c_30, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.61/1.91  tff(c_63, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_30])).
% 4.61/1.91  tff(c_1338, plain, (~v1_relat_1('#skF_7') | v1_xboole_0(k11_relat_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_1298, c_63])).
% 4.61/1.91  tff(c_1372, plain, (v1_xboole_0(k11_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1338])).
% 4.61/1.91  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.61/1.91  tff(c_1395, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_1372, c_6])).
% 4.61/1.91  tff(c_1405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1395])).
% 4.61/1.91  tff(c_1406, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_30])).
% 4.61/1.91  tff(c_1408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1406])).
% 4.61/1.91  tff(c_1409, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_36])).
% 4.61/1.91  tff(c_1410, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 4.61/1.91  tff(c_1516, plain, (![C_131, A_132]: (r2_hidden(k4_tarski(C_131, '#skF_5'(A_132, k1_relat_1(A_132), C_131)), A_132) | ~r2_hidden(C_131, k1_relat_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.61/1.91  tff(c_26, plain, (![B_29, C_30, A_28]: (r2_hidden(B_29, k11_relat_1(C_30, A_28)) | ~r2_hidden(k4_tarski(A_28, B_29), C_30) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.61/1.91  tff(c_3034, plain, (![A_187, C_188]: (r2_hidden('#skF_5'(A_187, k1_relat_1(A_187), C_188), k11_relat_1(A_187, C_188)) | ~v1_relat_1(A_187) | ~r2_hidden(C_188, k1_relat_1(A_187)))), inference(resolution, [status(thm)], [c_1516, c_26])).
% 4.61/1.91  tff(c_3063, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0) | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1410, c_3034])).
% 4.61/1.91  tff(c_3069, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1409, c_28, c_3063])).
% 4.61/1.91  tff(c_3071, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_3069])).
% 4.61/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.61/1.91  
% 4.61/1.91  Inference rules
% 4.61/1.91  ----------------------
% 4.61/1.91  #Ref     : 0
% 4.61/1.91  #Sup     : 730
% 4.61/1.91  #Fact    : 0
% 4.61/1.91  #Define  : 0
% 4.61/1.91  #Split   : 4
% 4.61/1.91  #Chain   : 0
% 4.61/1.91  #Close   : 0
% 4.61/1.91  
% 4.61/1.91  Ordering : KBO
% 4.61/1.91  
% 4.61/1.91  Simplification rules
% 4.61/1.91  ----------------------
% 4.61/1.91  #Subsume      : 171
% 4.61/1.91  #Demod        : 633
% 4.61/1.91  #Tautology    : 282
% 4.61/1.91  #SimpNegUnit  : 23
% 4.61/1.91  #BackRed      : 4
% 4.61/1.91  
% 4.61/1.91  #Partial instantiations: 0
% 4.61/1.91  #Strategies tried      : 1
% 4.61/1.91  
% 4.61/1.91  Timing (in seconds)
% 4.61/1.91  ----------------------
% 4.61/1.91  Preprocessing        : 0.30
% 4.61/1.91  Parsing              : 0.16
% 4.61/1.91  CNF conversion       : 0.02
% 4.61/1.91  Main loop            : 0.82
% 4.61/1.91  Inferencing          : 0.28
% 4.61/1.91  Reduction            : 0.23
% 4.61/1.91  Demodulation         : 0.16
% 4.61/1.91  BG Simplification    : 0.04
% 4.61/1.91  Subsumption          : 0.20
% 4.61/1.91  Abstraction          : 0.05
% 4.61/1.91  MUC search           : 0.00
% 4.61/1.91  Cooper               : 0.00
% 4.61/1.91  Total                : 1.16
% 4.61/1.91  Index Insertion      : 0.00
% 4.61/1.91  Index Deletion       : 0.00
% 4.61/1.91  Index Matching       : 0.00
% 4.61/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
