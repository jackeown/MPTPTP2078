%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:29 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   56 (  71 expanded)
%              Number of leaves         :   38 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  73 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_40,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_309,plain,(
    ! [A_141,B_142] :
      ( r2_hidden('#skF_3'(A_141,B_142),A_141)
      | r2_hidden('#skF_4'(A_141,B_142),B_142)
      | k3_tarski(A_141) = B_142 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,B_91)
      | ~ r2_hidden(C_92,k3_xboole_0(A_90,B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_98,plain,(
    ! [A_6,C_92] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_92,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_91])).

tff(c_101,plain,(
    ! [C_92] : ~ r2_hidden(C_92,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_98])).

tff(c_331,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_142),B_142)
      | k3_tarski(k1_xboole_0) = B_142 ) ),
    inference(resolution,[status(thm)],[c_309,c_101])).

tff(c_366,plain,(
    ! [B_142] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_142),B_142)
      | k1_xboole_0 = B_142 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_331])).

tff(c_48,plain,(
    ! [A_56] :
      ( r2_hidden('#skF_6'(A_56),A_56)
      | v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_111,plain,(
    ! [C_96] : ~ r2_hidden(C_96,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_98])).

tff(c_116,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_48,c_111])).

tff(c_894,plain,(
    ! [A_176,B_177,C_178] :
      ( r2_hidden(k4_tarski(A_176,'#skF_9'(A_176,B_177,C_178)),C_178)
      | ~ r2_hidden(A_176,k10_relat_1(C_178,B_177))
      | ~ v1_relat_1(C_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_924,plain,(
    ! [A_176,B_177] :
      ( ~ r2_hidden(A_176,k10_relat_1(k1_xboole_0,B_177))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_894,c_101])).

tff(c_940,plain,(
    ! [A_179,B_180] : ~ r2_hidden(A_179,k10_relat_1(k1_xboole_0,B_180)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_924])).

tff(c_973,plain,(
    ! [B_180] : k10_relat_1(k1_xboole_0,B_180) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_366,c_940])).

tff(c_58,plain,(
    k10_relat_1(k1_xboole_0,'#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:16:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.44  
% 2.76/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.44  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_6 > #skF_4
% 2.76/1.44  
% 2.76/1.44  %Foreground sorts:
% 2.76/1.44  
% 2.76/1.44  
% 2.76/1.44  %Background operators:
% 2.76/1.44  
% 2.76/1.44  
% 2.76/1.44  %Foreground operators:
% 2.76/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.76/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.76/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.76/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.76/1.44  tff('#skF_10', type, '#skF_10': $i).
% 2.76/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.76/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.76/1.44  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.76/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.76/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.76/1.44  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.76/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.44  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 2.76/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.76/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.76/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.76/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.76/1.44  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.76/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.76/1.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.76/1.44  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.76/1.44  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.76/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.76/1.44  
% 2.76/1.45  tff(f_66, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.76/1.45  tff(f_65, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 2.76/1.45  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.76/1.45  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.76/1.45  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.76/1.45  tff(f_78, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.76/1.45  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.76/1.45  tff(f_92, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.76/1.45  tff(c_40, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.76/1.45  tff(c_309, plain, (![A_141, B_142]: (r2_hidden('#skF_3'(A_141, B_142), A_141) | r2_hidden('#skF_4'(A_141, B_142), B_142) | k3_tarski(A_141)=B_142)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.76/1.45  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.76/1.45  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.76/1.45  tff(c_91, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, B_91) | ~r2_hidden(C_92, k3_xboole_0(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.76/1.45  tff(c_98, plain, (![A_6, C_92]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_92, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_91])).
% 2.76/1.45  tff(c_101, plain, (![C_92]: (~r2_hidden(C_92, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_98])).
% 2.76/1.45  tff(c_331, plain, (![B_142]: (r2_hidden('#skF_4'(k1_xboole_0, B_142), B_142) | k3_tarski(k1_xboole_0)=B_142)), inference(resolution, [status(thm)], [c_309, c_101])).
% 2.76/1.45  tff(c_366, plain, (![B_142]: (r2_hidden('#skF_4'(k1_xboole_0, B_142), B_142) | k1_xboole_0=B_142)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_331])).
% 2.76/1.45  tff(c_48, plain, (![A_56]: (r2_hidden('#skF_6'(A_56), A_56) | v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.76/1.45  tff(c_111, plain, (![C_96]: (~r2_hidden(C_96, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_98])).
% 2.76/1.45  tff(c_116, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_111])).
% 2.76/1.45  tff(c_894, plain, (![A_176, B_177, C_178]: (r2_hidden(k4_tarski(A_176, '#skF_9'(A_176, B_177, C_178)), C_178) | ~r2_hidden(A_176, k10_relat_1(C_178, B_177)) | ~v1_relat_1(C_178))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.76/1.45  tff(c_924, plain, (![A_176, B_177]: (~r2_hidden(A_176, k10_relat_1(k1_xboole_0, B_177)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_894, c_101])).
% 2.76/1.45  tff(c_940, plain, (![A_179, B_180]: (~r2_hidden(A_179, k10_relat_1(k1_xboole_0, B_180)))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_924])).
% 2.76/1.45  tff(c_973, plain, (![B_180]: (k10_relat_1(k1_xboole_0, B_180)=k1_xboole_0)), inference(resolution, [status(thm)], [c_366, c_940])).
% 2.76/1.45  tff(c_58, plain, (k10_relat_1(k1_xboole_0, '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.76/1.45  tff(c_982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_973, c_58])).
% 2.76/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.45  
% 2.76/1.45  Inference rules
% 2.76/1.45  ----------------------
% 2.76/1.45  #Ref     : 1
% 2.76/1.45  #Sup     : 200
% 2.76/1.45  #Fact    : 0
% 2.76/1.45  #Define  : 0
% 2.76/1.45  #Split   : 0
% 2.76/1.45  #Chain   : 0
% 2.76/1.45  #Close   : 0
% 2.76/1.45  
% 2.76/1.45  Ordering : KBO
% 2.76/1.45  
% 2.76/1.45  Simplification rules
% 2.76/1.45  ----------------------
% 2.76/1.45  #Subsume      : 49
% 2.76/1.45  #Demod        : 108
% 2.76/1.45  #Tautology    : 66
% 2.76/1.45  #SimpNegUnit  : 12
% 2.76/1.45  #BackRed      : 2
% 2.76/1.45  
% 2.76/1.45  #Partial instantiations: 0
% 2.76/1.45  #Strategies tried      : 1
% 2.76/1.45  
% 2.76/1.45  Timing (in seconds)
% 2.76/1.45  ----------------------
% 2.76/1.46  Preprocessing        : 0.35
% 2.76/1.46  Parsing              : 0.19
% 2.76/1.46  CNF conversion       : 0.03
% 2.76/1.46  Main loop            : 0.33
% 2.76/1.46  Inferencing          : 0.13
% 2.76/1.46  Reduction            : 0.09
% 2.76/1.46  Demodulation         : 0.07
% 2.76/1.46  BG Simplification    : 0.02
% 2.76/1.46  Subsumption          : 0.07
% 2.76/1.46  Abstraction          : 0.02
% 2.76/1.46  MUC search           : 0.00
% 2.76/1.46  Cooper               : 0.00
% 2.76/1.46  Total                : 0.71
% 2.76/1.46  Index Insertion      : 0.00
% 2.76/1.46  Index Deletion       : 0.00
% 2.76/1.46  Index Matching       : 0.00
% 2.76/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
