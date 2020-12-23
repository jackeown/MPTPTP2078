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
% DateTime   : Thu Dec  3 10:01:29 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 143 expanded)
%              Number of leaves         :   33 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 ( 220 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_183,plain,(
    ! [A_102,B_103] :
      ( r2_hidden('#skF_2'(A_102,B_103),A_102)
      | r2_hidden('#skF_3'(A_102,B_103),B_103)
      | k3_tarski(A_102) = B_103 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_68,plain,(
    ! [A_71,B_72] :
      ( ~ r2_hidden(A_71,B_72)
      | ~ r1_xboole_0(k1_tarski(A_71),B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_73,plain,(
    ! [A_71] : ~ r2_hidden(A_71,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_68])).

tff(c_206,plain,(
    ! [A_102] :
      ( r2_hidden('#skF_2'(A_102,k1_xboole_0),A_102)
      | k3_tarski(A_102) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_183,c_73])).

tff(c_42,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_5'(A_44),A_44)
      | v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_74,plain,(
    ! [A_73] : ~ r2_hidden(A_73,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_68])).

tff(c_79,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_74])).

tff(c_879,plain,(
    ! [A_161,B_162,C_163] :
      ( r2_hidden(k4_tarski(A_161,'#skF_8'(A_161,B_162,C_163)),C_163)
      | ~ r2_hidden(A_161,k10_relat_1(C_163,B_162))
      | ~ v1_relat_1(C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_913,plain,(
    ! [A_161,B_162] :
      ( ~ r2_hidden(A_161,k10_relat_1(k1_xboole_0,B_162))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_879,c_73])).

tff(c_925,plain,(
    ! [A_164,B_165] : ~ r2_hidden(A_164,k10_relat_1(k1_xboole_0,B_165)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_913])).

tff(c_965,plain,(
    ! [B_165] : v1_relat_1(k10_relat_1(k1_xboole_0,B_165)) ),
    inference(resolution,[status(thm)],[c_42,c_925])).

tff(c_48,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden(k4_tarski(A_62,'#skF_8'(A_62,B_63,C_64)),C_64)
      | ~ r2_hidden(A_62,k10_relat_1(C_64,B_63))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_958,plain,(
    ! [A_62,B_165,B_63] :
      ( ~ r2_hidden(A_62,k10_relat_1(k10_relat_1(k1_xboole_0,B_165),B_63))
      | ~ v1_relat_1(k10_relat_1(k1_xboole_0,B_165)) ) ),
    inference(resolution,[status(thm)],[c_48,c_925])).

tff(c_1431,plain,(
    ! [A_190,B_191,B_192] : ~ r2_hidden(A_190,k10_relat_1(k10_relat_1(k1_xboole_0,B_191),B_192)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_958])).

tff(c_1470,plain,(
    ! [B_191,B_192] : k3_tarski(k10_relat_1(k10_relat_1(k1_xboole_0,B_191),B_192)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_206,c_1431])).

tff(c_30,plain,(
    ! [A_23,B_24] :
      ( r2_hidden('#skF_2'(A_23,B_24),A_23)
      | r2_hidden('#skF_3'(A_23,B_24),B_24)
      | k3_tarski(A_23) = B_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2098,plain,(
    ! [A_226,B_227] :
      ( r2_hidden('#skF_2'(A_226,k10_relat_1(k1_xboole_0,B_227)),A_226)
      | k3_tarski(A_226) = k10_relat_1(k1_xboole_0,B_227) ) ),
    inference(resolution,[status(thm)],[c_30,c_925])).

tff(c_1430,plain,(
    ! [A_62,B_165,B_63] : ~ r2_hidden(A_62,k10_relat_1(k10_relat_1(k1_xboole_0,B_165),B_63)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_958])).

tff(c_2112,plain,(
    ! [B_165,B_63,B_227] : k3_tarski(k10_relat_1(k10_relat_1(k1_xboole_0,B_165),B_63)) = k10_relat_1(k1_xboole_0,B_227) ),
    inference(resolution,[status(thm)],[c_2098,c_1430])).

tff(c_2163,plain,(
    ! [B_227] : k10_relat_1(k1_xboole_0,B_227) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1470,c_2112])).

tff(c_52,plain,(
    k10_relat_1(k1_xboole_0,'#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2163,c_52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:26:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.64  
% 3.64/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.64  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1
% 3.64/1.64  
% 3.64/1.64  %Foreground sorts:
% 3.64/1.64  
% 3.64/1.64  
% 3.64/1.64  %Background operators:
% 3.64/1.64  
% 3.64/1.64  
% 3.64/1.64  %Foreground operators:
% 3.64/1.64  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.64/1.64  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.64/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.64/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.64/1.64  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.64/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.64/1.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.64/1.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.64/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.64/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.64/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.64/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.64/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.64/1.64  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.64  tff('#skF_9', type, '#skF_9': $i).
% 3.64/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.64/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.64/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.64/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.64  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.64/1.64  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.64/1.64  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.64/1.64  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.64/1.64  
% 3.64/1.65  tff(f_49, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 3.64/1.65  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.64/1.65  tff(f_54, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 3.64/1.65  tff(f_65, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 3.64/1.65  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 3.64/1.65  tff(f_79, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 3.64/1.65  tff(c_183, plain, (![A_102, B_103]: (r2_hidden('#skF_2'(A_102, B_103), A_102) | r2_hidden('#skF_3'(A_102, B_103), B_103) | k3_tarski(A_102)=B_103)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.64/1.65  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.64/1.65  tff(c_68, plain, (![A_71, B_72]: (~r2_hidden(A_71, B_72) | ~r1_xboole_0(k1_tarski(A_71), B_72))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.64/1.65  tff(c_73, plain, (![A_71]: (~r2_hidden(A_71, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_68])).
% 3.64/1.65  tff(c_206, plain, (![A_102]: (r2_hidden('#skF_2'(A_102, k1_xboole_0), A_102) | k3_tarski(A_102)=k1_xboole_0)), inference(resolution, [status(thm)], [c_183, c_73])).
% 3.64/1.65  tff(c_42, plain, (![A_44]: (r2_hidden('#skF_5'(A_44), A_44) | v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.64/1.65  tff(c_74, plain, (![A_73]: (~r2_hidden(A_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_68])).
% 3.64/1.65  tff(c_79, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_74])).
% 3.64/1.65  tff(c_879, plain, (![A_161, B_162, C_163]: (r2_hidden(k4_tarski(A_161, '#skF_8'(A_161, B_162, C_163)), C_163) | ~r2_hidden(A_161, k10_relat_1(C_163, B_162)) | ~v1_relat_1(C_163))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.64/1.65  tff(c_913, plain, (![A_161, B_162]: (~r2_hidden(A_161, k10_relat_1(k1_xboole_0, B_162)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_879, c_73])).
% 3.64/1.65  tff(c_925, plain, (![A_164, B_165]: (~r2_hidden(A_164, k10_relat_1(k1_xboole_0, B_165)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_913])).
% 3.64/1.65  tff(c_965, plain, (![B_165]: (v1_relat_1(k10_relat_1(k1_xboole_0, B_165)))), inference(resolution, [status(thm)], [c_42, c_925])).
% 3.64/1.65  tff(c_48, plain, (![A_62, B_63, C_64]: (r2_hidden(k4_tarski(A_62, '#skF_8'(A_62, B_63, C_64)), C_64) | ~r2_hidden(A_62, k10_relat_1(C_64, B_63)) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.64/1.65  tff(c_958, plain, (![A_62, B_165, B_63]: (~r2_hidden(A_62, k10_relat_1(k10_relat_1(k1_xboole_0, B_165), B_63)) | ~v1_relat_1(k10_relat_1(k1_xboole_0, B_165)))), inference(resolution, [status(thm)], [c_48, c_925])).
% 3.64/1.65  tff(c_1431, plain, (![A_190, B_191, B_192]: (~r2_hidden(A_190, k10_relat_1(k10_relat_1(k1_xboole_0, B_191), B_192)))), inference(demodulation, [status(thm), theory('equality')], [c_965, c_958])).
% 3.64/1.65  tff(c_1470, plain, (![B_191, B_192]: (k3_tarski(k10_relat_1(k10_relat_1(k1_xboole_0, B_191), B_192))=k1_xboole_0)), inference(resolution, [status(thm)], [c_206, c_1431])).
% 3.64/1.65  tff(c_30, plain, (![A_23, B_24]: (r2_hidden('#skF_2'(A_23, B_24), A_23) | r2_hidden('#skF_3'(A_23, B_24), B_24) | k3_tarski(A_23)=B_24)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.64/1.65  tff(c_2098, plain, (![A_226, B_227]: (r2_hidden('#skF_2'(A_226, k10_relat_1(k1_xboole_0, B_227)), A_226) | k3_tarski(A_226)=k10_relat_1(k1_xboole_0, B_227))), inference(resolution, [status(thm)], [c_30, c_925])).
% 3.64/1.65  tff(c_1430, plain, (![A_62, B_165, B_63]: (~r2_hidden(A_62, k10_relat_1(k10_relat_1(k1_xboole_0, B_165), B_63)))), inference(demodulation, [status(thm), theory('equality')], [c_965, c_958])).
% 3.64/1.65  tff(c_2112, plain, (![B_165, B_63, B_227]: (k3_tarski(k10_relat_1(k10_relat_1(k1_xboole_0, B_165), B_63))=k10_relat_1(k1_xboole_0, B_227))), inference(resolution, [status(thm)], [c_2098, c_1430])).
% 3.64/1.65  tff(c_2163, plain, (![B_227]: (k10_relat_1(k1_xboole_0, B_227)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1470, c_2112])).
% 3.64/1.65  tff(c_52, plain, (k10_relat_1(k1_xboole_0, '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.64/1.65  tff(c_2203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2163, c_52])).
% 3.64/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.65  
% 3.64/1.65  Inference rules
% 3.64/1.65  ----------------------
% 3.64/1.65  #Ref     : 1
% 3.64/1.65  #Sup     : 444
% 3.64/1.65  #Fact    : 0
% 3.64/1.65  #Define  : 0
% 3.64/1.65  #Split   : 0
% 3.64/1.65  #Chain   : 0
% 3.64/1.65  #Close   : 0
% 3.64/1.65  
% 3.64/1.65  Ordering : KBO
% 3.64/1.65  
% 3.64/1.65  Simplification rules
% 3.64/1.65  ----------------------
% 3.64/1.65  #Subsume      : 146
% 3.64/1.65  #Demod        : 280
% 3.64/1.65  #Tautology    : 134
% 3.64/1.65  #SimpNegUnit  : 29
% 3.64/1.65  #BackRed      : 20
% 3.64/1.65  
% 3.64/1.65  #Partial instantiations: 0
% 3.64/1.65  #Strategies tried      : 1
% 3.64/1.65  
% 3.64/1.65  Timing (in seconds)
% 3.64/1.65  ----------------------
% 3.64/1.65  Preprocessing        : 0.32
% 3.64/1.65  Parsing              : 0.17
% 3.64/1.65  CNF conversion       : 0.02
% 3.64/1.65  Main loop            : 0.57
% 3.64/1.65  Inferencing          : 0.21
% 3.64/1.65  Reduction            : 0.16
% 3.64/1.65  Demodulation         : 0.11
% 3.64/1.65  BG Simplification    : 0.03
% 3.64/1.65  Subsumption          : 0.13
% 3.64/1.65  Abstraction          : 0.03
% 3.64/1.65  MUC search           : 0.00
% 3.64/1.65  Cooper               : 0.00
% 3.64/1.65  Total                : 0.91
% 3.64/1.65  Index Insertion      : 0.00
% 3.64/1.66  Index Deletion       : 0.00
% 3.64/1.66  Index Matching       : 0.00
% 3.64/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
