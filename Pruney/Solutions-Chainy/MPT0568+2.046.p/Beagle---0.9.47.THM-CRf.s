%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:26 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   56 (  74 expanded)
%              Number of leaves         :   37 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  78 expanded)
%              Number of equality atoms :   16 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_22,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_605,plain,(
    ! [A_233,B_234,C_235] :
      ( r2_hidden('#skF_1'(A_233,B_234,C_235),A_233)
      | r2_hidden('#skF_2'(A_233,B_234,C_235),C_235)
      | k4_xboole_0(A_233,B_234) = C_235 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_163,plain,(
    ! [A_126,B_127] :
      ( k2_xboole_0(k1_tarski(A_126),B_127) = B_127
      | ~ r2_hidden(A_126,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_52,plain,(
    ! [A_44,B_45] : k2_xboole_0(k1_tarski(A_44),B_45) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_174,plain,(
    ! [A_126] : ~ r2_hidden(A_126,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_52])).

tff(c_183,plain,(
    ! [D_131,A_132,B_133] :
      ( r2_hidden(D_131,A_132)
      | ~ r2_hidden(D_131,k4_xboole_0(A_132,B_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_190,plain,(
    ! [D_131] :
      ( r2_hidden(D_131,k1_xboole_0)
      | ~ r2_hidden(D_131,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_183])).

tff(c_192,plain,(
    ! [D_131] : ~ r2_hidden(D_131,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_190])).

tff(c_618,plain,(
    ! [B_234,C_235] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_234,C_235),C_235)
      | k4_xboole_0(k1_xboole_0,B_234) = C_235 ) ),
    inference(resolution,[status(thm)],[c_605,c_192])).

tff(c_652,plain,(
    ! [B_234,C_235] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_234,C_235),C_235)
      | k1_xboole_0 = C_235 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_618])).

tff(c_76,plain,(
    ! [A_88] :
      ( r2_hidden('#skF_7'(A_88),A_88)
      | v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_175,plain,(
    ! [B_128,A_129] :
      ( k1_xboole_0 != B_128
      | ~ r2_hidden(A_129,B_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_52])).

tff(c_180,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_76,c_175])).

tff(c_1544,plain,(
    ! [D_282,A_283,B_284] :
      ( r2_hidden(k4_tarski(D_282,'#skF_6'(A_283,B_284,k10_relat_1(A_283,B_284),D_282)),A_283)
      | ~ r2_hidden(D_282,k10_relat_1(A_283,B_284))
      | ~ v1_relat_1(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1569,plain,(
    ! [D_282,B_284] :
      ( ~ r2_hidden(D_282,k10_relat_1(k1_xboole_0,B_284))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1544,c_192])).

tff(c_1620,plain,(
    ! [D_285,B_286] : ~ r2_hidden(D_285,k10_relat_1(k1_xboole_0,B_286)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_1569])).

tff(c_1675,plain,(
    ! [B_286] : k10_relat_1(k1_xboole_0,B_286) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_652,c_1620])).

tff(c_78,plain,(
    k10_relat_1(k1_xboole_0,'#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1675,c_78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.59  
% 3.34/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.59  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_7 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_9
% 3.34/1.59  
% 3.34/1.59  %Foreground sorts:
% 3.34/1.59  
% 3.34/1.59  
% 3.34/1.59  %Background operators:
% 3.34/1.59  
% 3.34/1.59  
% 3.34/1.59  %Foreground operators:
% 3.34/1.59  tff('#skF_7', type, '#skF_7': $i > $i).
% 3.34/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.34/1.59  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.34/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.34/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.34/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.34/1.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.34/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.34/1.59  tff('#skF_10', type, '#skF_10': $i).
% 3.34/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.34/1.59  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.34/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.34/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.34/1.59  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 3.34/1.59  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.34/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.59  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.34/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.34/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.34/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.34/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.34/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.59  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 3.34/1.59  
% 3.34/1.60  tff(f_38, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.34/1.60  tff(f_36, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.34/1.60  tff(f_68, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 3.34/1.60  tff(f_71, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.34/1.60  tff(f_94, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 3.34/1.60  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 3.34/1.60  tff(f_97, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 3.34/1.60  tff(c_22, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.34/1.60  tff(c_605, plain, (![A_233, B_234, C_235]: (r2_hidden('#skF_1'(A_233, B_234, C_235), A_233) | r2_hidden('#skF_2'(A_233, B_234, C_235), C_235) | k4_xboole_0(A_233, B_234)=C_235)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.34/1.60  tff(c_163, plain, (![A_126, B_127]: (k2_xboole_0(k1_tarski(A_126), B_127)=B_127 | ~r2_hidden(A_126, B_127))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.34/1.60  tff(c_52, plain, (![A_44, B_45]: (k2_xboole_0(k1_tarski(A_44), B_45)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.34/1.60  tff(c_174, plain, (![A_126]: (~r2_hidden(A_126, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_163, c_52])).
% 3.34/1.60  tff(c_183, plain, (![D_131, A_132, B_133]: (r2_hidden(D_131, A_132) | ~r2_hidden(D_131, k4_xboole_0(A_132, B_133)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.34/1.60  tff(c_190, plain, (![D_131]: (r2_hidden(D_131, k1_xboole_0) | ~r2_hidden(D_131, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_183])).
% 3.34/1.60  tff(c_192, plain, (![D_131]: (~r2_hidden(D_131, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_174, c_190])).
% 3.34/1.60  tff(c_618, plain, (![B_234, C_235]: (r2_hidden('#skF_2'(k1_xboole_0, B_234, C_235), C_235) | k4_xboole_0(k1_xboole_0, B_234)=C_235)), inference(resolution, [status(thm)], [c_605, c_192])).
% 3.34/1.60  tff(c_652, plain, (![B_234, C_235]: (r2_hidden('#skF_2'(k1_xboole_0, B_234, C_235), C_235) | k1_xboole_0=C_235)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_618])).
% 3.34/1.60  tff(c_76, plain, (![A_88]: (r2_hidden('#skF_7'(A_88), A_88) | v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.34/1.60  tff(c_175, plain, (![B_128, A_129]: (k1_xboole_0!=B_128 | ~r2_hidden(A_129, B_128))), inference(superposition, [status(thm), theory('equality')], [c_163, c_52])).
% 3.34/1.60  tff(c_180, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_76, c_175])).
% 3.34/1.60  tff(c_1544, plain, (![D_282, A_283, B_284]: (r2_hidden(k4_tarski(D_282, '#skF_6'(A_283, B_284, k10_relat_1(A_283, B_284), D_282)), A_283) | ~r2_hidden(D_282, k10_relat_1(A_283, B_284)) | ~v1_relat_1(A_283))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.34/1.60  tff(c_1569, plain, (![D_282, B_284]: (~r2_hidden(D_282, k10_relat_1(k1_xboole_0, B_284)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1544, c_192])).
% 3.34/1.60  tff(c_1620, plain, (![D_285, B_286]: (~r2_hidden(D_285, k10_relat_1(k1_xboole_0, B_286)))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_1569])).
% 3.34/1.60  tff(c_1675, plain, (![B_286]: (k10_relat_1(k1_xboole_0, B_286)=k1_xboole_0)), inference(resolution, [status(thm)], [c_652, c_1620])).
% 3.34/1.60  tff(c_78, plain, (k10_relat_1(k1_xboole_0, '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.34/1.60  tff(c_1684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1675, c_78])).
% 3.34/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.60  
% 3.34/1.60  Inference rules
% 3.34/1.60  ----------------------
% 3.34/1.60  #Ref     : 1
% 3.34/1.60  #Sup     : 364
% 3.34/1.60  #Fact    : 0
% 3.34/1.60  #Define  : 0
% 3.34/1.60  #Split   : 0
% 3.34/1.60  #Chain   : 0
% 3.34/1.60  #Close   : 0
% 3.34/1.60  
% 3.34/1.60  Ordering : KBO
% 3.34/1.60  
% 3.34/1.60  Simplification rules
% 3.34/1.60  ----------------------
% 3.34/1.60  #Subsume      : 86
% 3.34/1.60  #Demod        : 114
% 3.34/1.60  #Tautology    : 137
% 3.34/1.60  #SimpNegUnit  : 13
% 3.34/1.60  #BackRed      : 2
% 3.34/1.60  
% 3.34/1.60  #Partial instantiations: 0
% 3.34/1.60  #Strategies tried      : 1
% 3.34/1.60  
% 3.34/1.60  Timing (in seconds)
% 3.34/1.60  ----------------------
% 3.34/1.61  Preprocessing        : 0.37
% 3.34/1.61  Parsing              : 0.19
% 3.34/1.61  CNF conversion       : 0.03
% 3.34/1.61  Main loop            : 0.46
% 3.34/1.61  Inferencing          : 0.17
% 3.34/1.61  Reduction            : 0.13
% 3.34/1.61  Demodulation         : 0.09
% 3.34/1.61  BG Simplification    : 0.03
% 3.34/1.61  Subsumption          : 0.10
% 3.34/1.61  Abstraction          : 0.03
% 3.34/1.61  MUC search           : 0.00
% 3.34/1.61  Cooper               : 0.00
% 3.34/1.61  Total                : 0.85
% 3.34/1.61  Index Insertion      : 0.00
% 3.34/1.61  Index Deletion       : 0.00
% 3.34/1.61  Index Matching       : 0.00
% 3.34/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
