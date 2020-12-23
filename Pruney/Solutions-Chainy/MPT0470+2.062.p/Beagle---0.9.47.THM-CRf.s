%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:09 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   60 (  88 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 144 expanded)
%              Number of equality atoms :   22 (  36 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_8 > #skF_4 > #skF_5 > #skF_2 > #skF_9 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_59,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_28,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_38,plain,
    ( k5_relat_1('#skF_9',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_91,plain,(
    k5_relat_1(k1_xboole_0,'#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_48,plain,(
    ! [A_113] :
      ( v1_relat_1(A_113)
      | ~ v1_xboole_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_48])).

tff(c_34,plain,(
    ! [A_107,B_108] :
      ( v1_relat_1(k5_relat_1(A_107,B_108))
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    ! [A_109] :
      ( k1_xboole_0 = A_109
      | r2_hidden(k4_tarski('#skF_7'(A_109),'#skF_8'(A_109)),A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_116,plain,(
    ! [D_130,A_131,B_132,E_133] :
      ( r2_hidden(k4_tarski(D_130,'#skF_1'(k5_relat_1(A_131,B_132),B_132,A_131,E_133,D_130)),A_131)
      | ~ r2_hidden(k4_tarski(D_130,E_133),k5_relat_1(A_131,B_132))
      | ~ v1_relat_1(k5_relat_1(A_131,B_132))
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_92,plain,(
    ! [B_121,A_122] :
      ( ~ r2_hidden(B_121,A_122)
      | k4_xboole_0(A_122,k1_tarski(B_121)) != A_122 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [B_121] : ~ r2_hidden(B_121,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_92])).

tff(c_122,plain,(
    ! [D_130,E_133,B_132] :
      ( ~ r2_hidden(k4_tarski(D_130,E_133),k5_relat_1(k1_xboole_0,B_132))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_132))
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_116,c_101])).

tff(c_127,plain,(
    ! [D_134,E_135,B_136] :
      ( ~ r2_hidden(k4_tarski(D_134,E_135),k5_relat_1(k1_xboole_0,B_136))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_136))
      | ~ v1_relat_1(B_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_122])).

tff(c_138,plain,(
    ! [B_137] :
      ( ~ v1_relat_1(B_137)
      | k5_relat_1(k1_xboole_0,B_137) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_137)) ) ),
    inference(resolution,[status(thm)],[c_36,c_127])).

tff(c_142,plain,(
    ! [B_108] :
      ( k5_relat_1(k1_xboole_0,B_108) = k1_xboole_0
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_138])).

tff(c_146,plain,(
    ! [B_138] :
      ( k5_relat_1(k1_xboole_0,B_138) = k1_xboole_0
      | ~ v1_relat_1(B_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_142])).

tff(c_155,plain,(
    k5_relat_1(k1_xboole_0,'#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_146])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_155])).

tff(c_162,plain,(
    k5_relat_1('#skF_9',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_257,plain,(
    ! [A_157,B_158,E_159,D_160] :
      ( r2_hidden(k4_tarski('#skF_1'(k5_relat_1(A_157,B_158),B_158,A_157,E_159,D_160),E_159),B_158)
      | ~ r2_hidden(k4_tarski(D_160,E_159),k5_relat_1(A_157,B_158))
      | ~ v1_relat_1(k5_relat_1(A_157,B_158))
      | ~ v1_relat_1(B_158)
      | ~ v1_relat_1(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_173,plain,(
    ! [B_139,A_140] :
      ( ~ r2_hidden(B_139,A_140)
      | k4_xboole_0(A_140,k1_tarski(B_139)) != A_140 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_182,plain,(
    ! [B_139] : ~ r2_hidden(B_139,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_173])).

tff(c_267,plain,(
    ! [D_160,E_159,A_157] :
      ( ~ r2_hidden(k4_tarski(D_160,E_159),k5_relat_1(A_157,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_157,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_157) ) ),
    inference(resolution,[status(thm)],[c_257,c_182])).

tff(c_352,plain,(
    ! [D_163,E_164,A_165] :
      ( ~ r2_hidden(k4_tarski(D_163,E_164),k5_relat_1(A_165,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_165,k1_xboole_0))
      | ~ v1_relat_1(A_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_267])).

tff(c_373,plain,(
    ! [A_166] :
      ( ~ v1_relat_1(A_166)
      | k5_relat_1(A_166,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_166,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_36,c_352])).

tff(c_380,plain,(
    ! [A_107] :
      ( k5_relat_1(A_107,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_107) ) ),
    inference(resolution,[status(thm)],[c_34,c_373])).

tff(c_386,plain,(
    ! [A_167] :
      ( k5_relat_1(A_167,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_380])).

tff(c_395,plain,(
    k5_relat_1('#skF_9',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_386])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_395])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.37  
% 2.48/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.38  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_8 > #skF_4 > #skF_5 > #skF_2 > #skF_9 > #skF_1 > #skF_3
% 2.48/1.38  
% 2.48/1.38  %Foreground sorts:
% 2.48/1.38  
% 2.48/1.38  
% 2.48/1.38  %Background operators:
% 2.48/1.38  
% 2.48/1.38  
% 2.48/1.38  %Foreground operators:
% 2.48/1.38  tff('#skF_7', type, '#skF_7': $i > $i).
% 2.48/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.38  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.48/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.48/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.48/1.38  tff('#skF_8', type, '#skF_8': $i > $i).
% 2.48/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.48/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.38  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.48/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.48/1.38  tff('#skF_9', type, '#skF_9': $i).
% 2.48/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.48/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.48/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.48/1.38  
% 2.72/1.39  tff(f_80, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.72/1.39  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.72/1.39  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.72/1.39  tff(f_65, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.72/1.39  tff(f_73, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 2.72/1.39  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 2.72/1.39  tff(f_28, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.72/1.39  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.72/1.39  tff(c_38, plain, (k5_relat_1('#skF_9', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.72/1.39  tff(c_91, plain, (k5_relat_1(k1_xboole_0, '#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 2.72/1.39  tff(c_40, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.72/1.39  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.72/1.39  tff(c_48, plain, (![A_113]: (v1_relat_1(A_113) | ~v1_xboole_0(A_113))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.72/1.39  tff(c_52, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_48])).
% 2.72/1.39  tff(c_34, plain, (![A_107, B_108]: (v1_relat_1(k5_relat_1(A_107, B_108)) | ~v1_relat_1(B_108) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.72/1.39  tff(c_36, plain, (![A_109]: (k1_xboole_0=A_109 | r2_hidden(k4_tarski('#skF_7'(A_109), '#skF_8'(A_109)), A_109) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.72/1.39  tff(c_116, plain, (![D_130, A_131, B_132, E_133]: (r2_hidden(k4_tarski(D_130, '#skF_1'(k5_relat_1(A_131, B_132), B_132, A_131, E_133, D_130)), A_131) | ~r2_hidden(k4_tarski(D_130, E_133), k5_relat_1(A_131, B_132)) | ~v1_relat_1(k5_relat_1(A_131, B_132)) | ~v1_relat_1(B_132) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.72/1.39  tff(c_4, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.72/1.39  tff(c_92, plain, (![B_121, A_122]: (~r2_hidden(B_121, A_122) | k4_xboole_0(A_122, k1_tarski(B_121))!=A_122)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.72/1.39  tff(c_101, plain, (![B_121]: (~r2_hidden(B_121, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_92])).
% 2.72/1.39  tff(c_122, plain, (![D_130, E_133, B_132]: (~r2_hidden(k4_tarski(D_130, E_133), k5_relat_1(k1_xboole_0, B_132)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_132)) | ~v1_relat_1(B_132) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_116, c_101])).
% 2.72/1.39  tff(c_127, plain, (![D_134, E_135, B_136]: (~r2_hidden(k4_tarski(D_134, E_135), k5_relat_1(k1_xboole_0, B_136)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_136)) | ~v1_relat_1(B_136))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_122])).
% 2.72/1.39  tff(c_138, plain, (![B_137]: (~v1_relat_1(B_137) | k5_relat_1(k1_xboole_0, B_137)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_137)))), inference(resolution, [status(thm)], [c_36, c_127])).
% 2.72/1.39  tff(c_142, plain, (![B_108]: (k5_relat_1(k1_xboole_0, B_108)=k1_xboole_0 | ~v1_relat_1(B_108) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_138])).
% 2.72/1.39  tff(c_146, plain, (![B_138]: (k5_relat_1(k1_xboole_0, B_138)=k1_xboole_0 | ~v1_relat_1(B_138))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_142])).
% 2.72/1.39  tff(c_155, plain, (k5_relat_1(k1_xboole_0, '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_146])).
% 2.72/1.39  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_155])).
% 2.72/1.39  tff(c_162, plain, (k5_relat_1('#skF_9', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.72/1.39  tff(c_257, plain, (![A_157, B_158, E_159, D_160]: (r2_hidden(k4_tarski('#skF_1'(k5_relat_1(A_157, B_158), B_158, A_157, E_159, D_160), E_159), B_158) | ~r2_hidden(k4_tarski(D_160, E_159), k5_relat_1(A_157, B_158)) | ~v1_relat_1(k5_relat_1(A_157, B_158)) | ~v1_relat_1(B_158) | ~v1_relat_1(A_157))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.72/1.39  tff(c_173, plain, (![B_139, A_140]: (~r2_hidden(B_139, A_140) | k4_xboole_0(A_140, k1_tarski(B_139))!=A_140)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.72/1.39  tff(c_182, plain, (![B_139]: (~r2_hidden(B_139, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_173])).
% 2.72/1.39  tff(c_267, plain, (![D_160, E_159, A_157]: (~r2_hidden(k4_tarski(D_160, E_159), k5_relat_1(A_157, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_157, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_157))), inference(resolution, [status(thm)], [c_257, c_182])).
% 2.72/1.39  tff(c_352, plain, (![D_163, E_164, A_165]: (~r2_hidden(k4_tarski(D_163, E_164), k5_relat_1(A_165, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_165, k1_xboole_0)) | ~v1_relat_1(A_165))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_267])).
% 2.72/1.39  tff(c_373, plain, (![A_166]: (~v1_relat_1(A_166) | k5_relat_1(A_166, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_166, k1_xboole_0)))), inference(resolution, [status(thm)], [c_36, c_352])).
% 2.72/1.39  tff(c_380, plain, (![A_107]: (k5_relat_1(A_107, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_107))), inference(resolution, [status(thm)], [c_34, c_373])).
% 2.72/1.39  tff(c_386, plain, (![A_167]: (k5_relat_1(A_167, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_167))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_380])).
% 2.72/1.39  tff(c_395, plain, (k5_relat_1('#skF_9', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_386])).
% 2.72/1.39  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_395])).
% 2.72/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.39  
% 2.72/1.39  Inference rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Ref     : 0
% 2.72/1.39  #Sup     : 70
% 2.72/1.39  #Fact    : 0
% 2.72/1.39  #Define  : 0
% 2.72/1.39  #Split   : 1
% 2.72/1.39  #Chain   : 0
% 2.72/1.39  #Close   : 0
% 2.72/1.39  
% 2.72/1.39  Ordering : KBO
% 2.72/1.39  
% 2.72/1.39  Simplification rules
% 2.72/1.39  ----------------------
% 2.72/1.39  #Subsume      : 13
% 2.72/1.39  #Demod        : 65
% 2.72/1.39  #Tautology    : 31
% 2.72/1.39  #SimpNegUnit  : 6
% 2.72/1.39  #BackRed      : 0
% 2.72/1.39  
% 2.72/1.39  #Partial instantiations: 0
% 2.72/1.39  #Strategies tried      : 1
% 2.72/1.39  
% 2.72/1.39  Timing (in seconds)
% 2.72/1.39  ----------------------
% 2.72/1.39  Preprocessing        : 0.35
% 2.72/1.40  Parsing              : 0.17
% 2.72/1.40  CNF conversion       : 0.03
% 2.72/1.40  Main loop            : 0.26
% 2.72/1.40  Inferencing          : 0.10
% 2.72/1.40  Reduction            : 0.07
% 2.72/1.40  Demodulation         : 0.05
% 2.72/1.40  BG Simplification    : 0.02
% 2.72/1.40  Subsumption          : 0.04
% 2.72/1.40  Abstraction          : 0.02
% 2.72/1.40  MUC search           : 0.00
% 2.72/1.40  Cooper               : 0.00
% 2.72/1.40  Total                : 0.64
% 2.72/1.40  Index Insertion      : 0.00
% 2.72/1.40  Index Deletion       : 0.00
% 2.72/1.40  Index Matching       : 0.00
% 2.72/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
