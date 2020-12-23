%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:09 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   58 (  88 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 144 expanded)
%              Number of equality atoms :   20 (  34 expanded)
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

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_61,axiom,(
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

tff(f_28,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_40,plain,
    ( k5_relat_1('#skF_9',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_78,plain,(
    k5_relat_1(k1_xboole_0,'#skF_9') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_42,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_50,plain,(
    ! [A_114] :
      ( v1_relat_1(A_114)
      | ~ v1_xboole_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_50])).

tff(c_36,plain,(
    ! [A_108,B_109] :
      ( v1_relat_1(k5_relat_1(A_108,B_109))
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [A_110] :
      ( k1_xboole_0 = A_110
      | r2_hidden(k4_tarski('#skF_7'(A_110),'#skF_8'(A_110)),A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_158,plain,(
    ! [D_140,E_141,B_142,A_143] :
      ( r2_hidden(k4_tarski(D_140,'#skF_1'(E_141,B_142,D_140,A_143,k5_relat_1(A_143,B_142))),A_143)
      | ~ r2_hidden(k4_tarski(D_140,E_141),k5_relat_1(A_143,B_142))
      | ~ v1_relat_1(k5_relat_1(A_143,B_142))
      | ~ v1_relat_1(B_142)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_64,plain,(
    ! [C_116,B_117] : ~ r2_hidden(C_116,k4_xboole_0(B_117,k1_tarski(C_116))) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_67,plain,(
    ! [C_116] : ~ r2_hidden(C_116,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_64])).

tff(c_168,plain,(
    ! [D_140,E_141,B_142] :
      ( ~ r2_hidden(k4_tarski(D_140,E_141),k5_relat_1(k1_xboole_0,B_142))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_142))
      | ~ v1_relat_1(B_142)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_158,c_67])).

tff(c_190,plain,(
    ! [D_148,E_149,B_150] :
      ( ~ r2_hidden(k4_tarski(D_148,E_149),k5_relat_1(k1_xboole_0,B_150))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_150))
      | ~ v1_relat_1(B_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_168])).

tff(c_218,plain,(
    ! [B_151] :
      ( ~ v1_relat_1(B_151)
      | k5_relat_1(k1_xboole_0,B_151) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_151)) ) ),
    inference(resolution,[status(thm)],[c_38,c_190])).

tff(c_222,plain,(
    ! [B_109] :
      ( k5_relat_1(k1_xboole_0,B_109) = k1_xboole_0
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_36,c_218])).

tff(c_226,plain,(
    ! [B_152] :
      ( k5_relat_1(k1_xboole_0,B_152) = k1_xboole_0
      | ~ v1_relat_1(B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_222])).

tff(c_235,plain,(
    k5_relat_1(k1_xboole_0,'#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_226])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_235])).

tff(c_242,plain,(
    k5_relat_1('#skF_9',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_401,plain,(
    ! [E_180,B_181,D_182,A_183] :
      ( r2_hidden(k4_tarski('#skF_1'(E_180,B_181,D_182,A_183,k5_relat_1(A_183,B_181)),E_180),B_181)
      | ~ r2_hidden(k4_tarski(D_182,E_180),k5_relat_1(A_183,B_181))
      | ~ v1_relat_1(k5_relat_1(A_183,B_181))
      | ~ v1_relat_1(B_181)
      | ~ v1_relat_1(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_415,plain,(
    ! [D_182,E_180,A_183] :
      ( ~ r2_hidden(k4_tarski(D_182,E_180),k5_relat_1(A_183,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_183,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_183) ) ),
    inference(resolution,[status(thm)],[c_401,c_67])).

tff(c_548,plain,(
    ! [D_190,E_191,A_192] :
      ( ~ r2_hidden(k4_tarski(D_190,E_191),k5_relat_1(A_192,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_192,k1_xboole_0))
      | ~ v1_relat_1(A_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_415])).

tff(c_587,plain,(
    ! [A_193] :
      ( ~ v1_relat_1(A_193)
      | k5_relat_1(A_193,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_193,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_38,c_548])).

tff(c_594,plain,(
    ! [A_108] :
      ( k5_relat_1(A_108,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_108) ) ),
    inference(resolution,[status(thm)],[c_36,c_587])).

tff(c_600,plain,(
    ! [A_194] :
      ( k5_relat_1(A_194,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_594])).

tff(c_609,plain,(
    k5_relat_1('#skF_9',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_600])).

tff(c_616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_242,c_609])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.37  
% 2.58/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.37  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_8 > #skF_4 > #skF_5 > #skF_2 > #skF_9 > #skF_1 > #skF_3
% 2.58/1.37  
% 2.58/1.37  %Foreground sorts:
% 2.58/1.37  
% 2.58/1.37  
% 2.58/1.37  %Background operators:
% 2.58/1.37  
% 2.58/1.37  
% 2.58/1.37  %Foreground operators:
% 2.58/1.37  tff('#skF_7', type, '#skF_7': $i > $i).
% 2.58/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.37  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.58/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.58/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.58/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.58/1.37  tff('#skF_8', type, '#skF_8': $i > $i).
% 2.58/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.58/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.37  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.58/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.58/1.37  tff('#skF_9', type, '#skF_9': $i).
% 2.58/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.58/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.58/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.58/1.37  
% 2.58/1.38  tff(f_82, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.58/1.38  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.58/1.38  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.58/1.38  tff(f_67, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.58/1.38  tff(f_75, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 2.58/1.38  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 2.58/1.38  tff(f_28, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.58/1.38  tff(f_39, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.58/1.38  tff(c_40, plain, (k5_relat_1('#skF_9', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.58/1.38  tff(c_78, plain, (k5_relat_1(k1_xboole_0, '#skF_9')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 2.58/1.38  tff(c_42, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.58/1.38  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.58/1.38  tff(c_50, plain, (![A_114]: (v1_relat_1(A_114) | ~v1_xboole_0(A_114))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.58/1.38  tff(c_54, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_50])).
% 2.58/1.38  tff(c_36, plain, (![A_108, B_109]: (v1_relat_1(k5_relat_1(A_108, B_109)) | ~v1_relat_1(B_109) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.38  tff(c_38, plain, (![A_110]: (k1_xboole_0=A_110 | r2_hidden(k4_tarski('#skF_7'(A_110), '#skF_8'(A_110)), A_110) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.58/1.38  tff(c_158, plain, (![D_140, E_141, B_142, A_143]: (r2_hidden(k4_tarski(D_140, '#skF_1'(E_141, B_142, D_140, A_143, k5_relat_1(A_143, B_142))), A_143) | ~r2_hidden(k4_tarski(D_140, E_141), k5_relat_1(A_143, B_142)) | ~v1_relat_1(k5_relat_1(A_143, B_142)) | ~v1_relat_1(B_142) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.58/1.38  tff(c_4, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.58/1.38  tff(c_64, plain, (![C_116, B_117]: (~r2_hidden(C_116, k4_xboole_0(B_117, k1_tarski(C_116))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.58/1.38  tff(c_67, plain, (![C_116]: (~r2_hidden(C_116, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_64])).
% 2.58/1.38  tff(c_168, plain, (![D_140, E_141, B_142]: (~r2_hidden(k4_tarski(D_140, E_141), k5_relat_1(k1_xboole_0, B_142)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_142)) | ~v1_relat_1(B_142) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_158, c_67])).
% 2.58/1.38  tff(c_190, plain, (![D_148, E_149, B_150]: (~r2_hidden(k4_tarski(D_148, E_149), k5_relat_1(k1_xboole_0, B_150)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_150)) | ~v1_relat_1(B_150))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_168])).
% 2.58/1.38  tff(c_218, plain, (![B_151]: (~v1_relat_1(B_151) | k5_relat_1(k1_xboole_0, B_151)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_151)))), inference(resolution, [status(thm)], [c_38, c_190])).
% 2.58/1.38  tff(c_222, plain, (![B_109]: (k5_relat_1(k1_xboole_0, B_109)=k1_xboole_0 | ~v1_relat_1(B_109) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_36, c_218])).
% 2.58/1.38  tff(c_226, plain, (![B_152]: (k5_relat_1(k1_xboole_0, B_152)=k1_xboole_0 | ~v1_relat_1(B_152))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_222])).
% 2.58/1.38  tff(c_235, plain, (k5_relat_1(k1_xboole_0, '#skF_9')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_226])).
% 2.58/1.38  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_235])).
% 2.58/1.38  tff(c_242, plain, (k5_relat_1('#skF_9', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 2.58/1.38  tff(c_401, plain, (![E_180, B_181, D_182, A_183]: (r2_hidden(k4_tarski('#skF_1'(E_180, B_181, D_182, A_183, k5_relat_1(A_183, B_181)), E_180), B_181) | ~r2_hidden(k4_tarski(D_182, E_180), k5_relat_1(A_183, B_181)) | ~v1_relat_1(k5_relat_1(A_183, B_181)) | ~v1_relat_1(B_181) | ~v1_relat_1(A_183))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.58/1.38  tff(c_415, plain, (![D_182, E_180, A_183]: (~r2_hidden(k4_tarski(D_182, E_180), k5_relat_1(A_183, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_183, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_183))), inference(resolution, [status(thm)], [c_401, c_67])).
% 2.58/1.38  tff(c_548, plain, (![D_190, E_191, A_192]: (~r2_hidden(k4_tarski(D_190, E_191), k5_relat_1(A_192, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_192, k1_xboole_0)) | ~v1_relat_1(A_192))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_415])).
% 2.58/1.38  tff(c_587, plain, (![A_193]: (~v1_relat_1(A_193) | k5_relat_1(A_193, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_193, k1_xboole_0)))), inference(resolution, [status(thm)], [c_38, c_548])).
% 2.58/1.38  tff(c_594, plain, (![A_108]: (k5_relat_1(A_108, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_108))), inference(resolution, [status(thm)], [c_36, c_587])).
% 2.58/1.38  tff(c_600, plain, (![A_194]: (k5_relat_1(A_194, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_194))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_594])).
% 2.58/1.38  tff(c_609, plain, (k5_relat_1('#skF_9', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_600])).
% 2.58/1.38  tff(c_616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_242, c_609])).
% 2.58/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.38  
% 2.58/1.38  Inference rules
% 2.58/1.38  ----------------------
% 2.58/1.38  #Ref     : 0
% 2.58/1.38  #Sup     : 108
% 2.58/1.38  #Fact    : 0
% 2.58/1.38  #Define  : 0
% 2.58/1.38  #Split   : 1
% 2.58/1.38  #Chain   : 0
% 2.58/1.38  #Close   : 0
% 2.58/1.38  
% 2.58/1.38  Ordering : KBO
% 2.58/1.38  
% 2.58/1.38  Simplification rules
% 2.58/1.38  ----------------------
% 2.58/1.39  #Subsume      : 25
% 2.58/1.39  #Demod        : 101
% 2.58/1.39  #Tautology    : 36
% 2.58/1.39  #SimpNegUnit  : 17
% 2.58/1.39  #BackRed      : 0
% 2.58/1.39  
% 2.58/1.39  #Partial instantiations: 0
% 2.58/1.39  #Strategies tried      : 1
% 2.58/1.39  
% 2.58/1.39  Timing (in seconds)
% 2.58/1.39  ----------------------
% 2.58/1.39  Preprocessing        : 0.31
% 2.58/1.39  Parsing              : 0.16
% 2.58/1.39  CNF conversion       : 0.03
% 2.58/1.39  Main loop            : 0.28
% 2.58/1.39  Inferencing          : 0.10
% 2.58/1.39  Reduction            : 0.08
% 2.58/1.39  Demodulation         : 0.05
% 2.58/1.39  BG Simplification    : 0.02
% 2.58/1.39  Subsumption          : 0.05
% 2.58/1.39  Abstraction          : 0.02
% 2.58/1.39  MUC search           : 0.00
% 2.58/1.39  Cooper               : 0.00
% 2.58/1.39  Total                : 0.62
% 2.58/1.39  Index Insertion      : 0.00
% 2.58/1.39  Index Deletion       : 0.00
% 2.58/1.39  Index Matching       : 0.00
% 2.58/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
