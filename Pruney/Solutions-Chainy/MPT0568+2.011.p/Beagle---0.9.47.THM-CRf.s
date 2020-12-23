%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:22 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   37 (  43 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  48 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_62,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_26] :
      ( v1_xboole_0(A_26)
      | r2_hidden('#skF_1'(A_26),A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    ! [A_23,B_24] : ~ r2_hidden(A_23,k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_55,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_52])).

tff(c_68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_60,c_55])).

tff(c_16,plain,(
    ! [A_10] :
      ( v1_relat_1(A_10)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_68,c_16])).

tff(c_135,plain,(
    ! [A_40,B_41,C_42] :
      ( r2_hidden(k4_tarski(A_40,'#skF_2'(A_40,B_41,C_42)),C_42)
      | ~ r2_hidden(A_40,k10_relat_1(C_42,B_41))
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_143,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden(A_40,k10_relat_1(k1_xboole_0,B_41))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_135,c_55])).

tff(c_171,plain,(
    ! [A_43,B_44] : ~ r2_hidden(A_43,k10_relat_1(k1_xboole_0,B_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_143])).

tff(c_189,plain,(
    ! [B_45] : v1_xboole_0(k10_relat_1(k1_xboole_0,B_45)) ),
    inference(resolution,[status(thm)],[c_4,c_171])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_199,plain,(
    ! [B_45] : k10_relat_1(k1_xboole_0,B_45) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_189,c_6])).

tff(c_26,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:36:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.15  
% 1.68/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.15  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.68/1.15  
% 1.68/1.15  %Foreground sorts:
% 1.68/1.15  
% 1.68/1.15  
% 1.68/1.15  %Background operators:
% 1.68/1.15  
% 1.68/1.15  
% 1.68/1.15  %Foreground operators:
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.68/1.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.68/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.68/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.68/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.68/1.15  
% 1.68/1.16  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.68/1.16  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.68/1.16  tff(f_44, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.68/1.16  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.68/1.16  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.68/1.16  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.68/1.16  tff(f_62, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.68/1.16  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.16  tff(c_60, plain, (![A_26]: (v1_xboole_0(A_26) | r2_hidden('#skF_1'(A_26), A_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.16  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.68/1.16  tff(c_52, plain, (![A_23, B_24]: (~r2_hidden(A_23, k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.68/1.16  tff(c_55, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_52])).
% 1.68/1.16  tff(c_68, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_60, c_55])).
% 1.68/1.16  tff(c_16, plain, (![A_10]: (v1_relat_1(A_10) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.68/1.16  tff(c_76, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_16])).
% 1.68/1.16  tff(c_135, plain, (![A_40, B_41, C_42]: (r2_hidden(k4_tarski(A_40, '#skF_2'(A_40, B_41, C_42)), C_42) | ~r2_hidden(A_40, k10_relat_1(C_42, B_41)) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.68/1.16  tff(c_143, plain, (![A_40, B_41]: (~r2_hidden(A_40, k10_relat_1(k1_xboole_0, B_41)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_135, c_55])).
% 1.68/1.16  tff(c_171, plain, (![A_43, B_44]: (~r2_hidden(A_43, k10_relat_1(k1_xboole_0, B_44)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_143])).
% 1.68/1.16  tff(c_189, plain, (![B_45]: (v1_xboole_0(k10_relat_1(k1_xboole_0, B_45)))), inference(resolution, [status(thm)], [c_4, c_171])).
% 1.68/1.16  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.68/1.16  tff(c_199, plain, (![B_45]: (k10_relat_1(k1_xboole_0, B_45)=k1_xboole_0)), inference(resolution, [status(thm)], [c_189, c_6])).
% 1.68/1.16  tff(c_26, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.16  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_26])).
% 1.68/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.16  
% 1.68/1.16  Inference rules
% 1.68/1.16  ----------------------
% 1.68/1.16  #Ref     : 0
% 1.68/1.16  #Sup     : 40
% 1.68/1.16  #Fact    : 0
% 1.68/1.16  #Define  : 0
% 1.68/1.16  #Split   : 0
% 1.68/1.16  #Chain   : 0
% 1.68/1.16  #Close   : 0
% 1.68/1.16  
% 1.68/1.16  Ordering : KBO
% 1.68/1.16  
% 1.68/1.16  Simplification rules
% 1.68/1.16  ----------------------
% 1.68/1.16  #Subsume      : 4
% 1.68/1.16  #Demod        : 15
% 1.68/1.16  #Tautology    : 19
% 1.68/1.16  #SimpNegUnit  : 0
% 1.68/1.16  #BackRed      : 4
% 1.68/1.16  
% 1.68/1.16  #Partial instantiations: 0
% 1.68/1.16  #Strategies tried      : 1
% 1.68/1.16  
% 1.68/1.16  Timing (in seconds)
% 1.68/1.16  ----------------------
% 1.68/1.16  Preprocessing        : 0.26
% 1.68/1.16  Parsing              : 0.14
% 1.68/1.16  CNF conversion       : 0.02
% 1.68/1.16  Main loop            : 0.15
% 1.68/1.16  Inferencing          : 0.06
% 1.68/1.16  Reduction            : 0.04
% 1.68/1.16  Demodulation         : 0.03
% 1.68/1.16  BG Simplification    : 0.01
% 1.68/1.16  Subsumption          : 0.03
% 1.68/1.16  Abstraction          : 0.01
% 1.68/1.16  MUC search           : 0.00
% 1.68/1.17  Cooper               : 0.00
% 1.68/1.17  Total                : 0.43
% 1.68/1.17  Index Insertion      : 0.00
% 1.68/1.17  Index Deletion       : 0.00
% 1.68/1.17  Index Matching       : 0.00
% 1.68/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
