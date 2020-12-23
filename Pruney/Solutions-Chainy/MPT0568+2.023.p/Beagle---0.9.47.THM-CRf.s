%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:23 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   45 (  69 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :   58 ( 118 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_52,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_54,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_85,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_10,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_30,plain,(
    ! [A_24] :
      ( v1_relat_1(A_24)
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_30])).

tff(c_198,plain,(
    ! [A_60,B_61,C_62] :
      ( r2_hidden(k4_tarski(A_60,'#skF_4'(A_60,B_61,C_62)),C_62)
      | ~ r2_hidden(A_60,k10_relat_1(C_62,B_61))
      | ~ v1_relat_1(C_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden('#skF_4'(A_17,B_18,C_19),B_18)
      | ~ r2_hidden(A_17,k10_relat_1(C_19,B_18))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_106,plain,(
    ! [A_45,B_46,C_47] :
      ( r2_hidden('#skF_4'(A_45,B_46,C_47),B_46)
      | ~ r2_hidden(A_45,k10_relat_1(C_47,B_46))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_39,plain,(
    ! [A_32,B_33,C_34] :
      ( ~ r1_xboole_0(A_32,B_33)
      | ~ r2_hidden(C_34,B_33)
      | ~ r2_hidden(C_34,A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_42,plain,(
    ! [C_34,A_8] :
      ( ~ r2_hidden(C_34,k1_xboole_0)
      | ~ r2_hidden(C_34,A_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_39])).

tff(c_117,plain,(
    ! [A_50,C_51,A_52] :
      ( ~ r2_hidden('#skF_4'(A_50,k1_xboole_0,C_51),A_52)
      | ~ r2_hidden(A_50,k10_relat_1(C_51,k1_xboole_0))
      | ~ v1_relat_1(C_51) ) ),
    inference(resolution,[status(thm)],[c_106,c_42])).

tff(c_129,plain,(
    ! [A_56,C_57] :
      ( ~ r2_hidden(A_56,k10_relat_1(C_57,k1_xboole_0))
      | ~ v1_relat_1(C_57) ) ),
    inference(resolution,[status(thm)],[c_22,c_117])).

tff(c_155,plain,(
    ! [C_58] :
      ( ~ v1_relat_1(C_58)
      | k10_relat_1(C_58,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_129])).

tff(c_159,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_155])).

tff(c_122,plain,(
    ! [A_17,C_19] :
      ( ~ r2_hidden(A_17,k10_relat_1(C_19,k1_xboole_0))
      | ~ v1_relat_1(C_19) ) ),
    inference(resolution,[status(thm)],[c_22,c_117])).

tff(c_163,plain,(
    ! [A_17] :
      ( ~ r2_hidden(A_17,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_122])).

tff(c_167,plain,(
    ! [A_17] : ~ r2_hidden(A_17,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_163])).

tff(c_202,plain,(
    ! [A_60,B_61] :
      ( ~ r2_hidden(A_60,k10_relat_1(k1_xboole_0,B_61))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_198,c_167])).

tff(c_216,plain,(
    ! [A_63,B_64] : ~ r2_hidden(A_63,k10_relat_1(k1_xboole_0,B_64)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_202])).

tff(c_248,plain,(
    ! [B_64] : k10_relat_1(k1_xboole_0,B_64) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_216])).

tff(c_28,plain,(
    k10_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:31:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.17  
% 1.91/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.17  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1
% 1.91/1.17  
% 1.91/1.17  %Foreground sorts:
% 1.91/1.17  
% 1.91/1.17  
% 1.91/1.17  %Background operators:
% 1.91/1.17  
% 1.91/1.17  
% 1.91/1.17  %Foreground operators:
% 1.91/1.17  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.91/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.91/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.91/1.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.91/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.91/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.17  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.91/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.17  
% 1.91/1.18  tff(f_52, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.91/1.18  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.91/1.18  tff(f_71, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.91/1.18  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.91/1.18  tff(f_54, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.91/1.18  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.91/1.18  tff(f_85, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.91/1.18  tff(c_10, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.91/1.18  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.91/1.18  tff(c_30, plain, (![A_24]: (v1_relat_1(A_24) | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.91/1.18  tff(c_34, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_30])).
% 1.91/1.18  tff(c_198, plain, (![A_60, B_61, C_62]: (r2_hidden(k4_tarski(A_60, '#skF_4'(A_60, B_61, C_62)), C_62) | ~r2_hidden(A_60, k10_relat_1(C_62, B_61)) | ~v1_relat_1(C_62))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.91/1.18  tff(c_22, plain, (![A_17, B_18, C_19]: (r2_hidden('#skF_4'(A_17, B_18, C_19), B_18) | ~r2_hidden(A_17, k10_relat_1(C_19, B_18)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.91/1.18  tff(c_106, plain, (![A_45, B_46, C_47]: (r2_hidden('#skF_4'(A_45, B_46, C_47), B_46) | ~r2_hidden(A_45, k10_relat_1(C_47, B_46)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.91/1.18  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.91/1.18  tff(c_39, plain, (![A_32, B_33, C_34]: (~r1_xboole_0(A_32, B_33) | ~r2_hidden(C_34, B_33) | ~r2_hidden(C_34, A_32))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.91/1.18  tff(c_42, plain, (![C_34, A_8]: (~r2_hidden(C_34, k1_xboole_0) | ~r2_hidden(C_34, A_8))), inference(resolution, [status(thm)], [c_12, c_39])).
% 1.91/1.18  tff(c_117, plain, (![A_50, C_51, A_52]: (~r2_hidden('#skF_4'(A_50, k1_xboole_0, C_51), A_52) | ~r2_hidden(A_50, k10_relat_1(C_51, k1_xboole_0)) | ~v1_relat_1(C_51))), inference(resolution, [status(thm)], [c_106, c_42])).
% 1.91/1.18  tff(c_129, plain, (![A_56, C_57]: (~r2_hidden(A_56, k10_relat_1(C_57, k1_xboole_0)) | ~v1_relat_1(C_57))), inference(resolution, [status(thm)], [c_22, c_117])).
% 1.91/1.18  tff(c_155, plain, (![C_58]: (~v1_relat_1(C_58) | k10_relat_1(C_58, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_129])).
% 1.91/1.18  tff(c_159, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_155])).
% 1.91/1.18  tff(c_122, plain, (![A_17, C_19]: (~r2_hidden(A_17, k10_relat_1(C_19, k1_xboole_0)) | ~v1_relat_1(C_19))), inference(resolution, [status(thm)], [c_22, c_117])).
% 1.91/1.18  tff(c_163, plain, (![A_17]: (~r2_hidden(A_17, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_159, c_122])).
% 1.91/1.18  tff(c_167, plain, (![A_17]: (~r2_hidden(A_17, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_163])).
% 1.91/1.18  tff(c_202, plain, (![A_60, B_61]: (~r2_hidden(A_60, k10_relat_1(k1_xboole_0, B_61)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_198, c_167])).
% 1.91/1.18  tff(c_216, plain, (![A_63, B_64]: (~r2_hidden(A_63, k10_relat_1(k1_xboole_0, B_64)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_202])).
% 1.91/1.18  tff(c_248, plain, (![B_64]: (k10_relat_1(k1_xboole_0, B_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_216])).
% 1.91/1.18  tff(c_28, plain, (k10_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.91/1.18  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_248, c_28])).
% 1.91/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.18  
% 1.91/1.18  Inference rules
% 1.91/1.18  ----------------------
% 1.91/1.18  #Ref     : 0
% 1.91/1.18  #Sup     : 42
% 1.91/1.18  #Fact    : 0
% 1.91/1.18  #Define  : 0
% 1.91/1.18  #Split   : 0
% 1.91/1.18  #Chain   : 0
% 1.91/1.18  #Close   : 0
% 1.91/1.18  
% 1.91/1.18  Ordering : KBO
% 1.91/1.18  
% 1.91/1.18  Simplification rules
% 1.91/1.18  ----------------------
% 1.91/1.18  #Subsume      : 12
% 1.91/1.18  #Demod        : 10
% 1.91/1.18  #Tautology    : 10
% 1.91/1.18  #SimpNegUnit  : 0
% 1.91/1.18  #BackRed      : 2
% 1.91/1.18  
% 1.91/1.18  #Partial instantiations: 0
% 1.91/1.18  #Strategies tried      : 1
% 1.91/1.18  
% 1.91/1.18  Timing (in seconds)
% 1.91/1.18  ----------------------
% 1.91/1.18  Preprocessing        : 0.27
% 1.91/1.18  Parsing              : 0.15
% 1.91/1.18  CNF conversion       : 0.02
% 1.91/1.19  Main loop            : 0.17
% 1.91/1.19  Inferencing          : 0.08
% 1.91/1.19  Reduction            : 0.04
% 1.91/1.19  Demodulation         : 0.03
% 1.91/1.19  BG Simplification    : 0.01
% 1.91/1.19  Subsumption          : 0.03
% 1.91/1.19  Abstraction          : 0.01
% 1.91/1.19  MUC search           : 0.00
% 1.91/1.19  Cooper               : 0.00
% 1.91/1.19  Total                : 0.46
% 1.91/1.19  Index Insertion      : 0.00
% 1.91/1.19  Index Deletion       : 0.00
% 1.91/1.19  Index Matching       : 0.00
% 1.91/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
