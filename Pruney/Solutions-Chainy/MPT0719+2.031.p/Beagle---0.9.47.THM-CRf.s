%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:47 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   47 (  55 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   69 (  83 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_2'(A_44),A_44)
      | v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0(A_45)
      | v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_52,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_37,plain,(
    ! [A_41] :
      ( v1_funct_1(A_41)
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_41,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_37])).

tff(c_30,plain,(
    ! [A_31,B_37] :
      ( r2_hidden('#skF_6'(A_31,B_37),k1_relat_1(B_37))
      | v5_funct_1(B_37,A_31)
      | ~ v1_funct_1(B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_29] :
      ( k10_relat_1(A_29,k2_relat_1(A_29)) = k1_relat_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_168,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden(k4_tarski(A_78,'#skF_5'(A_78,B_79,C_80)),C_80)
      | ~ r2_hidden(A_78,k10_relat_1(C_80,B_79))
      | ~ v1_relat_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_183,plain,(
    ! [C_81,A_82,B_83] :
      ( ~ v1_xboole_0(C_81)
      | ~ r2_hidden(A_82,k10_relat_1(C_81,B_83))
      | ~ v1_relat_1(C_81) ) ),
    inference(resolution,[status(thm)],[c_168,c_2])).

tff(c_272,plain,(
    ! [A_106,A_107] :
      ( ~ v1_xboole_0(A_106)
      | ~ r2_hidden(A_107,k1_relat_1(A_106))
      | ~ v1_relat_1(A_106)
      | ~ v1_relat_1(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_183])).

tff(c_504,plain,(
    ! [B_164,A_165] :
      ( ~ v1_xboole_0(B_164)
      | v5_funct_1(B_164,A_165)
      | ~ v1_funct_1(B_164)
      | ~ v1_relat_1(B_164)
      | ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165) ) ),
    inference(resolution,[status(thm)],[c_30,c_272])).

tff(c_32,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_507,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_504,c_32])).

tff(c_511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_52,c_41,c_6,c_507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.09  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.28  % Computer   : n017.cluster.edu
% 0.09/0.28  % Model      : x86_64 x86_64
% 0.09/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.28  % Memory     : 8042.1875MB
% 0.09/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.28  % CPULimit   : 60
% 0.09/0.28  % DateTime   : Tue Dec  1 10:23:46 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.29  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.31  
% 2.55/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.31  %$ v5_funct_1 > r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_4
% 2.55/1.31  
% 2.55/1.31  %Foreground sorts:
% 2.55/1.31  
% 2.55/1.31  
% 2.55/1.31  %Background operators:
% 2.55/1.31  
% 2.55/1.31  
% 2.55/1.31  %Foreground operators:
% 2.55/1.31  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.55/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.55/1.31  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.55/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.55/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.55/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.55/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.55/1.31  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.55/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.55/1.31  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.55/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.55/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.55/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.55/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.55/1.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.55/1.31  
% 2.55/1.32  tff(f_84, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_funct_1)).
% 2.55/1.32  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.55/1.32  tff(f_42, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.55/1.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.55/1.32  tff(f_61, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.55/1.32  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.55/1.32  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.55/1.32  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.55/1.32  tff(c_36, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.55/1.32  tff(c_34, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.55/1.32  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.32  tff(c_43, plain, (![A_44]: (r2_hidden('#skF_2'(A_44), A_44) | v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.55/1.32  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.55/1.32  tff(c_48, plain, (![A_45]: (~v1_xboole_0(A_45) | v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_43, c_2])).
% 2.55/1.32  tff(c_52, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_48])).
% 2.55/1.32  tff(c_37, plain, (![A_41]: (v1_funct_1(A_41) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.55/1.32  tff(c_41, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_37])).
% 2.55/1.32  tff(c_30, plain, (![A_31, B_37]: (r2_hidden('#skF_6'(A_31, B_37), k1_relat_1(B_37)) | v5_funct_1(B_37, A_31) | ~v1_funct_1(B_37) | ~v1_relat_1(B_37) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.55/1.32  tff(c_22, plain, (![A_29]: (k10_relat_1(A_29, k2_relat_1(A_29))=k1_relat_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.55/1.32  tff(c_168, plain, (![A_78, B_79, C_80]: (r2_hidden(k4_tarski(A_78, '#skF_5'(A_78, B_79, C_80)), C_80) | ~r2_hidden(A_78, k10_relat_1(C_80, B_79)) | ~v1_relat_1(C_80))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.55/1.32  tff(c_183, plain, (![C_81, A_82, B_83]: (~v1_xboole_0(C_81) | ~r2_hidden(A_82, k10_relat_1(C_81, B_83)) | ~v1_relat_1(C_81))), inference(resolution, [status(thm)], [c_168, c_2])).
% 2.55/1.32  tff(c_272, plain, (![A_106, A_107]: (~v1_xboole_0(A_106) | ~r2_hidden(A_107, k1_relat_1(A_106)) | ~v1_relat_1(A_106) | ~v1_relat_1(A_106))), inference(superposition, [status(thm), theory('equality')], [c_22, c_183])).
% 2.55/1.32  tff(c_504, plain, (![B_164, A_165]: (~v1_xboole_0(B_164) | v5_funct_1(B_164, A_165) | ~v1_funct_1(B_164) | ~v1_relat_1(B_164) | ~v1_funct_1(A_165) | ~v1_relat_1(A_165))), inference(resolution, [status(thm)], [c_30, c_272])).
% 2.55/1.32  tff(c_32, plain, (~v5_funct_1(k1_xboole_0, '#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.55/1.32  tff(c_507, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_504, c_32])).
% 2.55/1.32  tff(c_511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_52, c_41, c_6, c_507])).
% 2.55/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.32  
% 2.55/1.32  Inference rules
% 2.55/1.32  ----------------------
% 2.55/1.32  #Ref     : 1
% 2.55/1.32  #Sup     : 101
% 2.55/1.32  #Fact    : 0
% 2.55/1.32  #Define  : 0
% 2.55/1.32  #Split   : 0
% 2.55/1.32  #Chain   : 0
% 2.55/1.32  #Close   : 0
% 2.55/1.32  
% 2.55/1.32  Ordering : KBO
% 2.55/1.32  
% 2.55/1.32  Simplification rules
% 2.55/1.32  ----------------------
% 2.55/1.32  #Subsume      : 19
% 2.55/1.32  #Demod        : 5
% 2.55/1.32  #Tautology    : 7
% 2.55/1.32  #SimpNegUnit  : 0
% 2.55/1.32  #BackRed      : 0
% 2.55/1.32  
% 2.55/1.32  #Partial instantiations: 0
% 2.55/1.32  #Strategies tried      : 1
% 2.55/1.32  
% 2.55/1.32  Timing (in seconds)
% 2.55/1.32  ----------------------
% 2.55/1.33  Preprocessing        : 0.28
% 2.55/1.33  Parsing              : 0.16
% 2.55/1.33  CNF conversion       : 0.02
% 2.55/1.33  Main loop            : 0.34
% 2.55/1.33  Inferencing          : 0.14
% 2.55/1.33  Reduction            : 0.07
% 2.55/1.33  Demodulation         : 0.05
% 2.55/1.33  BG Simplification    : 0.02
% 2.55/1.33  Subsumption          : 0.09
% 2.55/1.33  Abstraction          : 0.01
% 2.55/1.33  MUC search           : 0.00
% 2.55/1.33  Cooper               : 0.00
% 2.55/1.33  Total                : 0.65
% 2.55/1.33  Index Insertion      : 0.00
% 2.55/1.33  Index Deletion       : 0.00
% 2.55/1.33  Index Matching       : 0.00
% 2.55/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
