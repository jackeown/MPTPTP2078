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
% DateTime   : Thu Dec  3 10:00:42 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   48 (  68 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  86 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_43,axiom,(
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

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_24,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_3'(A_16),A_16)
      | v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_124,plain,(
    ! [A_51,B_52,C_53] :
      ( ~ r1_xboole_0(A_51,B_52)
      | ~ r2_hidden(C_53,k3_xboole_0(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_138,plain,(
    ! [A_11,C_53] :
      ( ~ r1_xboole_0(A_11,k1_xboole_0)
      | ~ r2_hidden(C_53,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_124])).

tff(c_143,plain,(
    ! [C_54] : ~ r2_hidden(C_54,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_138])).

tff(c_153,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_143])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_152,plain,(
    ! [B_2] : r1_xboole_0(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_143])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_294,plain,(
    ! [B_78,A_79] :
      ( k7_relat_1(B_78,A_79) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_78),A_79)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_305,plain,(
    ! [A_79] :
      ( k7_relat_1(k1_xboole_0,A_79) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_79)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_294])).

tff(c_310,plain,(
    ! [A_80] : k7_relat_1(k1_xboole_0,A_80) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_152,c_305])).

tff(c_26,plain,(
    ! [B_35,A_34] :
      ( k2_relat_1(k7_relat_1(B_35,A_34)) = k9_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_315,plain,(
    ! [A_80] :
      ( k9_relat_1(k1_xboole_0,A_80) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_26])).

tff(c_320,plain,(
    ! [A_80] : k9_relat_1(k1_xboole_0,A_80) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_28,c_315])).

tff(c_36,plain,(
    k9_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:20:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.34  
% 2.13/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.35  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.13/1.35  
% 2.13/1.35  %Foreground sorts:
% 2.13/1.35  
% 2.13/1.35  
% 2.13/1.35  %Background operators:
% 2.13/1.35  
% 2.13/1.35  
% 2.13/1.35  %Foreground operators:
% 2.13/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.13/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.13/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.13/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.13/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.13/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.35  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.13/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.13/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.13/1.35  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.13/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.13/1.35  
% 2.13/1.36  tff(f_75, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.13/1.36  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.13/1.36  tff(f_59, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.13/1.36  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.13/1.36  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.13/1.36  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.13/1.36  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.13/1.36  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.13/1.36  tff(f_91, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.13/1.36  tff(c_24, plain, (![A_16]: (r2_hidden('#skF_3'(A_16), A_16) | v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.13/1.36  tff(c_18, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.13/1.36  tff(c_12, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.13/1.36  tff(c_124, plain, (![A_51, B_52, C_53]: (~r1_xboole_0(A_51, B_52) | ~r2_hidden(C_53, k3_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.13/1.36  tff(c_138, plain, (![A_11, C_53]: (~r1_xboole_0(A_11, k1_xboole_0) | ~r2_hidden(C_53, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_124])).
% 2.13/1.36  tff(c_143, plain, (![C_54]: (~r2_hidden(C_54, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_138])).
% 2.13/1.36  tff(c_153, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_143])).
% 2.13/1.36  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.13/1.36  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.13/1.36  tff(c_152, plain, (![B_2]: (r1_xboole_0(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_143])).
% 2.13/1.36  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.13/1.36  tff(c_294, plain, (![B_78, A_79]: (k7_relat_1(B_78, A_79)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_78), A_79) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.13/1.36  tff(c_305, plain, (![A_79]: (k7_relat_1(k1_xboole_0, A_79)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_79) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_294])).
% 2.13/1.36  tff(c_310, plain, (![A_80]: (k7_relat_1(k1_xboole_0, A_80)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_152, c_305])).
% 2.13/1.36  tff(c_26, plain, (![B_35, A_34]: (k2_relat_1(k7_relat_1(B_35, A_34))=k9_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.13/1.36  tff(c_315, plain, (![A_80]: (k9_relat_1(k1_xboole_0, A_80)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_310, c_26])).
% 2.13/1.36  tff(c_320, plain, (![A_80]: (k9_relat_1(k1_xboole_0, A_80)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_153, c_28, c_315])).
% 2.13/1.36  tff(c_36, plain, (k9_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.13/1.36  tff(c_324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_320, c_36])).
% 2.13/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.36  
% 2.13/1.36  Inference rules
% 2.13/1.36  ----------------------
% 2.13/1.36  #Ref     : 0
% 2.13/1.36  #Sup     : 64
% 2.13/1.36  #Fact    : 0
% 2.13/1.36  #Define  : 0
% 2.13/1.36  #Split   : 0
% 2.13/1.36  #Chain   : 0
% 2.13/1.36  #Close   : 0
% 2.13/1.36  
% 2.13/1.36  Ordering : KBO
% 2.13/1.36  
% 2.13/1.36  Simplification rules
% 2.13/1.36  ----------------------
% 2.13/1.36  #Subsume      : 14
% 2.13/1.36  #Demod        : 21
% 2.13/1.36  #Tautology    : 32
% 2.13/1.36  #SimpNegUnit  : 0
% 2.13/1.36  #BackRed      : 1
% 2.13/1.36  
% 2.13/1.36  #Partial instantiations: 0
% 2.13/1.36  #Strategies tried      : 1
% 2.13/1.36  
% 2.13/1.36  Timing (in seconds)
% 2.13/1.36  ----------------------
% 2.13/1.36  Preprocessing        : 0.34
% 2.13/1.36  Parsing              : 0.18
% 2.13/1.36  CNF conversion       : 0.03
% 2.13/1.36  Main loop            : 0.19
% 2.13/1.36  Inferencing          : 0.08
% 2.13/1.36  Reduction            : 0.05
% 2.13/1.36  Demodulation         : 0.04
% 2.13/1.36  BG Simplification    : 0.01
% 2.13/1.36  Subsumption          : 0.03
% 2.13/1.36  Abstraction          : 0.01
% 2.13/1.36  MUC search           : 0.00
% 2.13/1.36  Cooper               : 0.00
% 2.13/1.36  Total                : 0.55
% 2.13/1.36  Index Insertion      : 0.00
% 2.13/1.36  Index Deletion       : 0.00
% 2.13/1.36  Index Matching       : 0.00
% 2.13/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
