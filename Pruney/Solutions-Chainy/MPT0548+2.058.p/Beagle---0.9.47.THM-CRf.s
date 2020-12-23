%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:42 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   46 (  51 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  55 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_79,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_67,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_47,axiom,(
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

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_63,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_78,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_30,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_48,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_46])).

tff(c_56,plain,(
    ! [A_22] :
      ( k9_relat_1(A_22,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_63,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_56])).

tff(c_109,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_1'(A_34,B_35),A_34)
      | r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_90,plain,(
    ! [A_28,B_29,C_30] :
      ( ~ r1_xboole_0(A_28,B_29)
      | ~ r2_hidden(C_30,k3_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_93,plain,(
    ! [A_13,C_30] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_30,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_90])).

tff(c_95,plain,(
    ! [C_30] : ~ r2_hidden(C_30,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_93])).

tff(c_120,plain,(
    ! [B_36] : r1_xboole_0(k1_xboole_0,B_36) ),
    inference(resolution,[status(thm)],[c_109,c_95])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_124,plain,(
    ! [B_36] : k3_xboole_0(k1_xboole_0,B_36) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_120,c_2])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_322,plain,(
    ! [B_55,A_56] :
      ( k9_relat_1(B_55,k3_xboole_0(k1_relat_1(B_55),A_56)) = k9_relat_1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_339,plain,(
    ! [A_56] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_56)) = k9_relat_1(k1_xboole_0,A_56)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_322])).

tff(c_344,plain,(
    ! [A_56] : k9_relat_1(k1_xboole_0,A_56) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_63,c_124,c_339])).

tff(c_32,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_348,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.53  
% 2.37/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.53  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.37/1.53  
% 2.37/1.53  %Foreground sorts:
% 2.37/1.53  
% 2.37/1.53  
% 2.37/1.53  %Background operators:
% 2.37/1.53  
% 2.37/1.53  
% 2.37/1.53  %Foreground operators:
% 2.37/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.37/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.37/1.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.37/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.37/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.37/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.37/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.37/1.53  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.53  
% 2.51/1.55  tff(f_79, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.51/1.55  tff(f_67, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.51/1.55  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 2.51/1.55  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.51/1.55  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.51/1.55  tff(f_63, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.51/1.55  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.51/1.55  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.51/1.55  tff(f_78, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.51/1.55  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 2.51/1.55  tff(f_82, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.51/1.55  tff(c_30, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.51/1.55  tff(c_46, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.51/1.55  tff(c_48, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_46])).
% 2.51/1.55  tff(c_56, plain, (![A_22]: (k9_relat_1(A_22, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.51/1.55  tff(c_63, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_56])).
% 2.51/1.55  tff(c_109, plain, (![A_34, B_35]: (r2_hidden('#skF_1'(A_34, B_35), A_34) | r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.51/1.55  tff(c_18, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.51/1.55  tff(c_16, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.51/1.55  tff(c_90, plain, (![A_28, B_29, C_30]: (~r1_xboole_0(A_28, B_29) | ~r2_hidden(C_30, k3_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.51/1.55  tff(c_93, plain, (![A_13, C_30]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_30, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_90])).
% 2.51/1.55  tff(c_95, plain, (![C_30]: (~r2_hidden(C_30, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_93])).
% 2.51/1.55  tff(c_120, plain, (![B_36]: (r1_xboole_0(k1_xboole_0, B_36))), inference(resolution, [status(thm)], [c_109, c_95])).
% 2.51/1.55  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.51/1.55  tff(c_124, plain, (![B_36]: (k3_xboole_0(k1_xboole_0, B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_120, c_2])).
% 2.51/1.55  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.51/1.55  tff(c_322, plain, (![B_55, A_56]: (k9_relat_1(B_55, k3_xboole_0(k1_relat_1(B_55), A_56))=k9_relat_1(B_55, A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.51/1.55  tff(c_339, plain, (![A_56]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_56))=k9_relat_1(k1_xboole_0, A_56) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_322])).
% 2.51/1.55  tff(c_344, plain, (![A_56]: (k9_relat_1(k1_xboole_0, A_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_63, c_124, c_339])).
% 2.51/1.55  tff(c_32, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.51/1.55  tff(c_348, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_344, c_32])).
% 2.51/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.55  
% 2.51/1.55  Inference rules
% 2.51/1.55  ----------------------
% 2.51/1.55  #Ref     : 0
% 2.51/1.55  #Sup     : 76
% 2.51/1.55  #Fact    : 0
% 2.51/1.55  #Define  : 0
% 2.51/1.55  #Split   : 0
% 2.51/1.55  #Chain   : 0
% 2.51/1.55  #Close   : 0
% 2.51/1.55  
% 2.51/1.55  Ordering : KBO
% 2.51/1.55  
% 2.51/1.55  Simplification rules
% 2.51/1.55  ----------------------
% 2.51/1.55  #Subsume      : 9
% 2.51/1.55  #Demod        : 38
% 2.51/1.55  #Tautology    : 55
% 2.51/1.55  #SimpNegUnit  : 4
% 2.51/1.55  #BackRed      : 1
% 2.51/1.55  
% 2.51/1.55  #Partial instantiations: 0
% 2.51/1.55  #Strategies tried      : 1
% 2.51/1.55  
% 2.51/1.55  Timing (in seconds)
% 2.51/1.55  ----------------------
% 2.51/1.56  Preprocessing        : 0.43
% 2.51/1.56  Parsing              : 0.24
% 2.51/1.56  CNF conversion       : 0.03
% 2.51/1.56  Main loop            : 0.31
% 2.51/1.56  Inferencing          : 0.13
% 2.51/1.56  Reduction            : 0.09
% 2.51/1.56  Demodulation         : 0.07
% 2.51/1.56  BG Simplification    : 0.02
% 2.51/1.56  Subsumption          : 0.06
% 2.51/1.56  Abstraction          : 0.01
% 2.51/1.56  MUC search           : 0.00
% 2.51/1.56  Cooper               : 0.00
% 2.51/1.56  Total                : 0.78
% 2.51/1.56  Index Insertion      : 0.00
% 2.51/1.56  Index Deletion       : 0.00
% 2.51/1.56  Index Matching       : 0.00
% 2.51/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
