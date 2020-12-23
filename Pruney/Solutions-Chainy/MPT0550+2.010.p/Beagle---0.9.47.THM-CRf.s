%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:53 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   44 (  47 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   66 (  78 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_24,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_141,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(k1_relat_1(B_32),A_33)
      | k9_relat_1(B_32,A_33) != k1_xboole_0
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_76,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,k3_xboole_0(A_22,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_87,plain,(
    ! [A_22,B_23] :
      ( ~ r1_xboole_0(A_22,B_23)
      | k3_xboole_0(A_22,B_23) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_456,plain,(
    ! [B_70,A_71] :
      ( k3_xboole_0(k1_relat_1(B_70),A_71) = k1_xboole_0
      | k9_relat_1(B_70,A_71) != k1_xboole_0
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_141,c_87])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_279,plain,(
    ! [A_45,B_46,C_47] :
      ( ~ r1_xboole_0(A_45,k3_xboole_0(B_46,C_47))
      | ~ r1_tarski(A_45,C_47)
      | r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_296,plain,(
    ! [A_45,B_2,A_1] :
      ( ~ r1_xboole_0(A_45,k3_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_45,B_2)
      | r1_xboole_0(A_45,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_279])).

tff(c_462,plain,(
    ! [A_45,B_70,A_71] :
      ( ~ r1_xboole_0(A_45,k1_xboole_0)
      | ~ r1_tarski(A_45,k1_relat_1(B_70))
      | r1_xboole_0(A_45,A_71)
      | k9_relat_1(B_70,A_71) != k1_xboole_0
      | ~ v1_relat_1(B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_296])).

tff(c_639,plain,(
    ! [A_88,B_89,A_90] :
      ( ~ r1_tarski(A_88,k1_relat_1(B_89))
      | r1_xboole_0(A_88,A_90)
      | k9_relat_1(B_89,A_90) != k1_xboole_0
      | ~ v1_relat_1(B_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_462])).

tff(c_641,plain,(
    ! [A_90] :
      ( r1_xboole_0('#skF_3',A_90)
      | k9_relat_1('#skF_4',A_90) != k1_xboole_0
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_639])).

tff(c_645,plain,(
    ! [A_91] :
      ( r1_xboole_0('#skF_3',A_91)
      | k9_relat_1('#skF_4',A_91) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_641])).

tff(c_14,plain,(
    ! [A_11] :
      ( ~ r1_xboole_0(A_11,A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_665,plain,
    ( k1_xboole_0 = '#skF_3'
    | k9_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_645,c_14])).

tff(c_673,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_665])).

tff(c_675,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_673])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.58  
% 2.59/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.59/1.58  
% 2.59/1.58  %Foreground sorts:
% 2.59/1.58  
% 2.59/1.58  
% 2.59/1.58  %Background operators:
% 2.59/1.58  
% 2.59/1.58  
% 2.59/1.58  %Foreground operators:
% 2.59/1.58  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.59/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.59/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.59/1.58  tff('#skF_3', type, '#skF_3': $i).
% 2.59/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.59/1.58  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.59/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.59/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.59/1.58  
% 2.59/1.59  tff(f_88, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 2.59/1.59  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.59/1.59  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.59/1.59  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.59/1.59  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.59/1.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.59/1.59  tff(f_71, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 2.59/1.59  tff(f_63, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.59/1.59  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.59/1.59  tff(c_22, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.59/1.59  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.59/1.59  tff(c_24, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.59/1.59  tff(c_10, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.59/1.59  tff(c_141, plain, (![B_32, A_33]: (r1_xboole_0(k1_relat_1(B_32), A_33) | k9_relat_1(B_32, A_33)!=k1_xboole_0 | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.59/1.59  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.59/1.59  tff(c_76, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, k3_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.59/1.59  tff(c_87, plain, (![A_22, B_23]: (~r1_xboole_0(A_22, B_23) | k3_xboole_0(A_22, B_23)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_76])).
% 2.59/1.59  tff(c_456, plain, (![B_70, A_71]: (k3_xboole_0(k1_relat_1(B_70), A_71)=k1_xboole_0 | k9_relat_1(B_70, A_71)!=k1_xboole_0 | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_141, c_87])).
% 2.59/1.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.59/1.59  tff(c_279, plain, (![A_45, B_46, C_47]: (~r1_xboole_0(A_45, k3_xboole_0(B_46, C_47)) | ~r1_tarski(A_45, C_47) | r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.59/1.59  tff(c_296, plain, (![A_45, B_2, A_1]: (~r1_xboole_0(A_45, k3_xboole_0(B_2, A_1)) | ~r1_tarski(A_45, B_2) | r1_xboole_0(A_45, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_279])).
% 2.59/1.59  tff(c_462, plain, (![A_45, B_70, A_71]: (~r1_xboole_0(A_45, k1_xboole_0) | ~r1_tarski(A_45, k1_relat_1(B_70)) | r1_xboole_0(A_45, A_71) | k9_relat_1(B_70, A_71)!=k1_xboole_0 | ~v1_relat_1(B_70))), inference(superposition, [status(thm), theory('equality')], [c_456, c_296])).
% 2.59/1.59  tff(c_639, plain, (![A_88, B_89, A_90]: (~r1_tarski(A_88, k1_relat_1(B_89)) | r1_xboole_0(A_88, A_90) | k9_relat_1(B_89, A_90)!=k1_xboole_0 | ~v1_relat_1(B_89))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_462])).
% 2.59/1.59  tff(c_641, plain, (![A_90]: (r1_xboole_0('#skF_3', A_90) | k9_relat_1('#skF_4', A_90)!=k1_xboole_0 | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_639])).
% 2.59/1.59  tff(c_645, plain, (![A_91]: (r1_xboole_0('#skF_3', A_91) | k9_relat_1('#skF_4', A_91)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_641])).
% 2.59/1.59  tff(c_14, plain, (![A_11]: (~r1_xboole_0(A_11, A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.59/1.59  tff(c_665, plain, (k1_xboole_0='#skF_3' | k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_645, c_14])).
% 2.59/1.59  tff(c_673, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_665])).
% 2.59/1.59  tff(c_675, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_673])).
% 2.59/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.59  
% 2.59/1.59  Inference rules
% 2.59/1.59  ----------------------
% 2.59/1.59  #Ref     : 0
% 2.59/1.59  #Sup     : 145
% 2.59/1.59  #Fact    : 0
% 2.59/1.59  #Define  : 0
% 2.59/1.59  #Split   : 1
% 2.59/1.59  #Chain   : 0
% 2.59/1.59  #Close   : 0
% 2.59/1.59  
% 2.59/1.59  Ordering : KBO
% 2.59/1.59  
% 2.59/1.59  Simplification rules
% 2.59/1.59  ----------------------
% 2.59/1.59  #Subsume      : 46
% 2.59/1.59  #Demod        : 37
% 2.59/1.59  #Tautology    : 56
% 2.59/1.59  #SimpNegUnit  : 9
% 2.59/1.59  #BackRed      : 0
% 2.59/1.59  
% 2.59/1.59  #Partial instantiations: 0
% 2.59/1.59  #Strategies tried      : 1
% 2.59/1.59  
% 2.59/1.59  Timing (in seconds)
% 2.59/1.59  ----------------------
% 2.59/1.60  Preprocessing        : 0.41
% 2.59/1.60  Parsing              : 0.18
% 2.59/1.60  CNF conversion       : 0.04
% 2.59/1.60  Main loop            : 0.36
% 2.59/1.60  Inferencing          : 0.13
% 2.59/1.60  Reduction            : 0.11
% 2.59/1.60  Demodulation         : 0.08
% 2.59/1.60  BG Simplification    : 0.03
% 2.59/1.60  Subsumption          : 0.08
% 2.59/1.60  Abstraction          : 0.01
% 2.59/1.60  MUC search           : 0.00
% 2.59/1.60  Cooper               : 0.00
% 2.59/1.60  Total                : 0.80
% 2.59/1.60  Index Insertion      : 0.00
% 2.59/1.60  Index Deletion       : 0.00
% 2.59/1.60  Index Matching       : 0.00
% 2.59/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
