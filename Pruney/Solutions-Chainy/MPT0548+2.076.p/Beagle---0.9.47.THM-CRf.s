%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:45 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   48 (  55 expanded)
%              Number of leaves         :   27 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  63 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_83,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_71,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_28,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_44])).

tff(c_55,plain,(
    ! [A_23] :
      ( k9_relat_1(A_23,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_62,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_55])).

tff(c_102,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_1'(A_31,B_32),A_31)
      | r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_78,plain,(
    ! [A_25,B_26,C_27] :
      ( ~ r1_xboole_0(A_25,B_26)
      | ~ r2_hidden(C_27,k3_xboole_0(A_25,B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_85,plain,(
    ! [A_13,C_27] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_27,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_78])).

tff(c_88,plain,(
    ! [C_27] : ~ r2_hidden(C_27,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_85])).

tff(c_113,plain,(
    ! [B_33] : r1_xboole_0(k1_xboole_0,B_33) ),
    inference(resolution,[status(thm)],[c_102,c_88])).

tff(c_12,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_86,plain,(
    ! [A_25,B_26] :
      ( ~ r1_xboole_0(A_25,B_26)
      | k3_xboole_0(A_25,B_26) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_78])).

tff(c_117,plain,(
    ! [B_33] : k3_xboole_0(k1_xboole_0,B_33) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_113,c_86])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_324,plain,(
    ! [B_54,A_55] :
      ( k9_relat_1(B_54,k3_xboole_0(k1_relat_1(B_54),A_55)) = k9_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_341,plain,(
    ! [A_55] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_55)) = k9_relat_1(k1_xboole_0,A_55)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_324])).

tff(c_346,plain,(
    ! [A_55] : k9_relat_1(k1_xboole_0,A_55) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_62,c_117,c_341])).

tff(c_30,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:11:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.21  
% 2.09/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.21  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.09/1.21  
% 2.09/1.21  %Foreground sorts:
% 2.09/1.21  
% 2.09/1.21  
% 2.09/1.21  %Background operators:
% 2.09/1.21  
% 2.09/1.21  
% 2.09/1.21  %Foreground operators:
% 2.09/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.09/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.21  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.09/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.09/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.09/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.21  
% 2.18/1.22  tff(f_83, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.18/1.22  tff(f_71, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.18/1.22  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_relat_1)).
% 2.18/1.22  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.18/1.22  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.18/1.22  tff(f_67, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.18/1.22  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.18/1.22  tff(f_65, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.18/1.22  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.18/1.22  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_relat_1)).
% 2.18/1.22  tff(f_86, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.18/1.22  tff(c_28, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.18/1.22  tff(c_44, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.18/1.22  tff(c_46, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_44])).
% 2.18/1.22  tff(c_55, plain, (![A_23]: (k9_relat_1(A_23, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.18/1.22  tff(c_62, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_55])).
% 2.18/1.22  tff(c_102, plain, (![A_31, B_32]: (r2_hidden('#skF_1'(A_31, B_32), A_31) | r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.18/1.22  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.18/1.22  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.18/1.22  tff(c_78, plain, (![A_25, B_26, C_27]: (~r1_xboole_0(A_25, B_26) | ~r2_hidden(C_27, k3_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.22  tff(c_85, plain, (![A_13, C_27]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_27, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_78])).
% 2.18/1.22  tff(c_88, plain, (![C_27]: (~r2_hidden(C_27, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_85])).
% 2.18/1.22  tff(c_113, plain, (![B_33]: (r1_xboole_0(k1_xboole_0, B_33))), inference(resolution, [status(thm)], [c_102, c_88])).
% 2.18/1.22  tff(c_12, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.18/1.22  tff(c_86, plain, (![A_25, B_26]: (~r1_xboole_0(A_25, B_26) | k3_xboole_0(A_25, B_26)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_78])).
% 2.18/1.22  tff(c_117, plain, (![B_33]: (k3_xboole_0(k1_xboole_0, B_33)=k1_xboole_0)), inference(resolution, [status(thm)], [c_113, c_86])).
% 2.18/1.22  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.18/1.22  tff(c_324, plain, (![B_54, A_55]: (k9_relat_1(B_54, k3_xboole_0(k1_relat_1(B_54), A_55))=k9_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.18/1.22  tff(c_341, plain, (![A_55]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_55))=k9_relat_1(k1_xboole_0, A_55) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_324])).
% 2.18/1.22  tff(c_346, plain, (![A_55]: (k9_relat_1(k1_xboole_0, A_55)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_62, c_117, c_341])).
% 2.18/1.22  tff(c_30, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.18/1.22  tff(c_350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_346, c_30])).
% 2.18/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.22  
% 2.18/1.22  Inference rules
% 2.18/1.22  ----------------------
% 2.18/1.22  #Ref     : 0
% 2.18/1.22  #Sup     : 76
% 2.18/1.22  #Fact    : 0
% 2.18/1.22  #Define  : 0
% 2.18/1.22  #Split   : 0
% 2.18/1.22  #Chain   : 0
% 2.18/1.22  #Close   : 0
% 2.18/1.22  
% 2.18/1.22  Ordering : KBO
% 2.18/1.22  
% 2.18/1.22  Simplification rules
% 2.18/1.22  ----------------------
% 2.18/1.22  #Subsume      : 9
% 2.18/1.22  #Demod        : 38
% 2.18/1.22  #Tautology    : 55
% 2.18/1.22  #SimpNegUnit  : 4
% 2.18/1.22  #BackRed      : 1
% 2.18/1.22  
% 2.18/1.22  #Partial instantiations: 0
% 2.18/1.22  #Strategies tried      : 1
% 2.18/1.22  
% 2.18/1.22  Timing (in seconds)
% 2.18/1.22  ----------------------
% 2.18/1.22  Preprocessing        : 0.27
% 2.18/1.22  Parsing              : 0.15
% 2.18/1.22  CNF conversion       : 0.02
% 2.18/1.22  Main loop            : 0.19
% 2.18/1.22  Inferencing          : 0.08
% 2.18/1.22  Reduction            : 0.06
% 2.18/1.22  Demodulation         : 0.04
% 2.18/1.22  BG Simplification    : 0.01
% 2.18/1.22  Subsumption          : 0.03
% 2.18/1.22  Abstraction          : 0.01
% 2.18/1.22  MUC search           : 0.00
% 2.18/1.22  Cooper               : 0.00
% 2.18/1.22  Total                : 0.49
% 2.18/1.22  Index Insertion      : 0.00
% 2.18/1.22  Index Deletion       : 0.00
% 2.18/1.22  Index Matching       : 0.00
% 2.18/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
