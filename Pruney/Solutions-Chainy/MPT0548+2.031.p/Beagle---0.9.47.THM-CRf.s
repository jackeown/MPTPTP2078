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
% DateTime   : Thu Dec  3 10:00:39 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   49 (  60 expanded)
%              Number of leaves         :   30 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  66 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_55,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
        & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_14,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_74,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_xboole_0(A_43,B_44)
      | ~ r2_hidden(C_45,k3_xboole_0(A_43,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_81,plain,(
    ! [A_6,C_45] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_45,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_74])).

tff(c_85,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_81])).

tff(c_90,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_127,plain,(
    ! [A_51,B_52] :
      ( k5_relat_1(k6_relat_1(A_51),B_52) = k7_relat_1(B_52,A_51)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_60,plain,(
    ! [A_37] :
      ( k5_relat_1(A_37,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_64,plain,(
    ! [A_26] : k5_relat_1(k6_relat_1(A_26),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_60])).

tff(c_134,plain,(
    ! [A_51] :
      ( k7_relat_1(k1_xboole_0,A_51) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_64])).

tff(c_147,plain,(
    ! [A_53] : k7_relat_1(k1_xboole_0,A_53) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_134])).

tff(c_18,plain,(
    ! [B_28,A_27] :
      ( k2_relat_1(k7_relat_1(B_28,A_27)) = k9_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_152,plain,(
    ! [A_53] :
      ( k9_relat_1(k1_xboole_0,A_53) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_18])).

tff(c_157,plain,(
    ! [A_53] : k9_relat_1(k1_xboole_0,A_53) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_20,c_152])).

tff(c_30,plain,(
    k9_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.25  % Computer   : n001.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % DateTime   : Tue Dec  1 18:53:15 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.10/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.09  
% 1.74/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.09  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 1.74/1.09  
% 1.74/1.09  %Foreground sorts:
% 1.74/1.09  
% 1.74/1.09  
% 1.74/1.09  %Background operators:
% 1.74/1.09  
% 1.74/1.09  
% 1.74/1.09  %Foreground operators:
% 1.74/1.09  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.74/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.74/1.09  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.74/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.74/1.09  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.74/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.74/1.09  tff('#skF_5', type, '#skF_5': $i).
% 1.74/1.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.74/1.09  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.74/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.74/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.74/1.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.74/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.74/1.09  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.74/1.09  
% 1.74/1.10  tff(f_53, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.74/1.10  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.74/1.10  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.74/1.10  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.74/1.10  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.74/1.10  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.74/1.10  tff(f_55, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.74/1.10  tff(f_68, axiom, (![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 1.74/1.10  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.74/1.10  tff(f_75, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.74/1.10  tff(c_14, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.74/1.10  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.74/1.10  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.74/1.10  tff(c_74, plain, (![A_43, B_44, C_45]: (~r1_xboole_0(A_43, B_44) | ~r2_hidden(C_45, k3_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.74/1.10  tff(c_81, plain, (![A_6, C_45]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_74])).
% 1.74/1.10  tff(c_85, plain, (![C_46]: (~r2_hidden(C_46, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_81])).
% 1.74/1.10  tff(c_90, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_85])).
% 1.74/1.10  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.74/1.10  tff(c_127, plain, (![A_51, B_52]: (k5_relat_1(k6_relat_1(A_51), B_52)=k7_relat_1(B_52, A_51) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.74/1.10  tff(c_16, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.74/1.10  tff(c_60, plain, (![A_37]: (k5_relat_1(A_37, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.74/1.10  tff(c_64, plain, (![A_26]: (k5_relat_1(k6_relat_1(A_26), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_60])).
% 1.74/1.10  tff(c_134, plain, (![A_51]: (k7_relat_1(k1_xboole_0, A_51)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_127, c_64])).
% 1.74/1.10  tff(c_147, plain, (![A_53]: (k7_relat_1(k1_xboole_0, A_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_134])).
% 1.74/1.10  tff(c_18, plain, (![B_28, A_27]: (k2_relat_1(k7_relat_1(B_28, A_27))=k9_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.74/1.10  tff(c_152, plain, (![A_53]: (k9_relat_1(k1_xboole_0, A_53)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_147, c_18])).
% 1.74/1.10  tff(c_157, plain, (![A_53]: (k9_relat_1(k1_xboole_0, A_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_20, c_152])).
% 1.74/1.10  tff(c_30, plain, (k9_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.74/1.10  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_30])).
% 1.74/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.10  
% 1.74/1.10  Inference rules
% 1.74/1.10  ----------------------
% 1.74/1.10  #Ref     : 0
% 1.74/1.10  #Sup     : 31
% 1.74/1.10  #Fact    : 0
% 1.74/1.10  #Define  : 0
% 1.74/1.10  #Split   : 0
% 1.74/1.10  #Chain   : 0
% 1.74/1.10  #Close   : 0
% 1.74/1.10  
% 1.74/1.10  Ordering : KBO
% 1.74/1.10  
% 1.74/1.10  Simplification rules
% 1.74/1.10  ----------------------
% 1.74/1.10  #Subsume      : 0
% 1.74/1.10  #Demod        : 10
% 1.74/1.10  #Tautology    : 21
% 1.74/1.10  #SimpNegUnit  : 0
% 1.74/1.10  #BackRed      : 1
% 1.74/1.10  
% 1.74/1.10  #Partial instantiations: 0
% 1.74/1.10  #Strategies tried      : 1
% 1.74/1.10  
% 1.74/1.10  Timing (in seconds)
% 1.74/1.10  ----------------------
% 1.74/1.11  Preprocessing        : 0.29
% 1.74/1.11  Parsing              : 0.16
% 1.74/1.11  CNF conversion       : 0.02
% 1.74/1.11  Main loop            : 0.14
% 1.74/1.11  Inferencing          : 0.06
% 1.74/1.11  Reduction            : 0.04
% 1.74/1.11  Demodulation         : 0.03
% 1.74/1.11  BG Simplification    : 0.01
% 1.74/1.11  Subsumption          : 0.02
% 1.74/1.11  Abstraction          : 0.01
% 1.74/1.11  MUC search           : 0.00
% 1.74/1.11  Cooper               : 0.00
% 1.74/1.11  Total                : 0.46
% 1.74/1.11  Index Insertion      : 0.00
% 1.74/1.11  Index Deletion       : 0.00
% 1.74/1.11  Index Matching       : 0.00
% 1.74/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
