%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:42 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   51 (  71 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 (  78 expanded)
%              Number of equality atoms :   21 (  34 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_18,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_2'(A_11),A_11)
      | v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_50,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    ! [A_45] : k4_xboole_0(A_45,A_45) = k3_xboole_0(A_45,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_50])).

tff(c_84,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_8])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_97,plain,(
    ! [C_5] :
      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r2_hidden(C_5,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_4])).

tff(c_103,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_97])).

tff(c_108,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_103])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_141,plain,(
    ! [B_52,A_53] :
      ( k7_relat_1(B_52,A_53) = B_52
      | ~ r1_tarski(k1_relat_1(B_52),A_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_144,plain,(
    ! [A_53] :
      ( k7_relat_1(k1_xboole_0,A_53) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_53)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_141])).

tff(c_157,plain,(
    ! [A_56] : k7_relat_1(k1_xboole_0,A_56) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_6,c_144])).

tff(c_20,plain,(
    ! [B_30,A_29] :
      ( k2_relat_1(k7_relat_1(B_30,A_29)) = k9_relat_1(B_30,A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_162,plain,(
    ! [A_56] :
      ( k9_relat_1(k1_xboole_0,A_56) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_20])).

tff(c_167,plain,(
    ! [A_56] : k9_relat_1(k1_xboole_0,A_56) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_22,c_162])).

tff(c_28,plain,(
    k9_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.21  
% 1.73/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 1.73/1.22  
% 1.73/1.22  %Foreground sorts:
% 1.73/1.22  
% 1.73/1.22  
% 1.73/1.22  %Background operators:
% 1.73/1.22  
% 1.73/1.22  
% 1.73/1.22  %Foreground operators:
% 1.73/1.22  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.73/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.73/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.73/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.73/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.73/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.73/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.73/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.73/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.73/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.73/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.73/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.73/1.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.73/1.22  
% 1.92/1.23  tff(f_57, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.92/1.23  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.92/1.23  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.92/1.23  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.92/1.23  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.92/1.23  tff(f_64, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.92/1.23  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.92/1.23  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 1.92/1.23  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.92/1.23  tff(f_73, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.92/1.23  tff(c_18, plain, (![A_11]: (r2_hidden('#skF_2'(A_11), A_11) | v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.92/1.23  tff(c_12, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.23  tff(c_8, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.23  tff(c_50, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k4_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.92/1.23  tff(c_74, plain, (![A_45]: (k4_xboole_0(A_45, A_45)=k3_xboole_0(A_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_50])).
% 1.92/1.23  tff(c_84, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_74, c_8])).
% 1.92/1.23  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.92/1.23  tff(c_97, plain, (![C_5]: (~r1_xboole_0(k1_xboole_0, k1_xboole_0) | ~r2_hidden(C_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_84, c_4])).
% 1.92/1.23  tff(c_103, plain, (![C_46]: (~r2_hidden(C_46, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_97])).
% 1.92/1.23  tff(c_108, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_103])).
% 1.92/1.23  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.23  tff(c_6, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.23  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.92/1.23  tff(c_141, plain, (![B_52, A_53]: (k7_relat_1(B_52, A_53)=B_52 | ~r1_tarski(k1_relat_1(B_52), A_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.92/1.23  tff(c_144, plain, (![A_53]: (k7_relat_1(k1_xboole_0, A_53)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_53) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_141])).
% 1.92/1.23  tff(c_157, plain, (![A_56]: (k7_relat_1(k1_xboole_0, A_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_6, c_144])).
% 1.92/1.23  tff(c_20, plain, (![B_30, A_29]: (k2_relat_1(k7_relat_1(B_30, A_29))=k9_relat_1(B_30, A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.23  tff(c_162, plain, (![A_56]: (k9_relat_1(k1_xboole_0, A_56)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_157, c_20])).
% 1.92/1.23  tff(c_167, plain, (![A_56]: (k9_relat_1(k1_xboole_0, A_56)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_22, c_162])).
% 1.92/1.23  tff(c_28, plain, (k9_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.92/1.23  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_28])).
% 1.92/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.23  
% 1.92/1.23  Inference rules
% 1.92/1.23  ----------------------
% 1.92/1.23  #Ref     : 0
% 1.92/1.23  #Sup     : 34
% 1.92/1.23  #Fact    : 0
% 1.92/1.23  #Define  : 0
% 1.92/1.23  #Split   : 0
% 1.92/1.23  #Chain   : 0
% 1.92/1.23  #Close   : 0
% 1.92/1.23  
% 1.92/1.23  Ordering : KBO
% 1.92/1.23  
% 1.92/1.23  Simplification rules
% 1.92/1.23  ----------------------
% 1.92/1.23  #Subsume      : 0
% 1.92/1.23  #Demod        : 12
% 1.92/1.23  #Tautology    : 23
% 1.92/1.23  #SimpNegUnit  : 1
% 1.92/1.23  #BackRed      : 1
% 1.92/1.23  
% 1.92/1.23  #Partial instantiations: 0
% 1.92/1.23  #Strategies tried      : 1
% 1.92/1.23  
% 1.92/1.23  Timing (in seconds)
% 1.92/1.23  ----------------------
% 1.92/1.23  Preprocessing        : 0.29
% 1.92/1.23  Parsing              : 0.16
% 1.92/1.23  CNF conversion       : 0.02
% 1.92/1.23  Main loop            : 0.14
% 1.92/1.23  Inferencing          : 0.07
% 1.92/1.23  Reduction            : 0.04
% 1.92/1.23  Demodulation         : 0.03
% 1.92/1.23  BG Simplification    : 0.01
% 1.92/1.23  Subsumption          : 0.01
% 1.92/1.23  Abstraction          : 0.01
% 1.92/1.23  MUC search           : 0.00
% 1.92/1.23  Cooper               : 0.00
% 1.92/1.23  Total                : 0.46
% 1.92/1.23  Index Insertion      : 0.00
% 1.92/1.23  Index Deletion       : 0.00
% 1.92/1.23  Index Matching       : 0.00
% 1.92/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
