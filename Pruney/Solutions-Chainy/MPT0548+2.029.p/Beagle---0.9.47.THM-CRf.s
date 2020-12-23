%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:39 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   50 (  77 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  83 expanded)
%              Number of equality atoms :   21 (  33 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_61,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_92,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_32,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_2'(A_24),A_24)
      | v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    ! [A_51,B_52] : r1_xboole_0(k3_xboole_0(A_51,B_52),k4_xboole_0(A_51,B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_81,plain,(
    ! [A_13] : r1_xboole_0(k3_xboole_0(k1_xboole_0,A_13),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_78])).

tff(c_87,plain,(
    ! [A_62,B_63] :
      ( k3_xboole_0(A_62,B_63) = k1_xboole_0
      | ~ r1_xboole_0(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_110,plain,(
    ! [A_67] : k3_xboole_0(k3_xboole_0(k1_xboole_0,A_67),k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_81,c_87])).

tff(c_8,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_115,plain,(
    ! [A_67,C_7] :
      ( ~ r1_xboole_0(k3_xboole_0(k1_xboole_0,A_67),k1_xboole_0)
      | ~ r2_hidden(C_7,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_8])).

tff(c_129,plain,(
    ! [C_68] : ~ r2_hidden(C_68,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_115])).

tff(c_134,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_129])).

tff(c_36,plain,(
    ! [A_44] :
      ( k9_relat_1(A_44,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_138,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_134,c_36])).

tff(c_139,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_152,plain,(
    ! [B_70] : k3_xboole_0(k1_xboole_0,B_70) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_16])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_388,plain,(
    ! [B_87,A_88] :
      ( k9_relat_1(B_87,k3_xboole_0(k1_relat_1(B_87),A_88)) = k9_relat_1(B_87,A_88)
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_397,plain,(
    ! [A_88] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_88)) = k9_relat_1(k1_xboole_0,A_88)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_388])).

tff(c_401,plain,(
    ! [A_88] : k9_relat_1(k1_xboole_0,A_88) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_138,c_152,c_397])).

tff(c_42,plain,(
    k9_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:27:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.27  
% 2.26/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.28  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 2.26/1.28  
% 2.26/1.28  %Foreground sorts:
% 2.26/1.28  
% 2.26/1.28  
% 2.26/1.28  %Background operators:
% 2.26/1.28  
% 2.26/1.28  
% 2.26/1.28  %Foreground operators:
% 2.26/1.28  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.26/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.26/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.26/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.26/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.26/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.26/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.26/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.26/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.26/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.26/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.26/1.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.26/1.28  
% 2.26/1.29  tff(f_81, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.26/1.29  tff(f_51, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.26/1.29  tff(f_61, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_xboole_1)).
% 2.26/1.29  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.26/1.29  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.26/1.29  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 2.26/1.29  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.26/1.29  tff(f_92, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.26/1.29  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 2.26/1.29  tff(f_95, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.26/1.29  tff(c_32, plain, (![A_24]: (r2_hidden('#skF_2'(A_24), A_24) | v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.26/1.29  tff(c_16, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.26/1.29  tff(c_78, plain, (![A_51, B_52]: (r1_xboole_0(k3_xboole_0(A_51, B_52), k4_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.26/1.29  tff(c_81, plain, (![A_13]: (r1_xboole_0(k3_xboole_0(k1_xboole_0, A_13), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_78])).
% 2.26/1.29  tff(c_87, plain, (![A_62, B_63]: (k3_xboole_0(A_62, B_63)=k1_xboole_0 | ~r1_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.29  tff(c_110, plain, (![A_67]: (k3_xboole_0(k3_xboole_0(k1_xboole_0, A_67), k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_81, c_87])).
% 2.26/1.29  tff(c_8, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.26/1.29  tff(c_115, plain, (![A_67, C_7]: (~r1_xboole_0(k3_xboole_0(k1_xboole_0, A_67), k1_xboole_0) | ~r2_hidden(C_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_110, c_8])).
% 2.26/1.29  tff(c_129, plain, (![C_68]: (~r2_hidden(C_68, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_115])).
% 2.26/1.29  tff(c_134, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_129])).
% 2.26/1.29  tff(c_36, plain, (![A_44]: (k9_relat_1(A_44, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.26/1.29  tff(c_138, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_134, c_36])).
% 2.26/1.29  tff(c_139, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.26/1.29  tff(c_152, plain, (![B_70]: (k3_xboole_0(k1_xboole_0, B_70)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_139, c_16])).
% 2.26/1.29  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.26/1.29  tff(c_388, plain, (![B_87, A_88]: (k9_relat_1(B_87, k3_xboole_0(k1_relat_1(B_87), A_88))=k9_relat_1(B_87, A_88) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.26/1.29  tff(c_397, plain, (![A_88]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_88))=k9_relat_1(k1_xboole_0, A_88) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_388])).
% 2.26/1.29  tff(c_401, plain, (![A_88]: (k9_relat_1(k1_xboole_0, A_88)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_138, c_152, c_397])).
% 2.26/1.29  tff(c_42, plain, (k9_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.26/1.29  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_401, c_42])).
% 2.26/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.29  
% 2.26/1.29  Inference rules
% 2.26/1.29  ----------------------
% 2.26/1.29  #Ref     : 0
% 2.26/1.29  #Sup     : 86
% 2.26/1.29  #Fact    : 0
% 2.26/1.29  #Define  : 0
% 2.26/1.29  #Split   : 0
% 2.26/1.29  #Chain   : 0
% 2.26/1.29  #Close   : 0
% 2.26/1.29  
% 2.26/1.29  Ordering : KBO
% 2.26/1.29  
% 2.26/1.29  Simplification rules
% 2.26/1.29  ----------------------
% 2.26/1.29  #Subsume      : 4
% 2.26/1.29  #Demod        : 52
% 2.26/1.29  #Tautology    : 61
% 2.26/1.29  #SimpNegUnit  : 3
% 2.26/1.29  #BackRed      : 2
% 2.26/1.29  
% 2.26/1.29  #Partial instantiations: 0
% 2.26/1.29  #Strategies tried      : 1
% 2.26/1.29  
% 2.26/1.29  Timing (in seconds)
% 2.26/1.29  ----------------------
% 2.26/1.29  Preprocessing        : 0.30
% 2.26/1.29  Parsing              : 0.17
% 2.26/1.29  CNF conversion       : 0.02
% 2.26/1.29  Main loop            : 0.21
% 2.26/1.29  Inferencing          : 0.09
% 2.26/1.29  Reduction            : 0.07
% 2.26/1.29  Demodulation         : 0.05
% 2.26/1.29  BG Simplification    : 0.01
% 2.26/1.29  Subsumption          : 0.03
% 2.26/1.29  Abstraction          : 0.01
% 2.26/1.29  MUC search           : 0.00
% 2.26/1.29  Cooper               : 0.00
% 2.26/1.29  Total                : 0.55
% 2.26/1.29  Index Insertion      : 0.00
% 2.26/1.29  Index Deletion       : 0.00
% 2.26/1.29  Index Matching       : 0.00
% 2.26/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
