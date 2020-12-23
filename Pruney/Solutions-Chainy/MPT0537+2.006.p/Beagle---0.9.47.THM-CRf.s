%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:20 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   52 (  53 expanded)
%              Number of leaves         :   33 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  57 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_55,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_38,plain,(
    k8_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_105,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_70,B_71)),A_70)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_192,plain,(
    ! [A_94,B_95] :
      ( k3_xboole_0(k2_relat_1(k8_relat_1(A_94,B_95)),A_94) = k2_relat_1(k8_relat_1(A_94,B_95))
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_105,c_12])).

tff(c_14,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_89,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ r1_xboole_0(A_63,B_64)
      | ~ r2_hidden(C_65,k3_xboole_0(A_63,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_95,plain,(
    ! [A_66,B_67] :
      ( ~ r1_xboole_0(A_66,B_67)
      | v1_xboole_0(k3_xboole_0(A_66,B_67)) ) ),
    inference(resolution,[status(thm)],[c_4,c_89])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_100,plain,(
    ! [A_68,B_69] :
      ( k3_xboole_0(A_68,B_69) = k1_xboole_0
      | ~ r1_xboole_0(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_95,c_6])).

tff(c_104,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_100])).

tff(c_221,plain,(
    ! [B_96] :
      ( k2_relat_1(k8_relat_1(k1_xboole_0,B_96)) = k1_xboole_0
      | ~ v1_relat_1(B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_104])).

tff(c_30,plain,(
    ! [A_43,B_44] :
      ( v1_relat_1(k8_relat_1(A_43,B_44))
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_61,plain,(
    ! [A_58] :
      ( k2_relat_1(A_58) != k1_xboole_0
      | k1_xboole_0 = A_58
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_68,plain,(
    ! [A_43,B_44] :
      ( k2_relat_1(k8_relat_1(A_43,B_44)) != k1_xboole_0
      | k8_relat_1(A_43,B_44) = k1_xboole_0
      | ~ v1_relat_1(B_44) ) ),
    inference(resolution,[status(thm)],[c_30,c_61])).

tff(c_241,plain,(
    ! [B_97] :
      ( k8_relat_1(k1_xboole_0,B_97) = k1_xboole_0
      | ~ v1_relat_1(B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_68])).

tff(c_247,plain,(
    k8_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_241])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.28  
% 2.13/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.13/1.28  
% 2.13/1.28  %Foreground sorts:
% 2.13/1.28  
% 2.13/1.28  
% 2.13/1.28  %Background operators:
% 2.13/1.28  
% 2.13/1.28  
% 2.13/1.28  %Foreground operators:
% 2.13/1.28  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.13/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.13/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.13/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.13/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.13/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.13/1.28  
% 2.13/1.29  tff(f_90, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 2.13/1.29  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_relat_1)).
% 2.13/1.29  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.13/1.29  tff(f_55, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.13/1.29  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.13/1.29  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.13/1.29  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.13/1.29  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.13/1.29  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.13/1.29  tff(c_38, plain, (k8_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.13/1.29  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.13/1.29  tff(c_105, plain, (![A_70, B_71]: (r1_tarski(k2_relat_1(k8_relat_1(A_70, B_71)), A_70) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.13/1.29  tff(c_12, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.13/1.29  tff(c_192, plain, (![A_94, B_95]: (k3_xboole_0(k2_relat_1(k8_relat_1(A_94, B_95)), A_94)=k2_relat_1(k8_relat_1(A_94, B_95)) | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_105, c_12])).
% 2.13/1.29  tff(c_14, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.13/1.29  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.29  tff(c_89, plain, (![A_63, B_64, C_65]: (~r1_xboole_0(A_63, B_64) | ~r2_hidden(C_65, k3_xboole_0(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.13/1.29  tff(c_95, plain, (![A_66, B_67]: (~r1_xboole_0(A_66, B_67) | v1_xboole_0(k3_xboole_0(A_66, B_67)))), inference(resolution, [status(thm)], [c_4, c_89])).
% 2.13/1.29  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.29  tff(c_100, plain, (![A_68, B_69]: (k3_xboole_0(A_68, B_69)=k1_xboole_0 | ~r1_xboole_0(A_68, B_69))), inference(resolution, [status(thm)], [c_95, c_6])).
% 2.13/1.29  tff(c_104, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_100])).
% 2.13/1.29  tff(c_221, plain, (![B_96]: (k2_relat_1(k8_relat_1(k1_xboole_0, B_96))=k1_xboole_0 | ~v1_relat_1(B_96))), inference(superposition, [status(thm), theory('equality')], [c_192, c_104])).
% 2.13/1.29  tff(c_30, plain, (![A_43, B_44]: (v1_relat_1(k8_relat_1(A_43, B_44)) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.13/1.29  tff(c_61, plain, (![A_58]: (k2_relat_1(A_58)!=k1_xboole_0 | k1_xboole_0=A_58 | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.13/1.29  tff(c_68, plain, (![A_43, B_44]: (k2_relat_1(k8_relat_1(A_43, B_44))!=k1_xboole_0 | k8_relat_1(A_43, B_44)=k1_xboole_0 | ~v1_relat_1(B_44))), inference(resolution, [status(thm)], [c_30, c_61])).
% 2.13/1.29  tff(c_241, plain, (![B_97]: (k8_relat_1(k1_xboole_0, B_97)=k1_xboole_0 | ~v1_relat_1(B_97))), inference(superposition, [status(thm), theory('equality')], [c_221, c_68])).
% 2.13/1.29  tff(c_247, plain, (k8_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_241])).
% 2.13/1.29  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_247])).
% 2.13/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.29  
% 2.13/1.29  Inference rules
% 2.13/1.29  ----------------------
% 2.13/1.29  #Ref     : 0
% 2.13/1.29  #Sup     : 45
% 2.13/1.29  #Fact    : 0
% 2.13/1.29  #Define  : 0
% 2.13/1.29  #Split   : 2
% 2.13/1.29  #Chain   : 0
% 2.13/1.29  #Close   : 0
% 2.13/1.29  
% 2.13/1.29  Ordering : KBO
% 2.13/1.29  
% 2.13/1.29  Simplification rules
% 2.13/1.29  ----------------------
% 2.13/1.29  #Subsume      : 1
% 2.13/1.29  #Demod        : 7
% 2.13/1.29  #Tautology    : 23
% 2.13/1.29  #SimpNegUnit  : 2
% 2.13/1.29  #BackRed      : 0
% 2.13/1.29  
% 2.13/1.29  #Partial instantiations: 0
% 2.13/1.29  #Strategies tried      : 1
% 2.13/1.29  
% 2.13/1.29  Timing (in seconds)
% 2.13/1.29  ----------------------
% 2.13/1.29  Preprocessing        : 0.30
% 2.13/1.29  Parsing              : 0.16
% 2.13/1.29  CNF conversion       : 0.02
% 2.13/1.29  Main loop            : 0.17
% 2.13/1.29  Inferencing          : 0.07
% 2.13/1.29  Reduction            : 0.05
% 2.13/1.29  Demodulation         : 0.03
% 2.13/1.29  BG Simplification    : 0.01
% 2.13/1.29  Subsumption          : 0.02
% 2.13/1.29  Abstraction          : 0.01
% 2.13/1.29  MUC search           : 0.00
% 2.13/1.29  Cooper               : 0.00
% 2.13/1.29  Total                : 0.50
% 2.13/1.29  Index Insertion      : 0.00
% 2.13/1.29  Index Deletion       : 0.00
% 2.13/1.29  Index Matching       : 0.00
% 2.13/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
