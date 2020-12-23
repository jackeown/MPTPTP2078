%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:03 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   55 (  86 expanded)
%              Number of leaves         :   29 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 131 expanded)
%              Number of equality atoms :   16 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    ! [B_37,A_36] :
      ( r1_tarski(k7_relat_1(B_37,A_36),B_37)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(A_25,k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_157,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_162,plain,(
    ! [A_58,B_59] :
      ( v1_relat_1(A_58)
      | ~ v1_relat_1(B_59)
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_18,c_157])).

tff(c_166,plain,(
    ! [B_37,A_36] :
      ( v1_relat_1(k7_relat_1(B_37,A_36))
      | ~ v1_relat_1(B_37) ) ),
    inference(resolution,[status(thm)],[c_28,c_162])).

tff(c_22,plain,(
    ! [C_32,A_30,B_31] :
      ( k7_relat_1(k7_relat_1(C_32,A_30),B_31) = k7_relat_1(C_32,k3_xboole_0(A_30,B_31))
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_187,plain,(
    ! [A_71,B_72] :
      ( r1_tarski(k1_relat_1(A_71),k1_relat_1(B_72))
      | ~ r1_tarski(A_71,B_72)
      | ~ v1_relat_1(B_72)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [B_39,A_38] :
      ( k7_relat_1(B_39,A_38) = B_39
      | ~ r1_tarski(k1_relat_1(B_39),A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_222,plain,(
    ! [A_78,B_79] :
      ( k7_relat_1(A_78,k1_relat_1(B_79)) = A_78
      | ~ r1_tarski(A_78,B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_187,c_30])).

tff(c_805,plain,(
    ! [C_129,A_130,B_131] :
      ( k7_relat_1(C_129,k3_xboole_0(A_130,k1_relat_1(B_131))) = k7_relat_1(C_129,A_130)
      | ~ r1_tarski(k7_relat_1(C_129,A_130),B_131)
      | ~ v1_relat_1(B_131)
      | ~ v1_relat_1(k7_relat_1(C_129,A_130))
      | ~ v1_relat_1(C_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_222])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_84,plain,(
    ! [A_50,B_51] : k1_setfam_1(k2_tarski(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_99,plain,(
    ! [B_52,A_53] : k1_setfam_1(k2_tarski(B_52,A_53)) = k3_xboole_0(A_53,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_14,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_105,plain,(
    ! [B_52,A_53] : k3_xboole_0(B_52,A_53) = k3_xboole_0(A_53,B_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_14])).

tff(c_32,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_155,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_32])).

tff(c_867,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_805,c_155])).

tff(c_909,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_867])).

tff(c_912,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_909])).

tff(c_915,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_166,c_912])).

tff(c_919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_915])).

tff(c_920,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_909])).

tff(c_924,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_920])).

tff(c_928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_924])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.48  
% 3.30/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.48  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.30/1.48  
% 3.30/1.48  %Foreground sorts:
% 3.30/1.48  
% 3.30/1.48  
% 3.30/1.48  %Background operators:
% 3.30/1.48  
% 3.30/1.48  
% 3.30/1.48  %Foreground operators:
% 3.30/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.30/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.30/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.30/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.30/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.30/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.30/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.30/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.30/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.30/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.30/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.30/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.30/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.30/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.30/1.48  
% 3.30/1.49  tff(f_80, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 3.30/1.49  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 3.30/1.49  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.30/1.49  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.30/1.49  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 3.30/1.49  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 3.30/1.49  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.30/1.49  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.30/1.49  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.30/1.49  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.30/1.49  tff(c_28, plain, (![B_37, A_36]: (r1_tarski(k7_relat_1(B_37, A_36), B_37) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.30/1.49  tff(c_18, plain, (![A_25, B_26]: (m1_subset_1(A_25, k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.30/1.49  tff(c_157, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.30/1.49  tff(c_162, plain, (![A_58, B_59]: (v1_relat_1(A_58) | ~v1_relat_1(B_59) | ~r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_18, c_157])).
% 3.30/1.49  tff(c_166, plain, (![B_37, A_36]: (v1_relat_1(k7_relat_1(B_37, A_36)) | ~v1_relat_1(B_37))), inference(resolution, [status(thm)], [c_28, c_162])).
% 3.30/1.49  tff(c_22, plain, (![C_32, A_30, B_31]: (k7_relat_1(k7_relat_1(C_32, A_30), B_31)=k7_relat_1(C_32, k3_xboole_0(A_30, B_31)) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.30/1.49  tff(c_187, plain, (![A_71, B_72]: (r1_tarski(k1_relat_1(A_71), k1_relat_1(B_72)) | ~r1_tarski(A_71, B_72) | ~v1_relat_1(B_72) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.30/1.49  tff(c_30, plain, (![B_39, A_38]: (k7_relat_1(B_39, A_38)=B_39 | ~r1_tarski(k1_relat_1(B_39), A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.30/1.49  tff(c_222, plain, (![A_78, B_79]: (k7_relat_1(A_78, k1_relat_1(B_79))=A_78 | ~r1_tarski(A_78, B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_187, c_30])).
% 3.30/1.49  tff(c_805, plain, (![C_129, A_130, B_131]: (k7_relat_1(C_129, k3_xboole_0(A_130, k1_relat_1(B_131)))=k7_relat_1(C_129, A_130) | ~r1_tarski(k7_relat_1(C_129, A_130), B_131) | ~v1_relat_1(B_131) | ~v1_relat_1(k7_relat_1(C_129, A_130)) | ~v1_relat_1(C_129))), inference(superposition, [status(thm), theory('equality')], [c_22, c_222])).
% 3.30/1.49  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.30/1.49  tff(c_84, plain, (![A_50, B_51]: (k1_setfam_1(k2_tarski(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.30/1.49  tff(c_99, plain, (![B_52, A_53]: (k1_setfam_1(k2_tarski(B_52, A_53))=k3_xboole_0(A_53, B_52))), inference(superposition, [status(thm), theory('equality')], [c_2, c_84])).
% 3.30/1.49  tff(c_14, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.30/1.49  tff(c_105, plain, (![B_52, A_53]: (k3_xboole_0(B_52, A_53)=k3_xboole_0(A_53, B_52))), inference(superposition, [status(thm), theory('equality')], [c_99, c_14])).
% 3.30/1.49  tff(c_32, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.30/1.49  tff(c_155, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_32])).
% 3.30/1.49  tff(c_867, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_805, c_155])).
% 3.30/1.49  tff(c_909, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_867])).
% 3.30/1.49  tff(c_912, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_909])).
% 3.30/1.49  tff(c_915, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_166, c_912])).
% 3.30/1.49  tff(c_919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_915])).
% 3.30/1.49  tff(c_920, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_909])).
% 3.30/1.49  tff(c_924, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_920])).
% 3.30/1.49  tff(c_928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_924])).
% 3.30/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.49  
% 3.30/1.49  Inference rules
% 3.30/1.49  ----------------------
% 3.30/1.49  #Ref     : 0
% 3.30/1.49  #Sup     : 238
% 3.30/1.49  #Fact    : 0
% 3.30/1.49  #Define  : 0
% 3.30/1.49  #Split   : 1
% 3.30/1.49  #Chain   : 0
% 3.30/1.49  #Close   : 0
% 3.30/1.49  
% 3.30/1.49  Ordering : KBO
% 3.30/1.49  
% 3.30/1.49  Simplification rules
% 3.30/1.49  ----------------------
% 3.30/1.49  #Subsume      : 40
% 3.30/1.49  #Demod        : 8
% 3.30/1.49  #Tautology    : 52
% 3.30/1.49  #SimpNegUnit  : 0
% 3.30/1.49  #BackRed      : 0
% 3.30/1.49  
% 3.30/1.49  #Partial instantiations: 0
% 3.30/1.49  #Strategies tried      : 1
% 3.30/1.49  
% 3.30/1.49  Timing (in seconds)
% 3.30/1.49  ----------------------
% 3.46/1.49  Preprocessing        : 0.31
% 3.46/1.49  Parsing              : 0.16
% 3.46/1.49  CNF conversion       : 0.02
% 3.46/1.49  Main loop            : 0.42
% 3.46/1.49  Inferencing          : 0.17
% 3.46/1.49  Reduction            : 0.12
% 3.46/1.49  Demodulation         : 0.10
% 3.46/1.49  BG Simplification    : 0.03
% 3.46/1.49  Subsumption          : 0.08
% 3.46/1.49  Abstraction          : 0.03
% 3.46/1.49  MUC search           : 0.00
% 3.46/1.49  Cooper               : 0.00
% 3.46/1.49  Total                : 0.76
% 3.46/1.49  Index Insertion      : 0.00
% 3.46/1.49  Index Deletion       : 0.00
% 3.46/1.49  Index Matching       : 0.00
% 3.46/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
