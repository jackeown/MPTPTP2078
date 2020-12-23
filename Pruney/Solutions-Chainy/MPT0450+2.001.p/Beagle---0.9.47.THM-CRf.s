%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:36 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 105 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 165 expanded)
%              Number of equality atoms :    8 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_66,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_96,plain,(
    ! [B_35,A_36] : k1_setfam_1(k2_tarski(B_35,A_36)) = k3_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_66])).

tff(c_16,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_102,plain,(
    ! [B_35,A_36] : k3_xboole_0(B_35,A_36) = k3_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_16])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_160,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski(A_41,B_42)
      | ~ r1_tarski(A_41,k3_xboole_0(B_42,C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_171,plain,(
    ! [B_42,C_43] : r1_tarski(k3_xboole_0(B_42,C_43),B_42) ),
    inference(resolution,[status(thm)],[c_6,c_160])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_172,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_228,plain,(
    ! [A_53,B_54] :
      ( v1_relat_1(A_53)
      | ~ v1_relat_1(B_54)
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_20,c_172])).

tff(c_245,plain,(
    ! [B_55,C_56] :
      ( v1_relat_1(k3_xboole_0(B_55,C_56))
      | ~ v1_relat_1(B_55) ) ),
    inference(resolution,[status(thm)],[c_171,c_228])).

tff(c_248,plain,(
    ! [B_35,A_36] :
      ( v1_relat_1(k3_xboole_0(B_35,A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_245])).

tff(c_177,plain,(
    ! [B_46,C_47] : r1_tarski(k3_xboole_0(B_46,C_47),B_46) ),
    inference(resolution,[status(thm)],[c_6,c_160])).

tff(c_186,plain,(
    ! [B_35,A_36] : r1_tarski(k3_xboole_0(B_35,A_36),A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_177])).

tff(c_24,plain,(
    ! [A_20,B_22] :
      ( r1_tarski(k3_relat_1(A_20),k3_relat_1(B_22))
      | ~ r1_tarski(A_20,B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_210,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_tarski(A_50,k3_xboole_0(B_51,C_52))
      | ~ r1_tarski(A_50,C_52)
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_227,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_210,c_26])).

tff(c_324,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_227])).

tff(c_327,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_324])).

tff(c_330,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_171,c_327])).

tff(c_333,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_248,c_330])).

tff(c_340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_333])).

tff(c_341,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_227])).

tff(c_345,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_341])).

tff(c_348,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_186,c_345])).

tff(c_351,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_248,c_348])).

tff(c_358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_351])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:04:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.23  
% 2.06/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.23  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 2.17/1.23  
% 2.17/1.23  %Foreground sorts:
% 2.17/1.23  
% 2.17/1.23  
% 2.17/1.23  %Background operators:
% 2.17/1.23  
% 2.17/1.23  
% 2.17/1.23  %Foreground operators:
% 2.17/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.23  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.17/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.17/1.23  
% 2.17/1.24  tff(f_75, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 2.17/1.24  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.17/1.24  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.17/1.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.17/1.24  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.17/1.24  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.17/1.24  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.17/1.24  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 2.17/1.24  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.17/1.24  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.17/1.24  tff(c_12, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.24  tff(c_66, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.24  tff(c_96, plain, (![B_35, A_36]: (k1_setfam_1(k2_tarski(B_35, A_36))=k3_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_12, c_66])).
% 2.17/1.24  tff(c_16, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.24  tff(c_102, plain, (![B_35, A_36]: (k3_xboole_0(B_35, A_36)=k3_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_96, c_16])).
% 2.17/1.24  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.24  tff(c_160, plain, (![A_41, B_42, C_43]: (r1_tarski(A_41, B_42) | ~r1_tarski(A_41, k3_xboole_0(B_42, C_43)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.24  tff(c_171, plain, (![B_42, C_43]: (r1_tarski(k3_xboole_0(B_42, C_43), B_42))), inference(resolution, [status(thm)], [c_6, c_160])).
% 2.17/1.24  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.24  tff(c_172, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.17/1.24  tff(c_228, plain, (![A_53, B_54]: (v1_relat_1(A_53) | ~v1_relat_1(B_54) | ~r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_20, c_172])).
% 2.17/1.24  tff(c_245, plain, (![B_55, C_56]: (v1_relat_1(k3_xboole_0(B_55, C_56)) | ~v1_relat_1(B_55))), inference(resolution, [status(thm)], [c_171, c_228])).
% 2.17/1.24  tff(c_248, plain, (![B_35, A_36]: (v1_relat_1(k3_xboole_0(B_35, A_36)) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_102, c_245])).
% 2.17/1.24  tff(c_177, plain, (![B_46, C_47]: (r1_tarski(k3_xboole_0(B_46, C_47), B_46))), inference(resolution, [status(thm)], [c_6, c_160])).
% 2.17/1.24  tff(c_186, plain, (![B_35, A_36]: (r1_tarski(k3_xboole_0(B_35, A_36), A_36))), inference(superposition, [status(thm), theory('equality')], [c_102, c_177])).
% 2.17/1.24  tff(c_24, plain, (![A_20, B_22]: (r1_tarski(k3_relat_1(A_20), k3_relat_1(B_22)) | ~r1_tarski(A_20, B_22) | ~v1_relat_1(B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.17/1.24  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.17/1.24  tff(c_210, plain, (![A_50, B_51, C_52]: (r1_tarski(A_50, k3_xboole_0(B_51, C_52)) | ~r1_tarski(A_50, C_52) | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.17/1.24  tff(c_26, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.17/1.24  tff(c_227, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_210, c_26])).
% 2.17/1.24  tff(c_324, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_227])).
% 2.17/1.24  tff(c_327, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_324])).
% 2.17/1.24  tff(c_330, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_171, c_327])).
% 2.17/1.24  tff(c_333, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_248, c_330])).
% 2.17/1.24  tff(c_340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_333])).
% 2.17/1.24  tff(c_341, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_227])).
% 2.17/1.24  tff(c_345, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_341])).
% 2.17/1.24  tff(c_348, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_186, c_345])).
% 2.17/1.24  tff(c_351, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_248, c_348])).
% 2.17/1.24  tff(c_358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_351])).
% 2.17/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.24  
% 2.17/1.24  Inference rules
% 2.17/1.24  ----------------------
% 2.17/1.24  #Ref     : 0
% 2.17/1.24  #Sup     : 77
% 2.17/1.24  #Fact    : 0
% 2.17/1.24  #Define  : 0
% 2.17/1.24  #Split   : 1
% 2.17/1.24  #Chain   : 0
% 2.17/1.24  #Close   : 0
% 2.17/1.24  
% 2.17/1.24  Ordering : KBO
% 2.17/1.24  
% 2.17/1.24  Simplification rules
% 2.17/1.24  ----------------------
% 2.17/1.24  #Subsume      : 7
% 2.17/1.24  #Demod        : 17
% 2.17/1.24  #Tautology    : 36
% 2.17/1.24  #SimpNegUnit  : 0
% 2.17/1.24  #BackRed      : 0
% 2.17/1.24  
% 2.17/1.24  #Partial instantiations: 0
% 2.17/1.24  #Strategies tried      : 1
% 2.17/1.24  
% 2.17/1.24  Timing (in seconds)
% 2.17/1.24  ----------------------
% 2.17/1.25  Preprocessing        : 0.29
% 2.17/1.25  Parsing              : 0.16
% 2.17/1.25  CNF conversion       : 0.02
% 2.17/1.25  Main loop            : 0.20
% 2.17/1.25  Inferencing          : 0.07
% 2.17/1.25  Reduction            : 0.07
% 2.17/1.25  Demodulation         : 0.06
% 2.17/1.25  BG Simplification    : 0.01
% 2.17/1.25  Subsumption          : 0.04
% 2.17/1.25  Abstraction          : 0.01
% 2.17/1.25  MUC search           : 0.00
% 2.17/1.25  Cooper               : 0.00
% 2.17/1.25  Total                : 0.52
% 2.17/1.25  Index Insertion      : 0.00
% 2.17/1.25  Index Deletion       : 0.00
% 2.17/1.25  Index Matching       : 0.00
% 2.17/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
