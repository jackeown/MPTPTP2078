%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:00 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   53 (  84 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 128 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_60,plain,(
    ! [C_22,A_23,B_24] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_60])).

tff(c_134,plain,(
    ! [C_40,B_41,A_42] :
      ( v5_relat_1(C_40,B_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_42,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_138,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_134])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [C_43,A_44,B_45] :
      ( v4_relat_1(C_43,A_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_143,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_139])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(B_10),A_9)
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_tarski(A_25,k2_xboole_0(C_26,B_27))
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_25,B_2,A_1] :
      ( r1_tarski(A_25,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_25,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_65])).

tff(c_16,plain,(
    ! [A_13] :
      ( k2_xboole_0(k1_relat_1(A_13),k2_relat_1(A_13)) = k3_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_144,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_tarski(k2_xboole_0(A_46,C_47),B_48)
      | ~ r1_tarski(C_47,B_48)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_206,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k3_relat_1(A_62),B_63)
      | ~ r1_tarski(k2_relat_1(A_62),B_63)
      | ~ r1_tarski(k1_relat_1(A_62),B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_144])).

tff(c_24,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_215,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_206,c_24])).

tff(c_224,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_215])).

tff(c_232,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_224])).

tff(c_245,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_71,c_232])).

tff(c_249,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_245])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_143,c_249])).

tff(c_254,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_224])).

tff(c_269,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_254])).

tff(c_284,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_269])).

tff(c_288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_138,c_284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.24  
% 2.13/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.24  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.13/1.24  
% 2.13/1.24  %Foreground sorts:
% 2.13/1.24  
% 2.13/1.24  
% 2.13/1.24  %Background operators:
% 2.13/1.24  
% 2.13/1.24  
% 2.13/1.24  %Foreground operators:
% 2.13/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.24  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.13/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.13/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.13/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.13/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.13/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.24  
% 2.13/1.26  tff(f_68, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relset_1)).
% 2.13/1.26  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.13/1.26  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.13/1.26  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.13/1.26  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.13/1.26  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.13/1.26  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.13/1.26  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 2.13/1.26  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.13/1.26  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.26  tff(c_60, plain, (![C_22, A_23, B_24]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.13/1.26  tff(c_64, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_60])).
% 2.13/1.26  tff(c_134, plain, (![C_40, B_41, A_42]: (v5_relat_1(C_40, B_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_42, B_41))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.13/1.26  tff(c_138, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_134])).
% 2.13/1.26  tff(c_14, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.13/1.26  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.26  tff(c_139, plain, (![C_43, A_44, B_45]: (v4_relat_1(C_43, A_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.13/1.26  tff(c_143, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_139])).
% 2.13/1.26  tff(c_10, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(B_10), A_9) | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.13/1.26  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.13/1.26  tff(c_65, plain, (![A_25, C_26, B_27]: (r1_tarski(A_25, k2_xboole_0(C_26, B_27)) | ~r1_tarski(A_25, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.26  tff(c_71, plain, (![A_25, B_2, A_1]: (r1_tarski(A_25, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_25, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_65])).
% 2.13/1.26  tff(c_16, plain, (![A_13]: (k2_xboole_0(k1_relat_1(A_13), k2_relat_1(A_13))=k3_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.13/1.26  tff(c_144, plain, (![A_46, C_47, B_48]: (r1_tarski(k2_xboole_0(A_46, C_47), B_48) | ~r1_tarski(C_47, B_48) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.13/1.26  tff(c_206, plain, (![A_62, B_63]: (r1_tarski(k3_relat_1(A_62), B_63) | ~r1_tarski(k2_relat_1(A_62), B_63) | ~r1_tarski(k1_relat_1(A_62), B_63) | ~v1_relat_1(A_62))), inference(superposition, [status(thm), theory('equality')], [c_16, c_144])).
% 2.13/1.26  tff(c_24, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.26  tff(c_215, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_206, c_24])).
% 2.13/1.26  tff(c_224, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_215])).
% 2.13/1.26  tff(c_232, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_224])).
% 2.13/1.26  tff(c_245, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_71, c_232])).
% 2.13/1.26  tff(c_249, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_245])).
% 2.13/1.26  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_143, c_249])).
% 2.13/1.26  tff(c_254, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_224])).
% 2.13/1.26  tff(c_269, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_4, c_254])).
% 2.13/1.26  tff(c_284, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_269])).
% 2.13/1.26  tff(c_288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_138, c_284])).
% 2.13/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.26  
% 2.13/1.26  Inference rules
% 2.13/1.26  ----------------------
% 2.13/1.26  #Ref     : 0
% 2.13/1.26  #Sup     : 57
% 2.13/1.26  #Fact    : 0
% 2.13/1.26  #Define  : 0
% 2.13/1.26  #Split   : 2
% 2.13/1.26  #Chain   : 0
% 2.13/1.26  #Close   : 0
% 2.13/1.26  
% 2.13/1.26  Ordering : KBO
% 2.13/1.26  
% 2.13/1.26  Simplification rules
% 2.13/1.26  ----------------------
% 2.13/1.26  #Subsume      : 8
% 2.13/1.26  #Demod        : 12
% 2.13/1.26  #Tautology    : 12
% 2.13/1.26  #SimpNegUnit  : 0
% 2.13/1.26  #BackRed      : 0
% 2.13/1.26  
% 2.13/1.26  #Partial instantiations: 0
% 2.13/1.26  #Strategies tried      : 1
% 2.13/1.26  
% 2.13/1.26  Timing (in seconds)
% 2.13/1.26  ----------------------
% 2.13/1.26  Preprocessing        : 0.27
% 2.13/1.26  Parsing              : 0.15
% 2.13/1.26  CNF conversion       : 0.02
% 2.13/1.26  Main loop            : 0.22
% 2.13/1.26  Inferencing          : 0.08
% 2.13/1.26  Reduction            : 0.07
% 2.13/1.26  Demodulation         : 0.05
% 2.13/1.26  BG Simplification    : 0.01
% 2.13/1.26  Subsumption          : 0.04
% 2.13/1.26  Abstraction          : 0.01
% 2.13/1.26  MUC search           : 0.00
% 2.13/1.26  Cooper               : 0.00
% 2.13/1.26  Total                : 0.52
% 2.13/1.26  Index Insertion      : 0.00
% 2.13/1.26  Index Deletion       : 0.00
% 2.13/1.26  Index Matching       : 0.00
% 2.13/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
