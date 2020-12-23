%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:18 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   46 (  60 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  71 expanded)
%              Number of equality atoms :   25 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_52,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_76])).

tff(c_12,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_5] : v1_relat_1(k6_relat_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [B_13,A_12] : k5_relat_1(k6_relat_1(B_13),k6_relat_1(A_12)) = k6_relat_1(k3_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_94,plain,(
    ! [A_25,B_26] :
      ( k5_relat_1(k6_relat_1(A_25),B_26) = B_26
      | ~ r1_tarski(k1_relat_1(B_26),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_97,plain,(
    ! [A_25,A_9] :
      ( k5_relat_1(k6_relat_1(A_25),k6_relat_1(A_9)) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_25)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_94])).

tff(c_100,plain,(
    ! [A_27,A_28] :
      ( k6_relat_1(k3_xboole_0(A_27,A_28)) = k6_relat_1(A_27)
      | ~ r1_tarski(A_27,A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_18,c_97])).

tff(c_112,plain,(
    ! [A_27,A_28] :
      ( k3_xboole_0(A_27,A_28) = k1_relat_1(k6_relat_1(A_27))
      | ~ r1_tarski(A_27,A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_12])).

tff(c_134,plain,(
    ! [A_29,A_30] :
      ( k3_xboole_0(A_29,A_30) = A_29
      | ~ r1_tarski(A_29,A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_112])).

tff(c_138,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_84,c_134])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_145,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_2])).

tff(c_14,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_168,plain,(
    ! [B_31,A_32] :
      ( k9_relat_1(B_31,k2_relat_1(A_32)) = k2_relat_1(k5_relat_1(A_32,B_31))
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_177,plain,(
    ! [A_9,B_31] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_9),B_31)) = k9_relat_1(B_31,A_9)
      | ~ v1_relat_1(B_31)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_168])).

tff(c_241,plain,(
    ! [A_37,B_38] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_37),B_38)) = k9_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_177])).

tff(c_259,plain,(
    ! [A_12,B_13] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_12,B_13))) = k9_relat_1(k6_relat_1(A_12),B_13)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_241])).

tff(c_263,plain,(
    ! [A_12,B_13] : k9_relat_1(k6_relat_1(A_12),B_13) = k3_xboole_0(A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14,c_259])).

tff(c_20,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_264,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_20])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_264])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:14:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.41  
% 2.17/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.41  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.17/1.41  
% 2.17/1.41  %Foreground sorts:
% 2.17/1.41  
% 2.17/1.41  
% 2.17/1.41  %Background operators:
% 2.17/1.41  
% 2.17/1.41  
% 2.17/1.41  %Foreground operators:
% 2.17/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.17/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.17/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.17/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.41  
% 2.17/1.42  tff(f_57, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 2.17/1.42  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.17/1.42  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.17/1.42  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.17/1.42  tff(f_52, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.17/1.42  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.17/1.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.17/1.42  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 2.17/1.42  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.17/1.42  tff(c_76, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.42  tff(c_84, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_76])).
% 2.17/1.42  tff(c_12, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.17/1.42  tff(c_8, plain, (![A_5]: (v1_relat_1(k6_relat_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.42  tff(c_18, plain, (![B_13, A_12]: (k5_relat_1(k6_relat_1(B_13), k6_relat_1(A_12))=k6_relat_1(k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.17/1.42  tff(c_94, plain, (![A_25, B_26]: (k5_relat_1(k6_relat_1(A_25), B_26)=B_26 | ~r1_tarski(k1_relat_1(B_26), A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.17/1.42  tff(c_97, plain, (![A_25, A_9]: (k5_relat_1(k6_relat_1(A_25), k6_relat_1(A_9))=k6_relat_1(A_9) | ~r1_tarski(A_9, A_25) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_94])).
% 2.17/1.42  tff(c_100, plain, (![A_27, A_28]: (k6_relat_1(k3_xboole_0(A_27, A_28))=k6_relat_1(A_27) | ~r1_tarski(A_27, A_28))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_18, c_97])).
% 2.17/1.42  tff(c_112, plain, (![A_27, A_28]: (k3_xboole_0(A_27, A_28)=k1_relat_1(k6_relat_1(A_27)) | ~r1_tarski(A_27, A_28))), inference(superposition, [status(thm), theory('equality')], [c_100, c_12])).
% 2.17/1.42  tff(c_134, plain, (![A_29, A_30]: (k3_xboole_0(A_29, A_30)=A_29 | ~r1_tarski(A_29, A_30))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_112])).
% 2.17/1.42  tff(c_138, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_84, c_134])).
% 2.17/1.42  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.42  tff(c_145, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_138, c_2])).
% 2.17/1.42  tff(c_14, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.17/1.42  tff(c_168, plain, (![B_31, A_32]: (k9_relat_1(B_31, k2_relat_1(A_32))=k2_relat_1(k5_relat_1(A_32, B_31)) | ~v1_relat_1(B_31) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.17/1.42  tff(c_177, plain, (![A_9, B_31]: (k2_relat_1(k5_relat_1(k6_relat_1(A_9), B_31))=k9_relat_1(B_31, A_9) | ~v1_relat_1(B_31) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_168])).
% 2.17/1.42  tff(c_241, plain, (![A_37, B_38]: (k2_relat_1(k5_relat_1(k6_relat_1(A_37), B_38))=k9_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_177])).
% 2.17/1.42  tff(c_259, plain, (![A_12, B_13]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_12, B_13)))=k9_relat_1(k6_relat_1(A_12), B_13) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_241])).
% 2.17/1.42  tff(c_263, plain, (![A_12, B_13]: (k9_relat_1(k6_relat_1(A_12), B_13)=k3_xboole_0(A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14, c_259])).
% 2.17/1.42  tff(c_20, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.17/1.42  tff(c_264, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_263, c_20])).
% 2.17/1.42  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_264])).
% 2.17/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.42  
% 2.17/1.42  Inference rules
% 2.17/1.42  ----------------------
% 2.17/1.42  #Ref     : 0
% 2.17/1.42  #Sup     : 60
% 2.17/1.42  #Fact    : 0
% 2.17/1.42  #Define  : 0
% 2.17/1.42  #Split   : 1
% 2.17/1.42  #Chain   : 0
% 2.17/1.42  #Close   : 0
% 2.17/1.42  
% 2.17/1.42  Ordering : KBO
% 2.17/1.42  
% 2.17/1.42  Simplification rules
% 2.17/1.42  ----------------------
% 2.17/1.42  #Subsume      : 5
% 2.17/1.42  #Demod        : 23
% 2.17/1.42  #Tautology    : 35
% 2.17/1.42  #SimpNegUnit  : 0
% 2.17/1.42  #BackRed      : 1
% 2.17/1.42  
% 2.17/1.42  #Partial instantiations: 0
% 2.17/1.42  #Strategies tried      : 1
% 2.17/1.42  
% 2.17/1.42  Timing (in seconds)
% 2.17/1.42  ----------------------
% 2.17/1.43  Preprocessing        : 0.36
% 2.17/1.43  Parsing              : 0.18
% 2.17/1.43  CNF conversion       : 0.02
% 2.17/1.43  Main loop            : 0.19
% 2.17/1.43  Inferencing          : 0.07
% 2.17/1.43  Reduction            : 0.07
% 2.17/1.43  Demodulation         : 0.05
% 2.17/1.43  BG Simplification    : 0.01
% 2.17/1.43  Subsumption          : 0.03
% 2.17/1.43  Abstraction          : 0.02
% 2.17/1.43  MUC search           : 0.00
% 2.17/1.43  Cooper               : 0.00
% 2.17/1.43  Total                : 0.58
% 2.17/1.43  Index Insertion      : 0.00
% 2.17/1.43  Index Deletion       : 0.00
% 2.17/1.43  Index Matching       : 0.00
% 2.17/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
