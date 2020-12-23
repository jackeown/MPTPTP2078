%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:17 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   50 (  56 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  55 expanded)
%              Number of equality atoms :   25 (  30 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(B_35,A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_101])).

tff(c_8,plain,(
    ! [A_7,B_8] : k1_setfam_1(k2_tarski(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_157,plain,(
    ! [B_38,A_39] : k3_xboole_0(B_38,A_39) = k3_xboole_0(A_39,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_8])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_83,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_83])).

tff(c_92,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_96,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_91,c_92])).

tff(c_172,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_96])).

tff(c_20,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [B_17,A_16] : k5_relat_1(k6_relat_1(B_17),k6_relat_1(A_16)) = k6_relat_1(k3_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_210,plain,(
    ! [B_40,A_41] :
      ( k9_relat_1(B_40,k2_relat_1(A_41)) = k2_relat_1(k5_relat_1(A_41,B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_219,plain,(
    ! [A_14,B_40] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_14),B_40)) = k9_relat_1(B_40,A_14)
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_210])).

tff(c_224,plain,(
    ! [A_42,B_43] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_42),B_43)) = k9_relat_1(B_43,A_42)
      | ~ v1_relat_1(B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_219])).

tff(c_236,plain,(
    ! [A_16,B_17] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_16,B_17))) = k9_relat_1(k6_relat_1(A_16),B_17)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_224])).

tff(c_240,plain,(
    ! [A_16,B_17] : k9_relat_1(k6_relat_1(A_16),B_17) = k3_xboole_0(A_16,B_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_236])).

tff(c_26,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_241,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_26])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:12:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.26  
% 1.93/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.26  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.93/1.26  
% 1.93/1.26  %Foreground sorts:
% 1.93/1.26  
% 1.93/1.26  
% 1.93/1.26  %Background operators:
% 1.93/1.26  
% 1.93/1.26  
% 1.93/1.26  %Foreground operators:
% 1.93/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.26  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.93/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.93/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.93/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.93/1.26  
% 1.93/1.27  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.93/1.27  tff(f_35, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.93/1.27  tff(f_61, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.93/1.27  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.93/1.27  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.93/1.27  tff(f_54, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.93/1.27  tff(f_50, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.93/1.27  tff(f_56, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.93/1.27  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 1.93/1.27  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.27  tff(c_101, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.27  tff(c_125, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(B_35, A_34))), inference(superposition, [status(thm), theory('equality')], [c_4, c_101])).
% 1.93/1.27  tff(c_8, plain, (![A_7, B_8]: (k1_setfam_1(k2_tarski(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.27  tff(c_157, plain, (![B_38, A_39]: (k3_xboole_0(B_38, A_39)=k3_xboole_0(A_39, B_38))), inference(superposition, [status(thm), theory('equality')], [c_125, c_8])).
% 1.93/1.27  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.93/1.27  tff(c_83, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.27  tff(c_91, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_83])).
% 1.93/1.27  tff(c_92, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.27  tff(c_96, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_91, c_92])).
% 1.93/1.27  tff(c_172, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_157, c_96])).
% 1.93/1.27  tff(c_20, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.93/1.27  tff(c_18, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.27  tff(c_24, plain, (![B_17, A_16]: (k5_relat_1(k6_relat_1(B_17), k6_relat_1(A_16))=k6_relat_1(k3_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.27  tff(c_210, plain, (![B_40, A_41]: (k9_relat_1(B_40, k2_relat_1(A_41))=k2_relat_1(k5_relat_1(A_41, B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.93/1.27  tff(c_219, plain, (![A_14, B_40]: (k2_relat_1(k5_relat_1(k6_relat_1(A_14), B_40))=k9_relat_1(B_40, A_14) | ~v1_relat_1(B_40) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_210])).
% 1.93/1.27  tff(c_224, plain, (![A_42, B_43]: (k2_relat_1(k5_relat_1(k6_relat_1(A_42), B_43))=k9_relat_1(B_43, A_42) | ~v1_relat_1(B_43))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_219])).
% 1.93/1.27  tff(c_236, plain, (![A_16, B_17]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_16, B_17)))=k9_relat_1(k6_relat_1(A_16), B_17) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_224])).
% 1.93/1.27  tff(c_240, plain, (![A_16, B_17]: (k9_relat_1(k6_relat_1(A_16), B_17)=k3_xboole_0(A_16, B_17))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_236])).
% 1.93/1.27  tff(c_26, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.93/1.27  tff(c_241, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_240, c_26])).
% 1.93/1.27  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172, c_241])).
% 1.93/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.27  
% 1.93/1.27  Inference rules
% 1.93/1.27  ----------------------
% 1.93/1.27  #Ref     : 0
% 1.93/1.27  #Sup     : 52
% 1.93/1.27  #Fact    : 0
% 1.93/1.27  #Define  : 0
% 1.93/1.27  #Split   : 0
% 1.93/1.27  #Chain   : 0
% 1.93/1.27  #Close   : 0
% 1.93/1.27  
% 1.93/1.27  Ordering : KBO
% 1.93/1.27  
% 1.93/1.27  Simplification rules
% 1.93/1.27  ----------------------
% 1.93/1.27  #Subsume      : 1
% 1.93/1.27  #Demod        : 11
% 1.93/1.27  #Tautology    : 43
% 1.93/1.27  #SimpNegUnit  : 0
% 1.93/1.27  #BackRed      : 1
% 1.93/1.27  
% 1.93/1.27  #Partial instantiations: 0
% 1.93/1.27  #Strategies tried      : 1
% 1.93/1.27  
% 1.93/1.27  Timing (in seconds)
% 1.93/1.27  ----------------------
% 1.93/1.27  Preprocessing        : 0.31
% 1.93/1.27  Parsing              : 0.17
% 1.93/1.28  CNF conversion       : 0.02
% 1.93/1.28  Main loop            : 0.15
% 1.93/1.28  Inferencing          : 0.06
% 1.93/1.28  Reduction            : 0.05
% 1.93/1.28  Demodulation         : 0.04
% 1.93/1.28  BG Simplification    : 0.01
% 1.93/1.28  Subsumption          : 0.02
% 1.93/1.28  Abstraction          : 0.01
% 1.93/1.28  MUC search           : 0.00
% 1.93/1.28  Cooper               : 0.00
% 1.93/1.28  Total                : 0.49
% 1.93/1.28  Index Insertion      : 0.00
% 1.93/1.28  Index Deletion       : 0.00
% 1.93/1.28  Index Matching       : 0.00
% 1.93/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
