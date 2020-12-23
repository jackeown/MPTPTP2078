%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:43 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 131 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 193 expanded)
%              Number of equality atoms :    8 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [A_36,B_37] : k1_setfam_1(k2_tarski(A_36,B_37)) = k3_xboole_0(B_37,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_59])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_86,plain,(
    ! [B_37,A_36] : k3_xboole_0(B_37,A_36) = k3_xboole_0(A_36,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_154,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_159,plain,(
    ! [A_44,B_45] :
      ( v1_relat_1(A_44)
      | ~ v1_relat_1(B_45)
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_12,c_154])).

tff(c_168,plain,(
    ! [A_46,B_47] :
      ( v1_relat_1(k3_xboole_0(A_46,B_47))
      | ~ v1_relat_1(A_46) ) ),
    inference(resolution,[status(thm)],[c_2,c_159])).

tff(c_171,plain,(
    ! [B_37,A_36] :
      ( v1_relat_1(k3_xboole_0(B_37,A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_168])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_104,plain,(
    ! [B_38,A_39] : k3_xboole_0(B_38,A_39) = k3_xboole_0(A_39,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_8])).

tff(c_119,plain,(
    ! [B_38,A_39] : r1_tarski(k3_xboole_0(B_38,A_39),A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_2])).

tff(c_16,plain,(
    ! [C_21,A_15,B_19] :
      ( r1_tarski(k5_relat_1(C_21,A_15),k5_relat_1(C_21,B_19))
      | ~ r1_tarski(A_15,B_19)
      | ~ v1_relat_1(C_21)
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_182,plain,(
    ! [A_50,B_51,C_52] :
      ( r1_tarski(A_50,k3_xboole_0(B_51,C_52))
      | ~ r1_tarski(A_50,C_52)
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_103,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_86,c_18])).

tff(c_195,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_182,c_103])).

tff(c_214,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_217,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_214])).

tff(c_220,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24,c_2,c_217])).

tff(c_223,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_171,c_220])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_223])).

tff(c_231,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_235,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_231])).

tff(c_238,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_119,c_235])).

tff(c_241,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_171,c_238])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.27  
% 1.99/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.27  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.99/1.27  
% 1.99/1.27  %Foreground sorts:
% 1.99/1.27  
% 1.99/1.27  
% 1.99/1.27  %Background operators:
% 1.99/1.27  
% 1.99/1.27  
% 1.99/1.27  %Foreground operators:
% 1.99/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.99/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.27  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.99/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.99/1.27  
% 1.99/1.28  tff(f_71, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 1.99/1.28  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.99/1.28  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.99/1.28  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.99/1.28  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.99/1.28  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.99/1.28  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 1.99/1.28  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.99/1.28  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.99/1.28  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.28  tff(c_59, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.28  tff(c_80, plain, (![A_36, B_37]: (k1_setfam_1(k2_tarski(A_36, B_37))=k3_xboole_0(B_37, A_36))), inference(superposition, [status(thm), theory('equality')], [c_6, c_59])).
% 1.99/1.28  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.28  tff(c_86, plain, (![B_37, A_36]: (k3_xboole_0(B_37, A_36)=k3_xboole_0(A_36, B_37))), inference(superposition, [status(thm), theory('equality')], [c_80, c_8])).
% 1.99/1.28  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.99/1.28  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.28  tff(c_154, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.99/1.28  tff(c_159, plain, (![A_44, B_45]: (v1_relat_1(A_44) | ~v1_relat_1(B_45) | ~r1_tarski(A_44, B_45))), inference(resolution, [status(thm)], [c_12, c_154])).
% 1.99/1.28  tff(c_168, plain, (![A_46, B_47]: (v1_relat_1(k3_xboole_0(A_46, B_47)) | ~v1_relat_1(A_46))), inference(resolution, [status(thm)], [c_2, c_159])).
% 1.99/1.28  tff(c_171, plain, (![B_37, A_36]: (v1_relat_1(k3_xboole_0(B_37, A_36)) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_86, c_168])).
% 1.99/1.28  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.99/1.28  tff(c_104, plain, (![B_38, A_39]: (k3_xboole_0(B_38, A_39)=k3_xboole_0(A_39, B_38))), inference(superposition, [status(thm), theory('equality')], [c_80, c_8])).
% 1.99/1.28  tff(c_119, plain, (![B_38, A_39]: (r1_tarski(k3_xboole_0(B_38, A_39), A_39))), inference(superposition, [status(thm), theory('equality')], [c_104, c_2])).
% 1.99/1.28  tff(c_16, plain, (![C_21, A_15, B_19]: (r1_tarski(k5_relat_1(C_21, A_15), k5_relat_1(C_21, B_19)) | ~r1_tarski(A_15, B_19) | ~v1_relat_1(C_21) | ~v1_relat_1(B_19) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.99/1.28  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.99/1.28  tff(c_182, plain, (![A_50, B_51, C_52]: (r1_tarski(A_50, k3_xboole_0(B_51, C_52)) | ~r1_tarski(A_50, C_52) | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.28  tff(c_18, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.99/1.28  tff(c_103, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_86, c_18])).
% 1.99/1.28  tff(c_195, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_182, c_103])).
% 1.99/1.28  tff(c_214, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_195])).
% 1.99/1.28  tff(c_217, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_214])).
% 1.99/1.28  tff(c_220, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24, c_2, c_217])).
% 1.99/1.28  tff(c_223, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_171, c_220])).
% 1.99/1.28  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_223])).
% 1.99/1.28  tff(c_231, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_195])).
% 1.99/1.28  tff(c_235, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_231])).
% 1.99/1.28  tff(c_238, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_119, c_235])).
% 1.99/1.28  tff(c_241, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_171, c_238])).
% 1.99/1.28  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_241])).
% 1.99/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.28  
% 1.99/1.28  Inference rules
% 1.99/1.28  ----------------------
% 1.99/1.28  #Ref     : 0
% 1.99/1.28  #Sup     : 53
% 1.99/1.28  #Fact    : 0
% 1.99/1.28  #Define  : 0
% 1.99/1.28  #Split   : 1
% 1.99/1.28  #Chain   : 0
% 1.99/1.28  #Close   : 0
% 1.99/1.28  
% 1.99/1.28  Ordering : KBO
% 1.99/1.28  
% 1.99/1.28  Simplification rules
% 1.99/1.29  ----------------------
% 1.99/1.29  #Subsume      : 11
% 1.99/1.29  #Demod        : 16
% 1.99/1.29  #Tautology    : 27
% 1.99/1.29  #SimpNegUnit  : 0
% 1.99/1.29  #BackRed      : 1
% 1.99/1.29  
% 1.99/1.29  #Partial instantiations: 0
% 1.99/1.29  #Strategies tried      : 1
% 1.99/1.29  
% 1.99/1.29  Timing (in seconds)
% 1.99/1.29  ----------------------
% 1.99/1.29  Preprocessing        : 0.29
% 1.99/1.29  Parsing              : 0.17
% 1.99/1.29  CNF conversion       : 0.02
% 1.99/1.29  Main loop            : 0.20
% 1.99/1.29  Inferencing          : 0.07
% 1.99/1.29  Reduction            : 0.07
% 1.99/1.29  Demodulation         : 0.06
% 1.99/1.29  BG Simplification    : 0.01
% 1.99/1.29  Subsumption          : 0.04
% 1.99/1.29  Abstraction          : 0.01
% 1.99/1.29  MUC search           : 0.00
% 1.99/1.29  Cooper               : 0.00
% 1.99/1.29  Total                : 0.52
% 1.99/1.29  Index Insertion      : 0.00
% 1.99/1.29  Index Deletion       : 0.00
% 1.99/1.29  Index Matching       : 0.00
% 1.99/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
