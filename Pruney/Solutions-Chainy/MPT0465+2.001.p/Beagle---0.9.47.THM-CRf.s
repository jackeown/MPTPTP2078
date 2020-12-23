%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:48 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 112 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 196 expanded)
%              Number of equality atoms :    8 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k6_subset_1(k5_relat_1(A,B),k5_relat_1(A,C)),k5_relat_1(A,k6_subset_1(B,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(A,k2_xboole_0(B,C)) = k2_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [A_12,B_13] : k6_subset_1(A_12,B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_10,B_11] : m1_subset_1(k6_subset_1(A_10,B_11),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_10,B_11] : m1_subset_1(k4_xboole_0(A_10,B_11),k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10])).

tff(c_130,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_134,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k4_xboole_0(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_30,c_130])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_269,plain,(
    ! [A_87,B_88,C_89] :
      ( k2_xboole_0(k5_relat_1(A_87,B_88),k5_relat_1(A_87,C_89)) = k5_relat_1(A_87,k2_xboole_0(B_88,C_89))
      | ~ v1_relat_1(C_89)
      | ~ v1_relat_1(B_88)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_166,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_tarski(k4_xboole_0(A_63,B_64),C_65)
      | ~ r1_tarski(A_63,k2_xboole_0(B_64,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ~ r1_tarski(k6_subset_1(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3')),k5_relat_1('#skF_1',k6_subset_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_29,plain,(
    ~ r1_tarski(k4_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3')),k5_relat_1('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_22])).

tff(c_170,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k2_xboole_0(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_166,c_29])).

tff(c_284,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_3'))))
    | ~ v1_relat_1(k4_xboole_0('#skF_2','#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_170])).

tff(c_338,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',k2_xboole_0('#skF_3','#skF_2')))
    | ~ v1_relat_1(k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_4,c_284])).

tff(c_340,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_338])).

tff(c_343,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_134,c_340])).

tff(c_347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_343])).

tff(c_349,plain,(
    v1_relat_1(k4_xboole_0('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_135,plain,(
    ! [A_55,B_56] :
      ( v1_relat_1(k2_xboole_0(A_55,B_56))
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_138,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k2_xboole_0(A_3,B_4))
      | ~ v1_relat_1(k4_xboole_0(B_4,A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_135])).

tff(c_352,plain,
    ( v1_relat_1(k2_xboole_0('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_349,c_138])).

tff(c_355,plain,(
    v1_relat_1(k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_352])).

tff(c_42,plain,(
    ! [B_43,A_44] : k2_xboole_0(B_43,A_44) = k2_xboole_0(A_44,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_57,plain,(
    ! [A_44,B_43] : r1_tarski(A_44,k2_xboole_0(B_43,A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_8])).

tff(c_18,plain,(
    ! [C_25,A_19,B_23] :
      ( r1_tarski(k5_relat_1(C_25,A_19),k5_relat_1(C_25,B_23))
      | ~ r1_tarski(A_19,B_23)
      | ~ v1_relat_1(C_25)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_348,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1',k2_xboole_0('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_338])).

tff(c_358,plain,
    ( ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_xboole_0('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_348])).

tff(c_361,plain,(
    ~ v1_relat_1(k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_57,c_358])).

tff(c_363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_361])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:18:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.28  
% 2.20/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.28  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_subset_1 > k5_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.20/1.28  
% 2.20/1.28  %Foreground sorts:
% 2.20/1.28  
% 2.20/1.28  
% 2.20/1.28  %Background operators:
% 2.20/1.28  
% 2.20/1.28  
% 2.20/1.28  %Foreground operators:
% 2.20/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.20/1.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.20/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.28  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.20/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.20/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.20/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.28  
% 2.20/1.29  tff(f_85, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k6_subset_1(k5_relat_1(A, B), k5_relat_1(A, C)), k5_relat_1(A, k6_subset_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_relat_1)).
% 2.20/1.29  tff(f_39, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.20/1.29  tff(f_37, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 2.20/1.29  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.20/1.29  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.20/1.29  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(A, k2_xboole_0(B, C)) = k2_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_relat_1)).
% 2.20/1.29  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.20/1.29  tff(f_52, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_relat_1)).
% 2.20/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.20/1.29  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.20/1.29  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 2.20/1.29  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.20/1.29  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.20/1.29  tff(c_12, plain, (![A_12, B_13]: (k6_subset_1(A_12, B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.29  tff(c_10, plain, (![A_10, B_11]: (m1_subset_1(k6_subset_1(A_10, B_11), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.20/1.29  tff(c_30, plain, (![A_10, B_11]: (m1_subset_1(k4_xboole_0(A_10, B_11), k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10])).
% 2.20/1.29  tff(c_130, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.20/1.29  tff(c_134, plain, (![A_10, B_11]: (v1_relat_1(k4_xboole_0(A_10, B_11)) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_30, c_130])).
% 2.20/1.29  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.20/1.29  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.29  tff(c_269, plain, (![A_87, B_88, C_89]: (k2_xboole_0(k5_relat_1(A_87, B_88), k5_relat_1(A_87, C_89))=k5_relat_1(A_87, k2_xboole_0(B_88, C_89)) | ~v1_relat_1(C_89) | ~v1_relat_1(B_88) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.20/1.29  tff(c_166, plain, (![A_63, B_64, C_65]: (r1_tarski(k4_xboole_0(A_63, B_64), C_65) | ~r1_tarski(A_63, k2_xboole_0(B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.20/1.29  tff(c_22, plain, (~r1_tarski(k6_subset_1(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')), k5_relat_1('#skF_1', k6_subset_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.20/1.29  tff(c_29, plain, (~r1_tarski(k4_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')), k5_relat_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_22])).
% 2.20/1.29  tff(c_170, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k2_xboole_0(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_166, c_29])).
% 2.20/1.29  tff(c_284, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_3')))) | ~v1_relat_1(k4_xboole_0('#skF_2', '#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_269, c_170])).
% 2.20/1.29  tff(c_338, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))) | ~v1_relat_1(k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_4, c_284])).
% 2.20/1.29  tff(c_340, plain, (~v1_relat_1(k4_xboole_0('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_338])).
% 2.20/1.29  tff(c_343, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_134, c_340])).
% 2.20/1.30  tff(c_347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_343])).
% 2.20/1.30  tff(c_349, plain, (v1_relat_1(k4_xboole_0('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_338])).
% 2.20/1.30  tff(c_135, plain, (![A_55, B_56]: (v1_relat_1(k2_xboole_0(A_55, B_56)) | ~v1_relat_1(B_56) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.20/1.30  tff(c_138, plain, (![A_3, B_4]: (v1_relat_1(k2_xboole_0(A_3, B_4)) | ~v1_relat_1(k4_xboole_0(B_4, A_3)) | ~v1_relat_1(A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_135])).
% 2.20/1.30  tff(c_352, plain, (v1_relat_1(k2_xboole_0('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_349, c_138])).
% 2.20/1.30  tff(c_355, plain, (v1_relat_1(k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_352])).
% 2.20/1.30  tff(c_42, plain, (![B_43, A_44]: (k2_xboole_0(B_43, A_44)=k2_xboole_0(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.20/1.30  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.30  tff(c_57, plain, (![A_44, B_43]: (r1_tarski(A_44, k2_xboole_0(B_43, A_44)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_8])).
% 2.20/1.30  tff(c_18, plain, (![C_25, A_19, B_23]: (r1_tarski(k5_relat_1(C_25, A_19), k5_relat_1(C_25, B_23)) | ~r1_tarski(A_19, B_23) | ~v1_relat_1(C_25) | ~v1_relat_1(B_23) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.20/1.30  tff(c_348, plain, (~r1_tarski(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', k2_xboole_0('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_338])).
% 2.20/1.30  tff(c_358, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_xboole_0('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_348])).
% 2.20/1.30  tff(c_361, plain, (~v1_relat_1(k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_57, c_358])).
% 2.20/1.30  tff(c_363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_355, c_361])).
% 2.20/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.30  
% 2.20/1.30  Inference rules
% 2.20/1.30  ----------------------
% 2.20/1.30  #Ref     : 0
% 2.20/1.30  #Sup     : 85
% 2.20/1.30  #Fact    : 0
% 2.20/1.30  #Define  : 0
% 2.20/1.30  #Split   : 1
% 2.20/1.30  #Chain   : 0
% 2.20/1.30  #Close   : 0
% 2.20/1.30  
% 2.20/1.30  Ordering : KBO
% 2.20/1.30  
% 2.20/1.30  Simplification rules
% 2.20/1.30  ----------------------
% 2.20/1.30  #Subsume      : 3
% 2.20/1.30  #Demod        : 31
% 2.20/1.30  #Tautology    : 33
% 2.20/1.30  #SimpNegUnit  : 0
% 2.20/1.30  #BackRed      : 0
% 2.20/1.30  
% 2.20/1.30  #Partial instantiations: 0
% 2.20/1.30  #Strategies tried      : 1
% 2.20/1.30  
% 2.20/1.30  Timing (in seconds)
% 2.20/1.30  ----------------------
% 2.20/1.30  Preprocessing        : 0.30
% 2.20/1.30  Parsing              : 0.16
% 2.20/1.30  CNF conversion       : 0.02
% 2.20/1.30  Main loop            : 0.24
% 2.20/1.30  Inferencing          : 0.08
% 2.20/1.30  Reduction            : 0.08
% 2.20/1.30  Demodulation         : 0.07
% 2.20/1.30  BG Simplification    : 0.01
% 2.20/1.30  Subsumption          : 0.05
% 2.20/1.30  Abstraction          : 0.01
% 2.20/1.30  MUC search           : 0.00
% 2.20/1.30  Cooper               : 0.00
% 2.20/1.30  Total                : 0.57
% 2.20/1.30  Index Insertion      : 0.00
% 2.20/1.30  Index Deletion       : 0.00
% 2.20/1.30  Index Matching       : 0.00
% 2.20/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
