%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:43 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 144 expanded)
%              Number of leaves         :   24 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 221 expanded)
%              Number of equality atoms :    8 (  60 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

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

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,(
    ! [B_42,A_43] : k1_setfam_1(k2_tarski(B_42,A_43)) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_83])).

tff(c_16,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,(
    ! [B_42,A_43] : k3_xboole_0(B_42,A_43) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_16])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_tarski(A_46,B_47)
      | ~ r1_tarski(A_46,k3_xboole_0(B_47,C_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_167,plain,(
    ! [B_47,C_48] : r1_tarski(k3_xboole_0(B_47,C_48),B_47) ),
    inference(resolution,[status(thm)],[c_6,c_156])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_283,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_288,plain,(
    ! [A_66,B_67] :
      ( v1_relat_1(A_66)
      | ~ v1_relat_1(B_67)
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(resolution,[status(thm)],[c_20,c_283])).

tff(c_313,plain,(
    ! [B_68,C_69] :
      ( v1_relat_1(k3_xboole_0(B_68,C_69))
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_167,c_288])).

tff(c_316,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(k3_xboole_0(B_42,A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_313])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_175,plain,(
    ! [B_51,C_52] : r1_tarski(k3_xboole_0(B_51,C_52),B_51) ),
    inference(resolution,[status(thm)],[c_6,c_156])).

tff(c_184,plain,(
    ! [B_42,A_43] : r1_tarski(k3_xboole_0(B_42,A_43),A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_175])).

tff(c_24,plain,(
    ! [C_26,A_20,B_24] :
      ( r1_tarski(k5_relat_1(C_26,A_20),k5_relat_1(C_26,B_24))
      | ~ r1_tarski(A_20,B_24)
      | ~ v1_relat_1(C_26)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_327,plain,(
    ! [A_72,B_73,C_74] :
      ( r1_tarski(A_72,k3_xboole_0(B_73,C_74))
      | ~ r1_tarski(A_72,C_74)
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_121,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_104,c_26])).

tff(c_346,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_327,c_121])).

tff(c_441,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_346])).

tff(c_705,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_441])).

tff(c_708,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_167,c_705])).

tff(c_711,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_316,c_708])).

tff(c_718,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_711])).

tff(c_719,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_346])).

tff(c_1648,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_719])).

tff(c_1651,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_184,c_1648])).

tff(c_1654,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_316,c_1651])).

tff(c_1661,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1654])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:48:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.56  
% 3.22/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.57  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.22/1.57  
% 3.22/1.57  %Foreground sorts:
% 3.22/1.57  
% 3.22/1.57  
% 3.22/1.57  %Background operators:
% 3.22/1.57  
% 3.22/1.57  
% 3.22/1.57  %Foreground operators:
% 3.22/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.22/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.22/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.22/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.22/1.57  
% 3.22/1.58  tff(f_81, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 3.22/1.58  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.22/1.58  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.22/1.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.22/1.58  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.22/1.58  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.22/1.58  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.22/1.58  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 3.22/1.58  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.22/1.58  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.22/1.58  tff(c_12, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.22/1.58  tff(c_83, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.58  tff(c_98, plain, (![B_42, A_43]: (k1_setfam_1(k2_tarski(B_42, A_43))=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_12, c_83])).
% 3.22/1.58  tff(c_16, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.22/1.58  tff(c_104, plain, (![B_42, A_43]: (k3_xboole_0(B_42, A_43)=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_98, c_16])).
% 3.22/1.58  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.58  tff(c_156, plain, (![A_46, B_47, C_48]: (r1_tarski(A_46, B_47) | ~r1_tarski(A_46, k3_xboole_0(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.22/1.58  tff(c_167, plain, (![B_47, C_48]: (r1_tarski(k3_xboole_0(B_47, C_48), B_47))), inference(resolution, [status(thm)], [c_6, c_156])).
% 3.22/1.58  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.22/1.58  tff(c_283, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.22/1.58  tff(c_288, plain, (![A_66, B_67]: (v1_relat_1(A_66) | ~v1_relat_1(B_67) | ~r1_tarski(A_66, B_67))), inference(resolution, [status(thm)], [c_20, c_283])).
% 3.22/1.58  tff(c_313, plain, (![B_68, C_69]: (v1_relat_1(k3_xboole_0(B_68, C_69)) | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_167, c_288])).
% 3.22/1.58  tff(c_316, plain, (![B_42, A_43]: (v1_relat_1(k3_xboole_0(B_42, A_43)) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_104, c_313])).
% 3.22/1.58  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.22/1.58  tff(c_175, plain, (![B_51, C_52]: (r1_tarski(k3_xboole_0(B_51, C_52), B_51))), inference(resolution, [status(thm)], [c_6, c_156])).
% 3.22/1.58  tff(c_184, plain, (![B_42, A_43]: (r1_tarski(k3_xboole_0(B_42, A_43), A_43))), inference(superposition, [status(thm), theory('equality')], [c_104, c_175])).
% 3.22/1.58  tff(c_24, plain, (![C_26, A_20, B_24]: (r1_tarski(k5_relat_1(C_26, A_20), k5_relat_1(C_26, B_24)) | ~r1_tarski(A_20, B_24) | ~v1_relat_1(C_26) | ~v1_relat_1(B_24) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.22/1.58  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.22/1.58  tff(c_327, plain, (![A_72, B_73, C_74]: (r1_tarski(A_72, k3_xboole_0(B_73, C_74)) | ~r1_tarski(A_72, C_74) | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.22/1.58  tff(c_26, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.22/1.58  tff(c_121, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_104, c_26])).
% 3.22/1.58  tff(c_346, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_327, c_121])).
% 3.22/1.58  tff(c_441, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_346])).
% 3.22/1.58  tff(c_705, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_441])).
% 3.22/1.58  tff(c_708, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_167, c_705])).
% 3.22/1.58  tff(c_711, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_316, c_708])).
% 3.22/1.58  tff(c_718, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_711])).
% 3.22/1.58  tff(c_719, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_346])).
% 3.22/1.58  tff(c_1648, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_719])).
% 3.22/1.58  tff(c_1651, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_184, c_1648])).
% 3.22/1.58  tff(c_1654, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_316, c_1651])).
% 3.22/1.58  tff(c_1661, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1654])).
% 3.22/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/1.58  
% 3.22/1.58  Inference rules
% 3.22/1.58  ----------------------
% 3.22/1.58  #Ref     : 0
% 3.22/1.58  #Sup     : 403
% 3.22/1.58  #Fact    : 0
% 3.22/1.58  #Define  : 0
% 3.22/1.58  #Split   : 1
% 3.22/1.58  #Chain   : 0
% 3.22/1.58  #Close   : 0
% 3.22/1.58  
% 3.22/1.58  Ordering : KBO
% 3.22/1.58  
% 3.22/1.58  Simplification rules
% 3.22/1.58  ----------------------
% 3.22/1.58  #Subsume      : 72
% 3.22/1.58  #Demod        : 182
% 3.22/1.58  #Tautology    : 177
% 3.22/1.58  #SimpNegUnit  : 0
% 3.22/1.58  #BackRed      : 1
% 3.22/1.58  
% 3.22/1.58  #Partial instantiations: 0
% 3.22/1.58  #Strategies tried      : 1
% 3.22/1.58  
% 3.22/1.58  Timing (in seconds)
% 3.22/1.58  ----------------------
% 3.22/1.58  Preprocessing        : 0.31
% 3.22/1.58  Parsing              : 0.17
% 3.22/1.58  CNF conversion       : 0.02
% 3.22/1.58  Main loop            : 0.43
% 3.22/1.58  Inferencing          : 0.14
% 3.22/1.58  Reduction            : 0.16
% 3.22/1.58  Demodulation         : 0.14
% 3.22/1.58  BG Simplification    : 0.02
% 3.22/1.58  Subsumption          : 0.08
% 3.22/1.58  Abstraction          : 0.02
% 3.22/1.58  MUC search           : 0.00
% 3.22/1.58  Cooper               : 0.00
% 3.22/1.58  Total                : 0.77
% 3.22/1.58  Index Insertion      : 0.00
% 3.22/1.58  Index Deletion       : 0.00
% 3.22/1.58  Index Matching       : 0.00
% 3.22/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
