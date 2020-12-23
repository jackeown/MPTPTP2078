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
% DateTime   : Thu Dec  3 09:58:44 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 100 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 161 expanded)
%              Number of equality atoms :    4 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

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

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [A_36,B_37] : r1_tarski(k3_xboole_0(A_36,B_37),A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6])).

tff(c_87,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_84])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_101,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_106,plain,(
    ! [A_42,B_43] :
      ( v1_relat_1(A_42)
      | ~ v1_relat_1(B_43)
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_12,c_101])).

tff(c_116,plain,(
    ! [B_2,A_1] :
      ( v1_relat_1(k3_xboole_0(B_2,A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_87,c_106])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_307,plain,(
    ! [C_64,A_65,B_66] :
      ( r1_tarski(k5_relat_1(C_64,A_65),k5_relat_1(C_64,B_66))
      | ~ r1_tarski(A_65,B_66)
      | ~ v1_relat_1(C_64)
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_75,plain,(
    ! [A_34,B_35] : r1_tarski(k3_xboole_0(A_34,B_35),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6])).

tff(c_216,plain,(
    ! [C_57,A_58,B_59] :
      ( r1_tarski(k5_relat_1(C_57,A_58),k5_relat_1(C_57,B_59))
      | ~ r1_tarski(A_58,B_59)
      | ~ v1_relat_1(C_57)
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_126,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_tarski(A_46,k3_xboole_0(B_47,C_48))
      | ~ r1_tarski(A_46,C_48)
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_25,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_18])).

tff(c_140,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_126,c_25])).

tff(c_152,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_219,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_216,c_152])).

tff(c_225,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24,c_75,c_219])).

tff(c_229,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_116,c_225])).

tff(c_236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_229])).

tff(c_237,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_310,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_307,c_237])).

tff(c_316,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_87,c_310])).

tff(c_320,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_116,c_316])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:03:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.27  
% 2.05/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.27  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.05/1.27  
% 2.05/1.27  %Foreground sorts:
% 2.05/1.27  
% 2.05/1.27  
% 2.05/1.27  %Background operators:
% 2.05/1.27  
% 2.05/1.27  
% 2.05/1.27  %Foreground operators:
% 2.05/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.05/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.05/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.05/1.27  
% 2.05/1.28  tff(f_71, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 2.05/1.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.05/1.28  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.05/1.28  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.05/1.28  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.05/1.28  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.05/1.28  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 2.05/1.28  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.05/1.28  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.28  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.05/1.28  tff(c_66, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.05/1.28  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.28  tff(c_84, plain, (![A_36, B_37]: (r1_tarski(k3_xboole_0(A_36, B_37), A_36))), inference(superposition, [status(thm), theory('equality')], [c_66, c_6])).
% 2.05/1.28  tff(c_87, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_84])).
% 2.05/1.28  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.05/1.28  tff(c_101, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.05/1.28  tff(c_106, plain, (![A_42, B_43]: (v1_relat_1(A_42) | ~v1_relat_1(B_43) | ~r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_12, c_101])).
% 2.05/1.28  tff(c_116, plain, (![B_2, A_1]: (v1_relat_1(k3_xboole_0(B_2, A_1)) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_87, c_106])).
% 2.05/1.28  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.28  tff(c_307, plain, (![C_64, A_65, B_66]: (r1_tarski(k5_relat_1(C_64, A_65), k5_relat_1(C_64, B_66)) | ~r1_tarski(A_65, B_66) | ~v1_relat_1(C_64) | ~v1_relat_1(B_66) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.05/1.28  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.28  tff(c_75, plain, (![A_34, B_35]: (r1_tarski(k3_xboole_0(A_34, B_35), A_34))), inference(superposition, [status(thm), theory('equality')], [c_66, c_6])).
% 2.05/1.28  tff(c_216, plain, (![C_57, A_58, B_59]: (r1_tarski(k5_relat_1(C_57, A_58), k5_relat_1(C_57, B_59)) | ~r1_tarski(A_58, B_59) | ~v1_relat_1(C_57) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.05/1.28  tff(c_126, plain, (![A_46, B_47, C_48]: (r1_tarski(A_46, k3_xboole_0(B_47, C_48)) | ~r1_tarski(A_46, C_48) | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.05/1.28  tff(c_18, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.05/1.28  tff(c_25, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_18])).
% 2.05/1.28  tff(c_140, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_126, c_25])).
% 2.05/1.28  tff(c_152, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_140])).
% 2.05/1.28  tff(c_219, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_216, c_152])).
% 2.05/1.28  tff(c_225, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24, c_75, c_219])).
% 2.05/1.28  tff(c_229, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_116, c_225])).
% 2.05/1.28  tff(c_236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_229])).
% 2.05/1.28  tff(c_237, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_140])).
% 2.05/1.28  tff(c_310, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_307, c_237])).
% 2.05/1.28  tff(c_316, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_87, c_310])).
% 2.05/1.28  tff(c_320, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_116, c_316])).
% 2.05/1.28  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_320])).
% 2.05/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.28  
% 2.05/1.28  Inference rules
% 2.05/1.28  ----------------------
% 2.05/1.28  #Ref     : 0
% 2.05/1.28  #Sup     : 72
% 2.05/1.28  #Fact    : 0
% 2.05/1.28  #Define  : 0
% 2.05/1.28  #Split   : 2
% 2.05/1.28  #Chain   : 0
% 2.05/1.28  #Close   : 0
% 2.05/1.28  
% 2.05/1.28  Ordering : KBO
% 2.05/1.28  
% 2.05/1.28  Simplification rules
% 2.05/1.28  ----------------------
% 2.05/1.28  #Subsume      : 12
% 2.05/1.28  #Demod        : 23
% 2.05/1.28  #Tautology    : 36
% 2.05/1.28  #SimpNegUnit  : 0
% 2.05/1.28  #BackRed      : 0
% 2.05/1.28  
% 2.05/1.28  #Partial instantiations: 0
% 2.05/1.28  #Strategies tried      : 1
% 2.05/1.28  
% 2.05/1.28  Timing (in seconds)
% 2.05/1.28  ----------------------
% 2.05/1.29  Preprocessing        : 0.29
% 2.05/1.29  Parsing              : 0.16
% 2.05/1.29  CNF conversion       : 0.02
% 2.05/1.29  Main loop            : 0.23
% 2.05/1.29  Inferencing          : 0.08
% 2.05/1.29  Reduction            : 0.08
% 2.05/1.29  Demodulation         : 0.07
% 2.05/1.29  BG Simplification    : 0.01
% 2.05/1.29  Subsumption          : 0.04
% 2.05/1.29  Abstraction          : 0.01
% 2.05/1.29  MUC search           : 0.00
% 2.05/1.29  Cooper               : 0.00
% 2.05/1.29  Total                : 0.54
% 2.05/1.29  Index Insertion      : 0.00
% 2.05/1.29  Index Deletion       : 0.00
% 2.05/1.29  Index Matching       : 0.00
% 2.05/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
