%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:39 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 107 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :   70 ( 144 expanded)
%              Number of equality atoms :    5 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_51,plain,(
    ! [A_48,B_49] : k2_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_51])).

tff(c_144,plain,(
    ! [A_75,B_76,C_77] : r1_tarski(k2_xboole_0(k3_xboole_0(A_75,B_76),k3_xboole_0(A_75,C_77)),k2_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_154,plain,(
    ! [A_75,A_1] : r1_tarski(k2_xboole_0(k3_xboole_0(A_75,A_1),k3_xboole_0(A_75,A_1)),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_144])).

tff(c_239,plain,(
    ! [A_90,A_91] : r1_tarski(k3_xboole_0(A_90,A_91),A_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_154])).

tff(c_26,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(A_35,k1_zfmisc_1(B_36))
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_96,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_100,plain,(
    ! [A_35,B_36] :
      ( v1_relat_1(A_35)
      | ~ v1_relat_1(B_36)
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_26,c_96])).

tff(c_246,plain,(
    ! [A_90,A_91] :
      ( v1_relat_1(k3_xboole_0(A_90,A_91))
      | ~ v1_relat_1(A_91) ) ),
    inference(resolution,[status(thm)],[c_239,c_100])).

tff(c_166,plain,(
    ! [A_75,A_1] : r1_tarski(k3_xboole_0(A_75,A_1),A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_154])).

tff(c_264,plain,(
    ! [A_96,B_97] :
      ( r1_tarski(k3_relat_1(A_96),k3_relat_1(B_97))
      | ~ r1_tarski(A_96,B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_182,plain,(
    ! [A_80,A_81] : r1_tarski(k3_xboole_0(A_80,A_81),A_81) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_154])).

tff(c_189,plain,(
    ! [A_80,A_81] :
      ( v1_relat_1(k3_xboole_0(A_80,A_81))
      | ~ v1_relat_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_182,c_100])).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_40,B_42] :
      ( r1_tarski(k3_relat_1(A_40),k3_relat_1(B_42))
      | ~ r1_tarski(A_40,B_42)
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_123,plain,(
    ! [A_68,B_69,C_70] :
      ( r1_tarski(A_68,k3_xboole_0(B_69,C_70))
      | ~ r1_tarski(A_68,C_70)
      | ~ r1_tarski(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_134,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_123,c_32])).

tff(c_168,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_210,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_168])).

tff(c_213,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4,c_210])).

tff(c_216,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_189,c_213])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_216])).

tff(c_224,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_267,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_264,c_224])).

tff(c_273,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_166,c_267])).

tff(c_277,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_246,c_273])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.24  
% 2.15/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.24  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 2.15/1.24  
% 2.15/1.24  %Foreground sorts:
% 2.15/1.24  
% 2.15/1.24  
% 2.15/1.24  %Background operators:
% 2.15/1.24  
% 2.15/1.24  
% 2.15/1.24  %Foreground operators:
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.24  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.15/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.15/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.15/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.15/1.24  
% 2.15/1.25  tff(f_79, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 2.15/1.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.15/1.25  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.15/1.25  tff(f_39, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.15/1.25  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.15/1.25  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.15/1.25  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 2.15/1.25  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.15/1.25  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.15/1.25  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.15/1.25  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.15/1.25  tff(c_51, plain, (![A_48, B_49]: (k2_xboole_0(A_48, k3_xboole_0(A_48, B_49))=A_48)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.25  tff(c_60, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_51])).
% 2.15/1.25  tff(c_144, plain, (![A_75, B_76, C_77]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_75, B_76), k3_xboole_0(A_75, C_77)), k2_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.15/1.25  tff(c_154, plain, (![A_75, A_1]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_75, A_1), k3_xboole_0(A_75, A_1)), A_1))), inference(superposition, [status(thm), theory('equality')], [c_60, c_144])).
% 2.15/1.25  tff(c_239, plain, (![A_90, A_91]: (r1_tarski(k3_xboole_0(A_90, A_91), A_91))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_154])).
% 2.15/1.25  tff(c_26, plain, (![A_35, B_36]: (m1_subset_1(A_35, k1_zfmisc_1(B_36)) | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.15/1.25  tff(c_96, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.15/1.25  tff(c_100, plain, (![A_35, B_36]: (v1_relat_1(A_35) | ~v1_relat_1(B_36) | ~r1_tarski(A_35, B_36))), inference(resolution, [status(thm)], [c_26, c_96])).
% 2.15/1.25  tff(c_246, plain, (![A_90, A_91]: (v1_relat_1(k3_xboole_0(A_90, A_91)) | ~v1_relat_1(A_91))), inference(resolution, [status(thm)], [c_239, c_100])).
% 2.15/1.25  tff(c_166, plain, (![A_75, A_1]: (r1_tarski(k3_xboole_0(A_75, A_1), A_1))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_154])).
% 2.15/1.25  tff(c_264, plain, (![A_96, B_97]: (r1_tarski(k3_relat_1(A_96), k3_relat_1(B_97)) | ~r1_tarski(A_96, B_97) | ~v1_relat_1(B_97) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.15/1.25  tff(c_182, plain, (![A_80, A_81]: (r1_tarski(k3_xboole_0(A_80, A_81), A_81))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_154])).
% 2.15/1.25  tff(c_189, plain, (![A_80, A_81]: (v1_relat_1(k3_xboole_0(A_80, A_81)) | ~v1_relat_1(A_81))), inference(resolution, [status(thm)], [c_182, c_100])).
% 2.15/1.25  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.15/1.25  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.15/1.25  tff(c_30, plain, (![A_40, B_42]: (r1_tarski(k3_relat_1(A_40), k3_relat_1(B_42)) | ~r1_tarski(A_40, B_42) | ~v1_relat_1(B_42) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.15/1.25  tff(c_123, plain, (![A_68, B_69, C_70]: (r1_tarski(A_68, k3_xboole_0(B_69, C_70)) | ~r1_tarski(A_68, C_70) | ~r1_tarski(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.15/1.25  tff(c_32, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.15/1.25  tff(c_134, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_123, c_32])).
% 2.15/1.25  tff(c_168, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_134])).
% 2.15/1.25  tff(c_210, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_168])).
% 2.15/1.25  tff(c_213, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4, c_210])).
% 2.15/1.25  tff(c_216, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_189, c_213])).
% 2.15/1.25  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_216])).
% 2.15/1.25  tff(c_224, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_134])).
% 2.15/1.25  tff(c_267, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_264, c_224])).
% 2.15/1.25  tff(c_273, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_166, c_267])).
% 2.15/1.25  tff(c_277, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_246, c_273])).
% 2.15/1.25  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_277])).
% 2.15/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.25  
% 2.15/1.25  Inference rules
% 2.15/1.25  ----------------------
% 2.15/1.25  #Ref     : 0
% 2.15/1.25  #Sup     : 55
% 2.15/1.25  #Fact    : 0
% 2.15/1.25  #Define  : 0
% 2.15/1.25  #Split   : 1
% 2.15/1.25  #Chain   : 0
% 2.15/1.25  #Close   : 0
% 2.15/1.25  
% 2.15/1.25  Ordering : KBO
% 2.15/1.25  
% 2.15/1.25  Simplification rules
% 2.15/1.25  ----------------------
% 2.15/1.25  #Subsume      : 0
% 2.15/1.25  #Demod        : 17
% 2.15/1.25  #Tautology    : 32
% 2.15/1.25  #SimpNegUnit  : 0
% 2.15/1.25  #BackRed      : 0
% 2.15/1.25  
% 2.15/1.25  #Partial instantiations: 0
% 2.15/1.25  #Strategies tried      : 1
% 2.15/1.25  
% 2.15/1.25  Timing (in seconds)
% 2.15/1.25  ----------------------
% 2.15/1.26  Preprocessing        : 0.31
% 2.15/1.26  Parsing              : 0.17
% 2.15/1.26  CNF conversion       : 0.02
% 2.15/1.26  Main loop            : 0.18
% 2.15/1.26  Inferencing          : 0.07
% 2.15/1.26  Reduction            : 0.06
% 2.15/1.26  Demodulation         : 0.04
% 2.15/1.26  BG Simplification    : 0.01
% 2.15/1.26  Subsumption          : 0.03
% 2.15/1.26  Abstraction          : 0.01
% 2.15/1.26  MUC search           : 0.00
% 2.15/1.26  Cooper               : 0.00
% 2.15/1.26  Total                : 0.52
% 2.15/1.26  Index Insertion      : 0.00
% 2.15/1.26  Index Deletion       : 0.00
% 2.15/1.26  Index Matching       : 0.00
% 2.15/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
