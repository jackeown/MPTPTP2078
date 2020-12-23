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
% DateTime   : Thu Dec  3 10:28:21 EST 2020

% Result     : Theorem 4.50s
% Output     : CNFRefutation 4.61s
% Verified   : 
% Statistics : Number of formulae       :   57 (  78 expanded)
%              Number of leaves         :   29 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 (  94 expanded)
%              Number of equality atoms :   30 (  46 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_90,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_98,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_88,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_111,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_193,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | k4_xboole_0(A_63,B_64) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_52,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_201,plain,(
    k4_xboole_0('#skF_5','#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_193,c_52])).

tff(c_40,plain,(
    ! [B_31,A_30] : k2_tarski(B_31,A_30) = k2_tarski(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_115,plain,(
    ! [A_57,B_58] : k1_setfam_1(k2_tarski(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_293,plain,(
    ! [B_72,A_73] : k1_setfam_1(k2_tarski(B_72,A_73)) = k3_xboole_0(A_73,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_115])).

tff(c_48,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_299,plain,(
    ! [B_72,A_73] : k3_xboole_0(B_72,A_73) = k3_xboole_0(A_73,B_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_48])).

tff(c_424,plain,(
    ! [A_93,B_94] : k4_xboole_0(A_93,k4_xboole_0(A_93,B_94)) = k3_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    ! [A_25,B_26] : r1_tarski(k4_xboole_0(A_25,B_26),A_25) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_130,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k1_xboole_0
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_140,plain,(
    ! [A_25,B_26] : k4_xboole_0(k4_xboole_0(A_25,B_26),A_25) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_130])).

tff(c_980,plain,(
    ! [A_152,B_153] : k4_xboole_0(k3_xboole_0(A_152,B_153),A_152) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_140])).

tff(c_1009,plain,(
    ! [B_72,A_73] : k4_xboole_0(k3_xboole_0(B_72,A_73),A_73) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_980])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_56,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | k4_xboole_0(A_22,B_23) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1062,plain,(
    ! [B_156,A_157] :
      ( B_156 = A_157
      | ~ r1_tarski(A_157,B_156)
      | ~ v1_zfmisc_1(B_156)
      | v1_xboole_0(B_156)
      | v1_xboole_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3676,plain,(
    ! [B_280,A_281] :
      ( B_280 = A_281
      | ~ v1_zfmisc_1(B_280)
      | v1_xboole_0(B_280)
      | v1_xboole_0(A_281)
      | k4_xboole_0(A_281,B_280) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_1062])).

tff(c_3678,plain,(
    ! [A_281] :
      ( A_281 = '#skF_5'
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_281)
      | k4_xboole_0(A_281,'#skF_5') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_3676])).

tff(c_3774,plain,(
    ! [A_286] :
      ( A_286 = '#skF_5'
      | v1_xboole_0(A_286)
      | k4_xboole_0(A_286,'#skF_5') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_3678])).

tff(c_54,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_316,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_54])).

tff(c_3805,plain,
    ( k3_xboole_0('#skF_6','#skF_5') = '#skF_5'
    | k4_xboole_0(k3_xboole_0('#skF_6','#skF_5'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3774,c_316])).

tff(c_3823,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_3805])).

tff(c_433,plain,(
    ! [A_93,B_94] : k4_xboole_0(k3_xboole_0(A_93,B_94),A_93) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_140])).

tff(c_3878,plain,(
    k4_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3823,c_433])).

tff(c_3919,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_3878])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.50/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.84  
% 4.50/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.50/1.84  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.50/1.84  
% 4.50/1.84  %Foreground sorts:
% 4.50/1.84  
% 4.50/1.84  
% 4.50/1.84  %Background operators:
% 4.50/1.84  
% 4.50/1.84  
% 4.50/1.84  %Foreground operators:
% 4.50/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.50/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.50/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.50/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.50/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.50/1.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.50/1.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.50/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.50/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.50/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.50/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.50/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.50/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.50/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.50/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.50/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.50/1.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.50/1.84  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.50/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.50/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.50/1.84  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.50/1.84  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.50/1.84  
% 4.61/1.85  tff(f_80, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.61/1.85  tff(f_123, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 4.61/1.85  tff(f_90, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.61/1.85  tff(f_98, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.61/1.85  tff(f_88, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.61/1.85  tff(f_84, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.61/1.85  tff(f_111, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 4.61/1.85  tff(c_193, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | k4_xboole_0(A_63, B_64)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.61/1.85  tff(c_52, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.61/1.85  tff(c_201, plain, (k4_xboole_0('#skF_5', '#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_193, c_52])).
% 4.61/1.85  tff(c_40, plain, (![B_31, A_30]: (k2_tarski(B_31, A_30)=k2_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.61/1.85  tff(c_115, plain, (![A_57, B_58]: (k1_setfam_1(k2_tarski(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.61/1.85  tff(c_293, plain, (![B_72, A_73]: (k1_setfam_1(k2_tarski(B_72, A_73))=k3_xboole_0(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_40, c_115])).
% 4.61/1.85  tff(c_48, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.61/1.85  tff(c_299, plain, (![B_72, A_73]: (k3_xboole_0(B_72, A_73)=k3_xboole_0(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_293, c_48])).
% 4.61/1.85  tff(c_424, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k4_xboole_0(A_93, B_94))=k3_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.61/1.85  tff(c_34, plain, (![A_25, B_26]: (r1_tarski(k4_xboole_0(A_25, B_26), A_25))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.61/1.85  tff(c_130, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k1_xboole_0 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.61/1.85  tff(c_140, plain, (![A_25, B_26]: (k4_xboole_0(k4_xboole_0(A_25, B_26), A_25)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_130])).
% 4.61/1.85  tff(c_980, plain, (![A_152, B_153]: (k4_xboole_0(k3_xboole_0(A_152, B_153), A_152)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_424, c_140])).
% 4.61/1.85  tff(c_1009, plain, (![B_72, A_73]: (k4_xboole_0(k3_xboole_0(B_72, A_73), A_73)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_299, c_980])).
% 4.61/1.85  tff(c_58, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.61/1.85  tff(c_56, plain, (v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.61/1.85  tff(c_28, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | k4_xboole_0(A_22, B_23)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.61/1.85  tff(c_1062, plain, (![B_156, A_157]: (B_156=A_157 | ~r1_tarski(A_157, B_156) | ~v1_zfmisc_1(B_156) | v1_xboole_0(B_156) | v1_xboole_0(A_157))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.61/1.85  tff(c_3676, plain, (![B_280, A_281]: (B_280=A_281 | ~v1_zfmisc_1(B_280) | v1_xboole_0(B_280) | v1_xboole_0(A_281) | k4_xboole_0(A_281, B_280)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_1062])).
% 4.61/1.85  tff(c_3678, plain, (![A_281]: (A_281='#skF_5' | v1_xboole_0('#skF_5') | v1_xboole_0(A_281) | k4_xboole_0(A_281, '#skF_5')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_3676])).
% 4.61/1.85  tff(c_3774, plain, (![A_286]: (A_286='#skF_5' | v1_xboole_0(A_286) | k4_xboole_0(A_286, '#skF_5')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_58, c_3678])).
% 4.61/1.85  tff(c_54, plain, (~v1_xboole_0(k3_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.61/1.85  tff(c_316, plain, (~v1_xboole_0(k3_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_299, c_54])).
% 4.61/1.85  tff(c_3805, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_5' | k4_xboole_0(k3_xboole_0('#skF_6', '#skF_5'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_3774, c_316])).
% 4.61/1.85  tff(c_3823, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_3805])).
% 4.61/1.85  tff(c_433, plain, (![A_93, B_94]: (k4_xboole_0(k3_xboole_0(A_93, B_94), A_93)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_424, c_140])).
% 4.61/1.85  tff(c_3878, plain, (k4_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3823, c_433])).
% 4.61/1.85  tff(c_3919, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_3878])).
% 4.61/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.61/1.85  
% 4.61/1.85  Inference rules
% 4.61/1.85  ----------------------
% 4.61/1.85  #Ref     : 1
% 4.61/1.85  #Sup     : 945
% 4.61/1.85  #Fact    : 0
% 4.61/1.85  #Define  : 0
% 4.61/1.85  #Split   : 3
% 4.61/1.85  #Chain   : 0
% 4.61/1.85  #Close   : 0
% 4.61/1.85  
% 4.61/1.85  Ordering : KBO
% 4.61/1.85  
% 4.61/1.85  Simplification rules
% 4.61/1.85  ----------------------
% 4.61/1.85  #Subsume      : 302
% 4.61/1.85  #Demod        : 329
% 4.61/1.85  #Tautology    : 370
% 4.61/1.85  #SimpNegUnit  : 22
% 4.61/1.85  #BackRed      : 24
% 4.61/1.85  
% 4.61/1.85  #Partial instantiations: 0
% 4.61/1.85  #Strategies tried      : 1
% 4.61/1.85  
% 4.61/1.85  Timing (in seconds)
% 4.61/1.85  ----------------------
% 4.61/1.86  Preprocessing        : 0.35
% 4.61/1.86  Parsing              : 0.19
% 4.61/1.86  CNF conversion       : 0.02
% 4.61/1.86  Main loop            : 0.74
% 4.61/1.86  Inferencing          : 0.24
% 4.61/1.86  Reduction            : 0.27
% 4.61/1.86  Demodulation         : 0.19
% 4.61/1.86  BG Simplification    : 0.03
% 4.61/1.86  Subsumption          : 0.14
% 4.61/1.86  Abstraction          : 0.04
% 4.61/1.86  MUC search           : 0.00
% 4.61/1.86  Cooper               : 0.00
% 4.61/1.86  Total                : 1.12
% 4.61/1.86  Index Insertion      : 0.00
% 4.61/1.86  Index Deletion       : 0.00
% 4.61/1.86  Index Matching       : 0.00
% 4.61/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
