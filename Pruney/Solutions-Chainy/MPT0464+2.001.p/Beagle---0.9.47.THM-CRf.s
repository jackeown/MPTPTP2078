%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:43 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 139 expanded)
%              Number of leaves         :   27 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :   88 ( 211 expanded)
%              Number of equality atoms :    9 (  58 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ! [D] :
                  ( v1_relat_1(D)
                 => ( ( r1_tarski(A,B)
                      & r1_tarski(C,D) )
                   => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_85,plain,(
    ! [A_59,B_60] : k1_setfam_1(k2_tarski(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_105,plain,(
    ! [A_63,B_64] : k1_setfam_1(k2_tarski(A_63,B_64)) = k3_xboole_0(B_64,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_85])).

tff(c_22,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_111,plain,(
    ! [B_64,A_63] : k3_xboole_0(B_64,A_63) = k3_xboole_0(A_63,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_22])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_192,plain,(
    ! [B_71,A_72] :
      ( v1_relat_1(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_197,plain,(
    ! [A_73,B_74] :
      ( v1_relat_1(A_73)
      | ~ v1_relat_1(B_74)
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_26,c_192])).

tff(c_210,plain,(
    ! [A_75,B_76] :
      ( v1_relat_1(k3_xboole_0(A_75,B_76))
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_8,c_197])).

tff(c_213,plain,(
    ! [B_64,A_63] :
      ( v1_relat_1(k3_xboole_0(B_64,A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_210])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [B_65,A_66] : k3_xboole_0(B_65,A_66) = k3_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_22])).

tff(c_144,plain,(
    ! [B_65,A_66] : r1_tarski(k3_xboole_0(B_65,A_66),A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_8])).

tff(c_1410,plain,(
    ! [A_130,C_131,B_132,D_133] :
      ( r1_tarski(k5_relat_1(A_130,C_131),k5_relat_1(B_132,D_133))
      | ~ r1_tarski(C_131,D_133)
      | ~ r1_tarski(A_130,B_132)
      | ~ v1_relat_1(D_133)
      | ~ v1_relat_1(C_131)
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1125,plain,(
    ! [A_117,C_118,B_119,D_120] :
      ( r1_tarski(k5_relat_1(A_117,C_118),k5_relat_1(B_119,D_120))
      | ~ r1_tarski(C_118,D_120)
      | ~ r1_tarski(A_117,B_119)
      | ~ v1_relat_1(D_120)
      | ~ v1_relat_1(C_118)
      | ~ v1_relat_1(B_119)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_247,plain,(
    ! [A_86,B_87,C_88] :
      ( r1_tarski(A_86,k3_xboole_0(B_87,C_88))
      | ~ r1_tarski(A_86,C_88)
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_128,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_111,c_32])).

tff(c_277,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_247,c_128])).

tff(c_733,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_1128,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1125,c_733])).

tff(c_1139,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_6,c_8,c_1128])).

tff(c_1145,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_213,c_1139])).

tff(c_1152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1145])).

tff(c_1153,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_1413,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1410,c_1153])).

tff(c_1424,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_6,c_144,c_1413])).

tff(c_1430,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_213,c_1424])).

tff(c_1437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:36:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.48  
% 3.29/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.48  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.29/1.48  
% 3.29/1.48  %Foreground sorts:
% 3.29/1.48  
% 3.29/1.48  
% 3.29/1.48  %Background operators:
% 3.29/1.48  
% 3.29/1.48  
% 3.29/1.48  %Foreground operators:
% 3.29/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.29/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.29/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.29/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.29/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.29/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.29/1.48  
% 3.29/1.49  tff(f_90, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 3.29/1.49  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.29/1.49  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.29/1.49  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.29/1.49  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.29/1.49  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.29/1.49  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.29/1.49  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relat_1)).
% 3.29/1.49  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.29/1.49  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.29/1.49  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.29/1.49  tff(c_85, plain, (![A_59, B_60]: (k1_setfam_1(k2_tarski(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.29/1.49  tff(c_105, plain, (![A_63, B_64]: (k1_setfam_1(k2_tarski(A_63, B_64))=k3_xboole_0(B_64, A_63))), inference(superposition, [status(thm), theory('equality')], [c_12, c_85])).
% 3.29/1.49  tff(c_22, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.29/1.49  tff(c_111, plain, (![B_64, A_63]: (k3_xboole_0(B_64, A_63)=k3_xboole_0(A_63, B_64))), inference(superposition, [status(thm), theory('equality')], [c_105, c_22])).
% 3.29/1.49  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.29/1.49  tff(c_26, plain, (![A_26, B_27]: (m1_subset_1(A_26, k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.29/1.49  tff(c_192, plain, (![B_71, A_72]: (v1_relat_1(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.29/1.49  tff(c_197, plain, (![A_73, B_74]: (v1_relat_1(A_73) | ~v1_relat_1(B_74) | ~r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_26, c_192])).
% 3.29/1.49  tff(c_210, plain, (![A_75, B_76]: (v1_relat_1(k3_xboole_0(A_75, B_76)) | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_8, c_197])).
% 3.29/1.49  tff(c_213, plain, (![B_64, A_63]: (v1_relat_1(k3_xboole_0(B_64, A_63)) | ~v1_relat_1(A_63))), inference(superposition, [status(thm), theory('equality')], [c_111, c_210])).
% 3.29/1.49  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.29/1.49  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.49  tff(c_129, plain, (![B_65, A_66]: (k3_xboole_0(B_65, A_66)=k3_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_105, c_22])).
% 3.29/1.49  tff(c_144, plain, (![B_65, A_66]: (r1_tarski(k3_xboole_0(B_65, A_66), A_66))), inference(superposition, [status(thm), theory('equality')], [c_129, c_8])).
% 3.29/1.49  tff(c_1410, plain, (![A_130, C_131, B_132, D_133]: (r1_tarski(k5_relat_1(A_130, C_131), k5_relat_1(B_132, D_133)) | ~r1_tarski(C_131, D_133) | ~r1_tarski(A_130, B_132) | ~v1_relat_1(D_133) | ~v1_relat_1(C_131) | ~v1_relat_1(B_132) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.29/1.49  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.29/1.49  tff(c_1125, plain, (![A_117, C_118, B_119, D_120]: (r1_tarski(k5_relat_1(A_117, C_118), k5_relat_1(B_119, D_120)) | ~r1_tarski(C_118, D_120) | ~r1_tarski(A_117, B_119) | ~v1_relat_1(D_120) | ~v1_relat_1(C_118) | ~v1_relat_1(B_119) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.29/1.49  tff(c_247, plain, (![A_86, B_87, C_88]: (r1_tarski(A_86, k3_xboole_0(B_87, C_88)) | ~r1_tarski(A_86, C_88) | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.29/1.49  tff(c_32, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.29/1.49  tff(c_128, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_111, c_32])).
% 3.29/1.49  tff(c_277, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_247, c_128])).
% 3.29/1.49  tff(c_733, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_277])).
% 3.29/1.49  tff(c_1128, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1125, c_733])).
% 3.29/1.49  tff(c_1139, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_6, c_8, c_1128])).
% 3.29/1.49  tff(c_1145, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_213, c_1139])).
% 3.29/1.49  tff(c_1152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1145])).
% 3.29/1.49  tff(c_1153, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_277])).
% 3.29/1.49  tff(c_1413, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1410, c_1153])).
% 3.29/1.49  tff(c_1424, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_6, c_144, c_1413])).
% 3.29/1.49  tff(c_1430, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_213, c_1424])).
% 3.29/1.49  tff(c_1437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1430])).
% 3.29/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.49  
% 3.29/1.49  Inference rules
% 3.29/1.49  ----------------------
% 3.29/1.49  #Ref     : 0
% 3.29/1.49  #Sup     : 344
% 3.29/1.49  #Fact    : 0
% 3.29/1.49  #Define  : 0
% 3.29/1.49  #Split   : 1
% 3.29/1.49  #Chain   : 0
% 3.29/1.49  #Close   : 0
% 3.29/1.49  
% 3.29/1.49  Ordering : KBO
% 3.29/1.49  
% 3.29/1.49  Simplification rules
% 3.29/1.49  ----------------------
% 3.29/1.49  #Subsume      : 53
% 3.29/1.49  #Demod        : 334
% 3.29/1.49  #Tautology    : 211
% 3.29/1.49  #SimpNegUnit  : 0
% 3.29/1.49  #BackRed      : 1
% 3.29/1.49  
% 3.29/1.49  #Partial instantiations: 0
% 3.29/1.49  #Strategies tried      : 1
% 3.29/1.49  
% 3.29/1.49  Timing (in seconds)
% 3.29/1.49  ----------------------
% 3.29/1.50  Preprocessing        : 0.33
% 3.29/1.50  Parsing              : 0.18
% 3.29/1.50  CNF conversion       : 0.02
% 3.29/1.50  Main loop            : 0.45
% 3.29/1.50  Inferencing          : 0.15
% 3.29/1.50  Reduction            : 0.19
% 3.29/1.50  Demodulation         : 0.16
% 3.29/1.50  BG Simplification    : 0.02
% 3.29/1.50  Subsumption          : 0.07
% 3.29/1.50  Abstraction          : 0.03
% 3.29/1.50  MUC search           : 0.00
% 3.29/1.50  Cooper               : 0.00
% 3.29/1.50  Total                : 0.81
% 3.29/1.50  Index Insertion      : 0.00
% 3.29/1.50  Index Deletion       : 0.00
% 3.29/1.50  Index Matching       : 0.00
% 3.29/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
