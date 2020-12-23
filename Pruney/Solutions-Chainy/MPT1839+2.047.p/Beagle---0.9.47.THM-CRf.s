%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:27 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   49 (  57 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 (  79 expanded)
%              Number of equality atoms :   27 (  32 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_89,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | k4_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_97,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_89,c_20])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_51,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_63,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_51])).

tff(c_10,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [A_39,B_40] : k5_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = k4_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k5_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_107])).

tff(c_119,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_116])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_62,plain,(
    ! [A_5,B_6] : k4_xboole_0(k3_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_51])).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_24,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_127,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(A_43,B_42)
      | ~ v1_zfmisc_1(B_42)
      | v1_xboole_0(B_42)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_145,plain,(
    ! [B_44,A_45] :
      ( B_44 = A_45
      | ~ v1_zfmisc_1(B_44)
      | v1_xboole_0(B_44)
      | v1_xboole_0(A_45)
      | k4_xboole_0(A_45,B_44) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_127])).

tff(c_147,plain,(
    ! [A_45] :
      ( A_45 = '#skF_1'
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_45)
      | k4_xboole_0(A_45,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_145])).

tff(c_151,plain,(
    ! [A_46] :
      ( A_46 = '#skF_1'
      | v1_xboole_0(A_46)
      | k4_xboole_0(A_46,'#skF_1') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_147])).

tff(c_22,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_154,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_151,c_22])).

tff(c_160,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_154])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_169,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_6])).

tff(c_178,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_169])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:59:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.18  
% 1.95/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.18  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.95/1.18  
% 1.95/1.18  %Foreground sorts:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Background operators:
% 1.95/1.18  
% 1.95/1.18  
% 1.95/1.18  %Foreground operators:
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.95/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.18  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.95/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.95/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.95/1.18  
% 1.95/1.19  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.95/1.19  tff(f_66, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 1.95/1.19  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.95/1.19  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.95/1.19  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.95/1.19  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.95/1.19  tff(f_54, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 1.95/1.19  tff(c_89, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | k4_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.19  tff(c_20, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.95/1.19  tff(c_97, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_89, c_20])).
% 1.95/1.19  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.19  tff(c_51, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.19  tff(c_63, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_51])).
% 1.95/1.19  tff(c_10, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.19  tff(c_107, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k3_xboole_0(A_39, B_40))=k4_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.19  tff(c_116, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k5_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_107])).
% 1.95/1.19  tff(c_119, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_116])).
% 1.95/1.19  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.19  tff(c_62, plain, (![A_5, B_6]: (k4_xboole_0(k3_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_51])).
% 1.95/1.19  tff(c_26, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.95/1.19  tff(c_24, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.95/1.19  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.19  tff(c_127, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(A_43, B_42) | ~v1_zfmisc_1(B_42) | v1_xboole_0(B_42) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.95/1.19  tff(c_145, plain, (![B_44, A_45]: (B_44=A_45 | ~v1_zfmisc_1(B_44) | v1_xboole_0(B_44) | v1_xboole_0(A_45) | k4_xboole_0(A_45, B_44)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_127])).
% 1.95/1.19  tff(c_147, plain, (![A_45]: (A_45='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(A_45) | k4_xboole_0(A_45, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_145])).
% 1.95/1.19  tff(c_151, plain, (![A_46]: (A_46='#skF_1' | v1_xboole_0(A_46) | k4_xboole_0(A_46, '#skF_1')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_26, c_147])).
% 1.95/1.19  tff(c_22, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.95/1.19  tff(c_154, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_151, c_22])).
% 1.95/1.19  tff(c_160, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_154])).
% 1.95/1.19  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.19  tff(c_169, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_160, c_6])).
% 1.95/1.19  tff(c_178, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_119, c_169])).
% 1.95/1.19  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_178])).
% 1.95/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  
% 1.95/1.19  Inference rules
% 1.95/1.19  ----------------------
% 1.95/1.19  #Ref     : 0
% 1.95/1.19  #Sup     : 36
% 1.95/1.19  #Fact    : 0
% 1.95/1.19  #Define  : 0
% 1.95/1.19  #Split   : 0
% 1.95/1.19  #Chain   : 0
% 1.95/1.19  #Close   : 0
% 1.95/1.19  
% 1.95/1.19  Ordering : KBO
% 1.95/1.19  
% 1.95/1.19  Simplification rules
% 1.95/1.19  ----------------------
% 1.95/1.19  #Subsume      : 1
% 1.95/1.19  #Demod        : 6
% 1.95/1.19  #Tautology    : 21
% 1.95/1.19  #SimpNegUnit  : 2
% 1.95/1.19  #BackRed      : 1
% 1.95/1.19  
% 1.95/1.19  #Partial instantiations: 0
% 1.95/1.19  #Strategies tried      : 1
% 1.95/1.19  
% 1.95/1.19  Timing (in seconds)
% 1.95/1.19  ----------------------
% 1.95/1.19  Preprocessing        : 0.29
% 1.95/1.19  Parsing              : 0.16
% 1.95/1.19  CNF conversion       : 0.02
% 1.95/1.19  Main loop            : 0.14
% 1.95/1.19  Inferencing          : 0.06
% 1.95/1.20  Reduction            : 0.04
% 1.95/1.20  Demodulation         : 0.03
% 1.95/1.20  BG Simplification    : 0.01
% 1.95/1.20  Subsumption          : 0.02
% 1.95/1.20  Abstraction          : 0.01
% 1.95/1.20  MUC search           : 0.00
% 1.95/1.20  Cooper               : 0.00
% 1.95/1.20  Total                : 0.47
% 1.95/1.20  Index Insertion      : 0.00
% 1.95/1.20  Index Deletion       : 0.00
% 1.95/1.20  Index Matching       : 0.00
% 1.95/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
