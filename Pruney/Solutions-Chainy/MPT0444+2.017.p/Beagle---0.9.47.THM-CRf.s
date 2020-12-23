%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:22 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   56 (  91 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 ( 128 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
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

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_102,plain,(
    ! [A_72,B_73,C_74] : r1_tarski(k2_xboole_0(k3_xboole_0(A_72,B_73),k3_xboole_0(A_72,C_74)),k2_xboole_0(B_73,C_74)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_109,plain,(
    ! [A_72,B_73] : r1_tarski(k3_xboole_0(A_72,B_73),k2_xboole_0(B_73,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_102])).

tff(c_125,plain,(
    ! [A_79,B_80] : r1_tarski(k3_xboole_0(A_79,B_80),B_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_109])).

tff(c_26,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(A_40,k1_zfmisc_1(B_41))
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_73,plain,(
    ! [B_60,A_61] :
      ( v1_relat_1(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_77,plain,(
    ! [A_40,B_41] :
      ( v1_relat_1(A_40)
      | ~ v1_relat_1(B_41)
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_26,c_73])).

tff(c_129,plain,(
    ! [A_79,B_80] :
      ( v1_relat_1(k3_xboole_0(A_79,B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_125,c_77])).

tff(c_114,plain,(
    ! [A_72,B_73] : r1_tarski(k3_xboole_0(A_72,B_73),B_73) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_109])).

tff(c_160,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k2_relat_1(A_85),k2_relat_1(B_86))
      | ~ r1_tarski(A_85,B_86)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_133,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k2_relat_1(A_83),k2_relat_1(B_84))
      | ~ r1_tarski(A_83,B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_93,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(A_69,k3_xboole_0(B_70,C_71))
      | ~ r1_tarski(A_69,C_71)
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_101,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_93,c_34])).

tff(c_132,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_136,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_133,c_132])).

tff(c_142,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4,c_136])).

tff(c_146,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_129,c_142])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_146])).

tff(c_154,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_163,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_160,c_154])).

tff(c_169,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_114,c_163])).

tff(c_173,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_129,c_169])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:36:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.21  
% 2.04/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.22  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.04/1.22  
% 2.04/1.22  %Foreground sorts:
% 2.04/1.22  
% 2.04/1.22  
% 2.04/1.22  %Background operators:
% 2.04/1.22  
% 2.04/1.22  
% 2.04/1.22  %Foreground operators:
% 2.04/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.04/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.04/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.04/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.04/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.04/1.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.04/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.04/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.04/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.04/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.04/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.04/1.22  
% 2.04/1.23  tff(f_81, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 2.04/1.23  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.04/1.23  tff(f_37, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.04/1.23  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.04/1.23  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.04/1.23  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.04/1.23  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.04/1.23  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.04/1.23  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.04/1.23  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.04/1.23  tff(c_102, plain, (![A_72, B_73, C_74]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_72, B_73), k3_xboole_0(A_72, C_74)), k2_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.23  tff(c_109, plain, (![A_72, B_73]: (r1_tarski(k3_xboole_0(A_72, B_73), k2_xboole_0(B_73, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_102])).
% 2.04/1.23  tff(c_125, plain, (![A_79, B_80]: (r1_tarski(k3_xboole_0(A_79, B_80), B_80))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_109])).
% 2.04/1.23  tff(c_26, plain, (![A_40, B_41]: (m1_subset_1(A_40, k1_zfmisc_1(B_41)) | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.04/1.23  tff(c_73, plain, (![B_60, A_61]: (v1_relat_1(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.04/1.23  tff(c_77, plain, (![A_40, B_41]: (v1_relat_1(A_40) | ~v1_relat_1(B_41) | ~r1_tarski(A_40, B_41))), inference(resolution, [status(thm)], [c_26, c_73])).
% 2.04/1.23  tff(c_129, plain, (![A_79, B_80]: (v1_relat_1(k3_xboole_0(A_79, B_80)) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_125, c_77])).
% 2.04/1.23  tff(c_114, plain, (![A_72, B_73]: (r1_tarski(k3_xboole_0(A_72, B_73), B_73))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_109])).
% 2.04/1.23  tff(c_160, plain, (![A_85, B_86]: (r1_tarski(k2_relat_1(A_85), k2_relat_1(B_86)) | ~r1_tarski(A_85, B_86) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.04/1.23  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.04/1.23  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.04/1.23  tff(c_133, plain, (![A_83, B_84]: (r1_tarski(k2_relat_1(A_83), k2_relat_1(B_84)) | ~r1_tarski(A_83, B_84) | ~v1_relat_1(B_84) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.04/1.23  tff(c_93, plain, (![A_69, B_70, C_71]: (r1_tarski(A_69, k3_xboole_0(B_70, C_71)) | ~r1_tarski(A_69, C_71) | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.23  tff(c_34, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.04/1.23  tff(c_101, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_93, c_34])).
% 2.04/1.23  tff(c_132, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_101])).
% 2.04/1.23  tff(c_136, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_133, c_132])).
% 2.04/1.23  tff(c_142, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4, c_136])).
% 2.04/1.23  tff(c_146, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_129, c_142])).
% 2.04/1.23  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_146])).
% 2.04/1.23  tff(c_154, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_101])).
% 2.04/1.23  tff(c_163, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_160, c_154])).
% 2.04/1.23  tff(c_169, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_114, c_163])).
% 2.04/1.23  tff(c_173, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_129, c_169])).
% 2.04/1.23  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_173])).
% 2.04/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.23  
% 2.04/1.23  Inference rules
% 2.04/1.23  ----------------------
% 2.04/1.23  #Ref     : 0
% 2.04/1.23  #Sup     : 28
% 2.04/1.23  #Fact    : 0
% 2.04/1.23  #Define  : 0
% 2.04/1.23  #Split   : 1
% 2.04/1.23  #Chain   : 0
% 2.04/1.23  #Close   : 0
% 2.04/1.23  
% 2.04/1.23  Ordering : KBO
% 2.04/1.23  
% 2.04/1.23  Simplification rules
% 2.04/1.23  ----------------------
% 2.04/1.23  #Subsume      : 0
% 2.04/1.23  #Demod        : 9
% 2.04/1.23  #Tautology    : 12
% 2.04/1.23  #SimpNegUnit  : 0
% 2.04/1.23  #BackRed      : 0
% 2.04/1.23  
% 2.04/1.23  #Partial instantiations: 0
% 2.04/1.23  #Strategies tried      : 1
% 2.04/1.23  
% 2.04/1.23  Timing (in seconds)
% 2.04/1.23  ----------------------
% 2.04/1.23  Preprocessing        : 0.31
% 2.04/1.23  Parsing              : 0.17
% 2.04/1.23  CNF conversion       : 0.02
% 2.04/1.23  Main loop            : 0.15
% 2.04/1.23  Inferencing          : 0.06
% 2.04/1.23  Reduction            : 0.04
% 2.04/1.23  Demodulation         : 0.03
% 2.04/1.23  BG Simplification    : 0.01
% 2.04/1.23  Subsumption          : 0.03
% 2.04/1.23  Abstraction          : 0.01
% 2.04/1.23  MUC search           : 0.00
% 2.04/1.23  Cooper               : 0.00
% 2.04/1.23  Total                : 0.49
% 2.04/1.23  Index Insertion      : 0.00
% 2.04/1.23  Index Deletion       : 0.00
% 2.04/1.23  Index Matching       : 0.00
% 2.04/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
