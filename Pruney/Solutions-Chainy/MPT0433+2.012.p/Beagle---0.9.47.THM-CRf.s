%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:15 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 101 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 154 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_182,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_196,plain,(
    ! [A_59,B_60] :
      ( v1_relat_1(A_59)
      | ~ v1_relat_1(B_60)
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_22,c_182])).

tff(c_207,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k3_xboole_0(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_196])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_35,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    ! [B_34,A_35] : r1_tarski(k3_xboole_0(B_34,A_35),A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_35,c_6])).

tff(c_94,plain,(
    ! [A_42,B_43] :
      ( k2_xboole_0(A_42,B_43) = B_43
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [B_34,A_35] : k2_xboole_0(k3_xboole_0(B_34,A_35),A_35) = A_35 ),
    inference(resolution,[status(thm)],[c_50,c_94])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_106,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k2_xboole_0(A_10,B_11) ),
    inference(resolution,[status(thm)],[c_10,c_94])).

tff(c_453,plain,(
    ! [A_86,B_87] :
      ( k2_xboole_0(k1_relat_1(A_86),k1_relat_1(B_87)) = k1_relat_1(k2_xboole_0(A_86,B_87))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_481,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(k1_relat_1(A_88),k1_relat_1(k2_xboole_0(A_88,B_89)))
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_10])).

tff(c_572,plain,(
    ! [A_95,B_96] :
      ( r1_tarski(k1_relat_1(A_95),k1_relat_1(k2_xboole_0(A_95,B_96)))
      | ~ v1_relat_1(k2_xboole_0(A_95,B_96))
      | ~ v1_relat_1(A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_481])).

tff(c_593,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(B_34,A_35)),k1_relat_1(A_35))
      | ~ v1_relat_1(k2_xboole_0(k3_xboole_0(B_34,A_35),A_35))
      | ~ v1_relat_1(k3_xboole_0(B_34,A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_572])).

tff(c_673,plain,(
    ! [B_102,A_103] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(B_102,A_103)),k1_relat_1(A_103))
      | ~ v1_relat_1(A_103)
      | ~ v1_relat_1(k3_xboole_0(B_102,A_103)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_593])).

tff(c_105,plain,(
    ! [A_5,B_6] : k2_xboole_0(k3_xboole_0(A_5,B_6),A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_6,c_94])).

tff(c_293,plain,(
    ! [A_75,B_76] :
      ( k2_xboole_0(k1_relat_1(A_75),k1_relat_1(B_76)) = k1_relat_1(k2_xboole_0(A_75,B_76))
      | ~ v1_relat_1(B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_311,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(k1_relat_1(A_77),k1_relat_1(k2_xboole_0(A_77,B_78)))
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_10])).

tff(c_396,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_84,B_85)),k1_relat_1(A_84))
      | ~ v1_relat_1(A_84)
      | ~ v1_relat_1(k3_xboole_0(A_84,B_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_311])).

tff(c_230,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(A_67,k3_xboole_0(B_68,C_69))
      | ~ r1_tarski(A_67,C_69)
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_248,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_230,c_28])).

tff(c_292,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_248])).

tff(c_399,plain,
    ( ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_396,c_292])).

tff(c_414,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_399])).

tff(c_419,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_207,c_414])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_419])).

tff(c_427,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_676,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_673,c_427])).

tff(c_691,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_676])).

tff(c_696,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_207,c_691])).

tff(c_703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_696])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:25:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.38  
% 2.82/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.39  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.82/1.39  
% 2.82/1.39  %Foreground sorts:
% 2.82/1.39  
% 2.82/1.39  
% 2.82/1.39  %Background operators:
% 2.82/1.39  
% 2.82/1.39  
% 2.82/1.39  %Foreground operators:
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.82/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.82/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.82/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.82/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.82/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.82/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.82/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.82/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.82/1.39  
% 2.82/1.40  tff(f_75, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 2.82/1.40  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.82/1.40  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.82/1.40  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.82/1.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.82/1.40  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.82/1.40  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.82/1.40  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 2.82/1.40  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.82/1.40  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.82/1.40  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.82/1.40  tff(c_22, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.82/1.40  tff(c_182, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.82/1.40  tff(c_196, plain, (![A_59, B_60]: (v1_relat_1(A_59) | ~v1_relat_1(B_60) | ~r1_tarski(A_59, B_60))), inference(resolution, [status(thm)], [c_22, c_182])).
% 2.82/1.40  tff(c_207, plain, (![A_5, B_6]: (v1_relat_1(k3_xboole_0(A_5, B_6)) | ~v1_relat_1(A_5))), inference(resolution, [status(thm)], [c_6, c_196])).
% 2.82/1.40  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.82/1.40  tff(c_35, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.82/1.40  tff(c_50, plain, (![B_34, A_35]: (r1_tarski(k3_xboole_0(B_34, A_35), A_35))), inference(superposition, [status(thm), theory('equality')], [c_35, c_6])).
% 2.82/1.40  tff(c_94, plain, (![A_42, B_43]: (k2_xboole_0(A_42, B_43)=B_43 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.40  tff(c_104, plain, (![B_34, A_35]: (k2_xboole_0(k3_xboole_0(B_34, A_35), A_35)=A_35)), inference(resolution, [status(thm)], [c_50, c_94])).
% 2.82/1.40  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.82/1.40  tff(c_106, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k2_xboole_0(A_10, B_11))), inference(resolution, [status(thm)], [c_10, c_94])).
% 2.82/1.40  tff(c_453, plain, (![A_86, B_87]: (k2_xboole_0(k1_relat_1(A_86), k1_relat_1(B_87))=k1_relat_1(k2_xboole_0(A_86, B_87)) | ~v1_relat_1(B_87) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.82/1.40  tff(c_481, plain, (![A_88, B_89]: (r1_tarski(k1_relat_1(A_88), k1_relat_1(k2_xboole_0(A_88, B_89))) | ~v1_relat_1(B_89) | ~v1_relat_1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_453, c_10])).
% 2.82/1.40  tff(c_572, plain, (![A_95, B_96]: (r1_tarski(k1_relat_1(A_95), k1_relat_1(k2_xboole_0(A_95, B_96))) | ~v1_relat_1(k2_xboole_0(A_95, B_96)) | ~v1_relat_1(A_95))), inference(superposition, [status(thm), theory('equality')], [c_106, c_481])).
% 2.82/1.40  tff(c_593, plain, (![B_34, A_35]: (r1_tarski(k1_relat_1(k3_xboole_0(B_34, A_35)), k1_relat_1(A_35)) | ~v1_relat_1(k2_xboole_0(k3_xboole_0(B_34, A_35), A_35)) | ~v1_relat_1(k3_xboole_0(B_34, A_35)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_572])).
% 2.82/1.40  tff(c_673, plain, (![B_102, A_103]: (r1_tarski(k1_relat_1(k3_xboole_0(B_102, A_103)), k1_relat_1(A_103)) | ~v1_relat_1(A_103) | ~v1_relat_1(k3_xboole_0(B_102, A_103)))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_593])).
% 2.82/1.40  tff(c_105, plain, (![A_5, B_6]: (k2_xboole_0(k3_xboole_0(A_5, B_6), A_5)=A_5)), inference(resolution, [status(thm)], [c_6, c_94])).
% 2.82/1.40  tff(c_293, plain, (![A_75, B_76]: (k2_xboole_0(k1_relat_1(A_75), k1_relat_1(B_76))=k1_relat_1(k2_xboole_0(A_75, B_76)) | ~v1_relat_1(B_76) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.82/1.40  tff(c_311, plain, (![A_77, B_78]: (r1_tarski(k1_relat_1(A_77), k1_relat_1(k2_xboole_0(A_77, B_78))) | ~v1_relat_1(B_78) | ~v1_relat_1(A_77))), inference(superposition, [status(thm), theory('equality')], [c_293, c_10])).
% 2.82/1.40  tff(c_396, plain, (![A_84, B_85]: (r1_tarski(k1_relat_1(k3_xboole_0(A_84, B_85)), k1_relat_1(A_84)) | ~v1_relat_1(A_84) | ~v1_relat_1(k3_xboole_0(A_84, B_85)))), inference(superposition, [status(thm), theory('equality')], [c_105, c_311])).
% 2.82/1.40  tff(c_230, plain, (![A_67, B_68, C_69]: (r1_tarski(A_67, k3_xboole_0(B_68, C_69)) | ~r1_tarski(A_67, C_69) | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.82/1.40  tff(c_28, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.82/1.40  tff(c_248, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_230, c_28])).
% 2.82/1.40  tff(c_292, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_248])).
% 2.82/1.40  tff(c_399, plain, (~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_396, c_292])).
% 2.82/1.40  tff(c_414, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_399])).
% 2.82/1.40  tff(c_419, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_207, c_414])).
% 2.82/1.40  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_419])).
% 2.82/1.40  tff(c_427, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_248])).
% 2.82/1.40  tff(c_676, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_673, c_427])).
% 2.82/1.40  tff(c_691, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_676])).
% 2.82/1.40  tff(c_696, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_207, c_691])).
% 2.82/1.40  tff(c_703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_696])).
% 2.82/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.40  
% 2.82/1.40  Inference rules
% 2.82/1.40  ----------------------
% 2.82/1.40  #Ref     : 0
% 2.82/1.40  #Sup     : 172
% 2.82/1.40  #Fact    : 0
% 2.82/1.40  #Define  : 0
% 2.82/1.40  #Split   : 2
% 2.82/1.40  #Chain   : 0
% 2.82/1.40  #Close   : 0
% 2.82/1.40  
% 2.82/1.40  Ordering : KBO
% 2.82/1.40  
% 2.82/1.40  Simplification rules
% 2.82/1.40  ----------------------
% 2.82/1.40  #Subsume      : 35
% 2.82/1.40  #Demod        : 33
% 2.82/1.40  #Tautology    : 65
% 2.82/1.40  #SimpNegUnit  : 0
% 2.82/1.40  #BackRed      : 0
% 2.82/1.40  
% 2.82/1.40  #Partial instantiations: 0
% 2.82/1.40  #Strategies tried      : 1
% 2.82/1.40  
% 2.82/1.40  Timing (in seconds)
% 2.82/1.40  ----------------------
% 2.82/1.40  Preprocessing        : 0.30
% 2.82/1.40  Parsing              : 0.16
% 2.82/1.40  CNF conversion       : 0.02
% 2.82/1.40  Main loop            : 0.32
% 2.82/1.40  Inferencing          : 0.12
% 2.82/1.40  Reduction            : 0.11
% 2.82/1.40  Demodulation         : 0.09
% 2.82/1.40  BG Simplification    : 0.02
% 2.82/1.40  Subsumption          : 0.06
% 2.82/1.40  Abstraction          : 0.02
% 2.82/1.40  MUC search           : 0.00
% 2.82/1.40  Cooper               : 0.00
% 2.82/1.40  Total                : 0.65
% 2.82/1.40  Index Insertion      : 0.00
% 2.82/1.40  Index Deletion       : 0.00
% 2.82/1.40  Index Matching       : 0.00
% 2.82/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
