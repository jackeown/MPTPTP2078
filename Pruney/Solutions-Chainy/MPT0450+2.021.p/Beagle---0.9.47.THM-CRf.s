%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:39 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   59 (  89 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 128 expanded)
%              Number of equality atoms :    5 (  14 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
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

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_98,plain,(
    ! [A_59,B_60,C_61] : k3_xboole_0(k3_xboole_0(A_59,B_60),C_61) = k3_xboole_0(A_59,k3_xboole_0(B_60,C_61)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_110,plain,(
    ! [A_59,B_60,C_61] : k2_xboole_0(k3_xboole_0(A_59,B_60),k3_xboole_0(A_59,k3_xboole_0(B_60,C_61))) = k3_xboole_0(A_59,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_8])).

tff(c_259,plain,(
    ! [A_86,B_87,C_88] : r1_tarski(k2_xboole_0(k3_xboole_0(A_86,B_87),k3_xboole_0(A_86,C_88)),k2_xboole_0(B_87,C_88)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_271,plain,(
    ! [A_86,A_9,B_10] : r1_tarski(k2_xboole_0(k3_xboole_0(A_86,A_9),k3_xboole_0(A_86,k3_xboole_0(A_9,B_10))),A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_259])).

tff(c_341,plain,(
    ! [A_101,A_102] : r1_tarski(k3_xboole_0(A_101,A_102),A_102) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_271])).

tff(c_24,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(A_27,k1_zfmisc_1(B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_78,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_82,plain,(
    ! [A_27,B_28] :
      ( v1_relat_1(A_27)
      | ~ v1_relat_1(B_28)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_24,c_78])).

tff(c_348,plain,(
    ! [A_101,A_102] :
      ( v1_relat_1(k3_xboole_0(A_101,A_102))
      | ~ v1_relat_1(A_102) ) ),
    inference(resolution,[status(thm)],[c_341,c_82])).

tff(c_312,plain,(
    ! [A_86,A_9] : r1_tarski(k3_xboole_0(A_86,A_9),A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_271])).

tff(c_301,plain,(
    ! [A_96,B_97] :
      ( r1_tarski(k3_relat_1(A_96),k3_relat_1(B_97))
      | ~ r1_tarski(A_96,B_97)
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k3_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    ! [A_52,B_53] :
      ( v1_relat_1(A_52)
      | ~ v1_relat_1(B_53)
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_24,c_78])).

tff(c_87,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k3_xboole_0(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_205,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(k3_relat_1(A_81),k3_relat_1(B_82))
      | ~ r1_tarski(A_81,B_82)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_124,plain,(
    ! [A_62,B_63,C_64] :
      ( r1_tarski(A_62,k3_xboole_0(B_63,C_64))
      | ~ r1_tarski(A_62,C_64)
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_135,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_124,c_30])).

tff(c_162,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_208,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_205,c_162])).

tff(c_214,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4,c_208])).

tff(c_247,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_87,c_214])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_247])).

tff(c_252,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_304,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_301,c_252])).

tff(c_310,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_304])).

tff(c_355,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_310])).

tff(c_358,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_348,c_355])).

tff(c_365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_358])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:28:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.29  
% 2.33/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.29  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 2.33/1.29  
% 2.33/1.29  %Foreground sorts:
% 2.33/1.29  
% 2.33/1.29  
% 2.33/1.29  %Background operators:
% 2.33/1.29  
% 2.33/1.29  
% 2.33/1.29  %Foreground operators:
% 2.33/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.33/1.29  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.33/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.33/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.33/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.33/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.33/1.29  
% 2.33/1.31  tff(f_77, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 2.33/1.31  tff(f_27, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.33/1.31  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.33/1.31  tff(f_39, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.33/1.31  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.33/1.31  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.33/1.31  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 2.33/1.31  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.33/1.31  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.33/1.31  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.33/1.31  tff(c_98, plain, (![A_59, B_60, C_61]: (k3_xboole_0(k3_xboole_0(A_59, B_60), C_61)=k3_xboole_0(A_59, k3_xboole_0(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.33/1.31  tff(c_8, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k3_xboole_0(A_9, B_10))=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.33/1.31  tff(c_110, plain, (![A_59, B_60, C_61]: (k2_xboole_0(k3_xboole_0(A_59, B_60), k3_xboole_0(A_59, k3_xboole_0(B_60, C_61)))=k3_xboole_0(A_59, B_60))), inference(superposition, [status(thm), theory('equality')], [c_98, c_8])).
% 2.33/1.31  tff(c_259, plain, (![A_86, B_87, C_88]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_86, B_87), k3_xboole_0(A_86, C_88)), k2_xboole_0(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.31  tff(c_271, plain, (![A_86, A_9, B_10]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_86, A_9), k3_xboole_0(A_86, k3_xboole_0(A_9, B_10))), A_9))), inference(superposition, [status(thm), theory('equality')], [c_8, c_259])).
% 2.33/1.31  tff(c_341, plain, (![A_101, A_102]: (r1_tarski(k3_xboole_0(A_101, A_102), A_102))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_271])).
% 2.33/1.31  tff(c_24, plain, (![A_27, B_28]: (m1_subset_1(A_27, k1_zfmisc_1(B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.33/1.31  tff(c_78, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.33/1.31  tff(c_82, plain, (![A_27, B_28]: (v1_relat_1(A_27) | ~v1_relat_1(B_28) | ~r1_tarski(A_27, B_28))), inference(resolution, [status(thm)], [c_24, c_78])).
% 2.33/1.31  tff(c_348, plain, (![A_101, A_102]: (v1_relat_1(k3_xboole_0(A_101, A_102)) | ~v1_relat_1(A_102))), inference(resolution, [status(thm)], [c_341, c_82])).
% 2.33/1.31  tff(c_312, plain, (![A_86, A_9]: (r1_tarski(k3_xboole_0(A_86, A_9), A_9))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_271])).
% 2.33/1.31  tff(c_301, plain, (![A_96, B_97]: (r1_tarski(k3_relat_1(A_96), k3_relat_1(B_97)) | ~r1_tarski(A_96, B_97) | ~v1_relat_1(B_97) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.33/1.31  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.33/1.31  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k3_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.33/1.31  tff(c_83, plain, (![A_52, B_53]: (v1_relat_1(A_52) | ~v1_relat_1(B_53) | ~r1_tarski(A_52, B_53))), inference(resolution, [status(thm)], [c_24, c_78])).
% 2.33/1.31  tff(c_87, plain, (![A_4, B_5]: (v1_relat_1(k3_xboole_0(A_4, B_5)) | ~v1_relat_1(A_4))), inference(resolution, [status(thm)], [c_4, c_83])).
% 2.33/1.31  tff(c_205, plain, (![A_81, B_82]: (r1_tarski(k3_relat_1(A_81), k3_relat_1(B_82)) | ~r1_tarski(A_81, B_82) | ~v1_relat_1(B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.33/1.31  tff(c_124, plain, (![A_62, B_63, C_64]: (r1_tarski(A_62, k3_xboole_0(B_63, C_64)) | ~r1_tarski(A_62, C_64) | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.31  tff(c_30, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.33/1.31  tff(c_135, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_124, c_30])).
% 2.33/1.31  tff(c_162, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_135])).
% 2.33/1.31  tff(c_208, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_205, c_162])).
% 2.33/1.31  tff(c_214, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4, c_208])).
% 2.33/1.31  tff(c_247, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_87, c_214])).
% 2.33/1.31  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_247])).
% 2.33/1.31  tff(c_252, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_135])).
% 2.33/1.31  tff(c_304, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_301, c_252])).
% 2.33/1.31  tff(c_310, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_304])).
% 2.33/1.31  tff(c_355, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_312, c_310])).
% 2.33/1.31  tff(c_358, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_348, c_355])).
% 2.33/1.31  tff(c_365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_358])).
% 2.33/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.31  
% 2.33/1.31  Inference rules
% 2.33/1.31  ----------------------
% 2.33/1.31  #Ref     : 0
% 2.33/1.31  #Sup     : 74
% 2.33/1.31  #Fact    : 0
% 2.33/1.31  #Define  : 0
% 2.33/1.31  #Split   : 2
% 2.33/1.31  #Chain   : 0
% 2.33/1.31  #Close   : 0
% 2.33/1.31  
% 2.33/1.31  Ordering : KBO
% 2.33/1.31  
% 2.33/1.31  Simplification rules
% 2.33/1.31  ----------------------
% 2.33/1.31  #Subsume      : 1
% 2.33/1.31  #Demod        : 36
% 2.33/1.31  #Tautology    : 24
% 2.33/1.31  #SimpNegUnit  : 0
% 2.33/1.31  #BackRed      : 2
% 2.33/1.31  
% 2.33/1.31  #Partial instantiations: 0
% 2.33/1.31  #Strategies tried      : 1
% 2.33/1.31  
% 2.33/1.31  Timing (in seconds)
% 2.33/1.31  ----------------------
% 2.33/1.31  Preprocessing        : 0.30
% 2.33/1.31  Parsing              : 0.16
% 2.33/1.31  CNF conversion       : 0.02
% 2.33/1.31  Main loop            : 0.24
% 2.33/1.31  Inferencing          : 0.09
% 2.33/1.31  Reduction            : 0.08
% 2.33/1.31  Demodulation         : 0.06
% 2.33/1.31  BG Simplification    : 0.01
% 2.33/1.31  Subsumption          : 0.04
% 2.33/1.31  Abstraction          : 0.02
% 2.33/1.31  MUC search           : 0.00
% 2.33/1.31  Cooper               : 0.00
% 2.33/1.31  Total                : 0.57
% 2.33/1.31  Index Insertion      : 0.00
% 2.33/1.31  Index Deletion       : 0.00
% 2.33/1.31  Index Matching       : 0.00
% 2.33/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
