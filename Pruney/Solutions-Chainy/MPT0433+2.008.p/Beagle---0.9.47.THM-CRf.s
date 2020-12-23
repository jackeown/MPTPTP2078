%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:14 EST 2020

% Result     : Theorem 10.82s
% Output     : CNFRefutation 10.98s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 214 expanded)
%              Number of leaves         :   28 (  82 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 316 expanded)
%              Number of equality atoms :   17 (  88 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

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

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(k3_xboole_0(A_6,B_7),k4_xboole_0(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_102,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_173,plain,(
    ! [A_50,B_51] : k3_tarski(k2_tarski(A_50,B_51)) = k2_xboole_0(B_51,A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_102])).

tff(c_16,plain,(
    ! [A_17,B_18] : k3_tarski(k2_tarski(A_17,B_18)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_179,plain,(
    ! [B_51,A_50] : k2_xboole_0(B_51,A_50) = k2_xboole_0(A_50,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_16])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_196,plain,(
    ! [B_52,A_53] :
      ( v1_relat_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4805,plain,(
    ! [A_175,B_176] :
      ( v1_relat_1(A_175)
      | ~ v1_relat_1(B_176)
      | ~ r1_tarski(A_175,B_176) ) ),
    inference(resolution,[status(thm)],[c_22,c_196])).

tff(c_4846,plain,(
    ! [A_179,B_180] :
      ( v1_relat_1(A_179)
      | ~ v1_relat_1(k2_xboole_0(A_179,B_180)) ) ),
    inference(resolution,[status(thm)],[c_8,c_4805])).

tff(c_4888,plain,(
    ! [A_183,B_184] :
      ( v1_relat_1(A_183)
      | ~ v1_relat_1(k2_xboole_0(B_184,A_183)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_4846])).

tff(c_4915,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k4_xboole_0(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_4888])).

tff(c_67,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_117,plain,(
    ! [B_46,A_47] : k1_setfam_1(k2_tarski(B_46,A_47)) = k3_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_18,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_123,plain,(
    ! [B_46,A_47] : k3_xboole_0(B_46,A_47) = k3_xboole_0(A_47,B_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_18])).

tff(c_254,plain,(
    ! [A_58,B_59] : k2_xboole_0(k3_xboole_0(A_58,B_59),k4_xboole_0(A_58,B_59)) = A_58 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_263,plain,(
    ! [A_58,B_59] : r1_tarski(k3_xboole_0(A_58,B_59),A_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_8])).

tff(c_4838,plain,(
    ! [A_177,B_178] :
      ( v1_relat_1(k3_xboole_0(A_177,B_178))
      | ~ v1_relat_1(A_177) ) ),
    inference(resolution,[status(thm)],[c_263,c_4805])).

tff(c_4844,plain,(
    ! [A_47,B_46] :
      ( v1_relat_1(k3_xboole_0(A_47,B_46))
      | ~ v1_relat_1(B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_4838])).

tff(c_462,plain,(
    ! [A_80,B_81] :
      ( k2_xboole_0(k1_relat_1(A_80),k1_relat_1(B_81)) = k1_relat_1(k2_xboole_0(A_80,B_81))
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5254,plain,(
    ! [A_193,B_194] :
      ( r1_tarski(k1_relat_1(A_193),k1_relat_1(k2_xboole_0(A_193,B_194)))
      | ~ v1_relat_1(B_194)
      | ~ v1_relat_1(A_193) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_8])).

tff(c_8432,plain,(
    ! [A_248,B_249] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_248,B_249)),k1_relat_1(A_248))
      | ~ v1_relat_1(k4_xboole_0(A_248,B_249))
      | ~ v1_relat_1(k3_xboole_0(A_248,B_249)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_5254])).

tff(c_25536,plain,(
    ! [B_368,A_369] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(B_368,A_369)),k1_relat_1(A_369))
      | ~ v1_relat_1(k4_xboole_0(A_369,B_368))
      | ~ v1_relat_1(k3_xboole_0(A_369,B_368)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_8432])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_542,plain,(
    ! [A_84,B_85] :
      ( v1_relat_1(A_84)
      | ~ v1_relat_1(B_85)
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_22,c_196])).

tff(c_578,plain,(
    ! [A_88,B_89] :
      ( v1_relat_1(A_88)
      | ~ v1_relat_1(k2_xboole_0(A_88,B_89)) ) ),
    inference(resolution,[status(thm)],[c_8,c_542])).

tff(c_613,plain,(
    ! [B_92,A_93] :
      ( v1_relat_1(B_92)
      | ~ v1_relat_1(k2_xboole_0(A_93,B_92)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_578])).

tff(c_634,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k4_xboole_0(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_613])).

tff(c_571,plain,(
    ! [A_86,B_87] :
      ( v1_relat_1(k3_xboole_0(A_86,B_87))
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_263,c_542])).

tff(c_574,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(k3_xboole_0(B_46,A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_571])).

tff(c_1338,plain,(
    ! [A_114,B_115] :
      ( r1_tarski(k1_relat_1(A_114),k1_relat_1(k2_xboole_0(A_114,B_115)))
      | ~ v1_relat_1(B_115)
      | ~ v1_relat_1(A_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_462,c_8])).

tff(c_4642,plain,(
    ! [A_169,B_170] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_169,B_170)),k1_relat_1(A_169))
      | ~ v1_relat_1(k4_xboole_0(A_169,B_170))
      | ~ v1_relat_1(k3_xboole_0(A_169,B_170)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1338])).

tff(c_372,plain,(
    ! [A_73,B_74,C_75] :
      ( r1_tarski(A_73,k3_xboole_0(B_74,C_75))
      | ~ r1_tarski(A_73,C_75)
      | ~ r1_tarski(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_385,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_372,c_28])).

tff(c_536,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_385])).

tff(c_4703,plain,
    ( ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4642,c_536])).

tff(c_4719,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4703])).

tff(c_4722,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_574,c_4719])).

tff(c_4729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4722])).

tff(c_4730,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4703])).

tff(c_4737,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_634,c_4730])).

tff(c_4741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4737])).

tff(c_4742,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_25554,plain,
    ( ~ v1_relat_1(k4_xboole_0('#skF_2','#skF_1'))
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_25536,c_4742])).

tff(c_25640,plain,
    ( ~ v1_relat_1(k4_xboole_0('#skF_2','#skF_1'))
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_25554])).

tff(c_25666,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_25640])).

tff(c_25669,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4844,c_25666])).

tff(c_25676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_25669])).

tff(c_25677,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_25640])).

tff(c_25681,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4915,c_25677])).

tff(c_25685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_25681])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:33:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.82/4.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.82/4.55  
% 10.82/4.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.82/4.56  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 10.82/4.56  
% 10.82/4.56  %Foreground sorts:
% 10.82/4.56  
% 10.82/4.56  
% 10.82/4.56  %Background operators:
% 10.82/4.56  
% 10.82/4.56  
% 10.82/4.56  %Foreground operators:
% 10.82/4.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.82/4.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.82/4.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.82/4.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.82/4.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.82/4.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.82/4.56  tff('#skF_2', type, '#skF_2': $i).
% 10.82/4.56  tff('#skF_1', type, '#skF_1': $i).
% 10.82/4.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.82/4.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.82/4.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.82/4.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.82/4.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.82/4.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.82/4.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.82/4.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.82/4.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.82/4.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.82/4.56  
% 10.98/4.57  tff(f_75, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relat_1)).
% 10.98/4.57  tff(f_37, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 10.98/4.57  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.98/4.57  tff(f_47, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.98/4.57  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.98/4.57  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 10.98/4.57  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.98/4.57  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 10.98/4.57  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relat_1)).
% 10.98/4.57  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 10.98/4.57  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.98/4.57  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(k3_xboole_0(A_6, B_7), k4_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.98/4.57  tff(c_10, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.98/4.57  tff(c_102, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.98/4.57  tff(c_173, plain, (![A_50, B_51]: (k3_tarski(k2_tarski(A_50, B_51))=k2_xboole_0(B_51, A_50))), inference(superposition, [status(thm), theory('equality')], [c_10, c_102])).
% 10.98/4.57  tff(c_16, plain, (![A_17, B_18]: (k3_tarski(k2_tarski(A_17, B_18))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.98/4.57  tff(c_179, plain, (![B_51, A_50]: (k2_xboole_0(B_51, A_50)=k2_xboole_0(A_50, B_51))), inference(superposition, [status(thm), theory('equality')], [c_173, c_16])).
% 10.98/4.57  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.98/4.57  tff(c_22, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.98/4.57  tff(c_196, plain, (![B_52, A_53]: (v1_relat_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_60])).
% 10.98/4.57  tff(c_4805, plain, (![A_175, B_176]: (v1_relat_1(A_175) | ~v1_relat_1(B_176) | ~r1_tarski(A_175, B_176))), inference(resolution, [status(thm)], [c_22, c_196])).
% 10.98/4.57  tff(c_4846, plain, (![A_179, B_180]: (v1_relat_1(A_179) | ~v1_relat_1(k2_xboole_0(A_179, B_180)))), inference(resolution, [status(thm)], [c_8, c_4805])).
% 10.98/4.57  tff(c_4888, plain, (![A_183, B_184]: (v1_relat_1(A_183) | ~v1_relat_1(k2_xboole_0(B_184, A_183)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_4846])).
% 10.98/4.57  tff(c_4915, plain, (![A_6, B_7]: (v1_relat_1(k4_xboole_0(A_6, B_7)) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_4888])).
% 10.98/4.57  tff(c_67, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.98/4.57  tff(c_117, plain, (![B_46, A_47]: (k1_setfam_1(k2_tarski(B_46, A_47))=k3_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_10, c_67])).
% 10.98/4.57  tff(c_18, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.98/4.57  tff(c_123, plain, (![B_46, A_47]: (k3_xboole_0(B_46, A_47)=k3_xboole_0(A_47, B_46))), inference(superposition, [status(thm), theory('equality')], [c_117, c_18])).
% 10.98/4.57  tff(c_254, plain, (![A_58, B_59]: (k2_xboole_0(k3_xboole_0(A_58, B_59), k4_xboole_0(A_58, B_59))=A_58)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.98/4.57  tff(c_263, plain, (![A_58, B_59]: (r1_tarski(k3_xboole_0(A_58, B_59), A_58))), inference(superposition, [status(thm), theory('equality')], [c_254, c_8])).
% 10.98/4.57  tff(c_4838, plain, (![A_177, B_178]: (v1_relat_1(k3_xboole_0(A_177, B_178)) | ~v1_relat_1(A_177))), inference(resolution, [status(thm)], [c_263, c_4805])).
% 10.98/4.57  tff(c_4844, plain, (![A_47, B_46]: (v1_relat_1(k3_xboole_0(A_47, B_46)) | ~v1_relat_1(B_46))), inference(superposition, [status(thm), theory('equality')], [c_123, c_4838])).
% 10.98/4.57  tff(c_462, plain, (![A_80, B_81]: (k2_xboole_0(k1_relat_1(A_80), k1_relat_1(B_81))=k1_relat_1(k2_xboole_0(A_80, B_81)) | ~v1_relat_1(B_81) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.98/4.57  tff(c_5254, plain, (![A_193, B_194]: (r1_tarski(k1_relat_1(A_193), k1_relat_1(k2_xboole_0(A_193, B_194))) | ~v1_relat_1(B_194) | ~v1_relat_1(A_193))), inference(superposition, [status(thm), theory('equality')], [c_462, c_8])).
% 10.98/4.57  tff(c_8432, plain, (![A_248, B_249]: (r1_tarski(k1_relat_1(k3_xboole_0(A_248, B_249)), k1_relat_1(A_248)) | ~v1_relat_1(k4_xboole_0(A_248, B_249)) | ~v1_relat_1(k3_xboole_0(A_248, B_249)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_5254])).
% 10.98/4.57  tff(c_25536, plain, (![B_368, A_369]: (r1_tarski(k1_relat_1(k3_xboole_0(B_368, A_369)), k1_relat_1(A_369)) | ~v1_relat_1(k4_xboole_0(A_369, B_368)) | ~v1_relat_1(k3_xboole_0(A_369, B_368)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_8432])).
% 10.98/4.57  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.98/4.57  tff(c_542, plain, (![A_84, B_85]: (v1_relat_1(A_84) | ~v1_relat_1(B_85) | ~r1_tarski(A_84, B_85))), inference(resolution, [status(thm)], [c_22, c_196])).
% 10.98/4.57  tff(c_578, plain, (![A_88, B_89]: (v1_relat_1(A_88) | ~v1_relat_1(k2_xboole_0(A_88, B_89)))), inference(resolution, [status(thm)], [c_8, c_542])).
% 10.98/4.57  tff(c_613, plain, (![B_92, A_93]: (v1_relat_1(B_92) | ~v1_relat_1(k2_xboole_0(A_93, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_179, c_578])).
% 10.98/4.57  tff(c_634, plain, (![A_6, B_7]: (v1_relat_1(k4_xboole_0(A_6, B_7)) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_613])).
% 10.98/4.57  tff(c_571, plain, (![A_86, B_87]: (v1_relat_1(k3_xboole_0(A_86, B_87)) | ~v1_relat_1(A_86))), inference(resolution, [status(thm)], [c_263, c_542])).
% 10.98/4.57  tff(c_574, plain, (![B_46, A_47]: (v1_relat_1(k3_xboole_0(B_46, A_47)) | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_123, c_571])).
% 10.98/4.57  tff(c_1338, plain, (![A_114, B_115]: (r1_tarski(k1_relat_1(A_114), k1_relat_1(k2_xboole_0(A_114, B_115))) | ~v1_relat_1(B_115) | ~v1_relat_1(A_114))), inference(superposition, [status(thm), theory('equality')], [c_462, c_8])).
% 10.98/4.57  tff(c_4642, plain, (![A_169, B_170]: (r1_tarski(k1_relat_1(k3_xboole_0(A_169, B_170)), k1_relat_1(A_169)) | ~v1_relat_1(k4_xboole_0(A_169, B_170)) | ~v1_relat_1(k3_xboole_0(A_169, B_170)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1338])).
% 10.98/4.57  tff(c_372, plain, (![A_73, B_74, C_75]: (r1_tarski(A_73, k3_xboole_0(B_74, C_75)) | ~r1_tarski(A_73, C_75) | ~r1_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.98/4.57  tff(c_28, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.98/4.57  tff(c_385, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_372, c_28])).
% 10.98/4.57  tff(c_536, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_385])).
% 10.98/4.57  tff(c_4703, plain, (~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4642, c_536])).
% 10.98/4.57  tff(c_4719, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_4703])).
% 10.98/4.57  tff(c_4722, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_574, c_4719])).
% 10.98/4.57  tff(c_4729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_4722])).
% 10.98/4.57  tff(c_4730, plain, (~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_4703])).
% 10.98/4.57  tff(c_4737, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_634, c_4730])).
% 10.98/4.57  tff(c_4741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_4737])).
% 10.98/4.57  tff(c_4742, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_385])).
% 10.98/4.57  tff(c_25554, plain, (~v1_relat_1(k4_xboole_0('#skF_2', '#skF_1')) | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_25536, c_4742])).
% 10.98/4.57  tff(c_25640, plain, (~v1_relat_1(k4_xboole_0('#skF_2', '#skF_1')) | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_25554])).
% 10.98/4.57  tff(c_25666, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_25640])).
% 10.98/4.57  tff(c_25669, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4844, c_25666])).
% 10.98/4.57  tff(c_25676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_25669])).
% 10.98/4.57  tff(c_25677, plain, (~v1_relat_1(k4_xboole_0('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_25640])).
% 10.98/4.57  tff(c_25681, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4915, c_25677])).
% 10.98/4.57  tff(c_25685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_25681])).
% 10.98/4.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.98/4.57  
% 10.98/4.57  Inference rules
% 10.98/4.57  ----------------------
% 10.98/4.57  #Ref     : 0
% 10.98/4.57  #Sup     : 6559
% 10.98/4.57  #Fact    : 0
% 10.98/4.57  #Define  : 0
% 10.98/4.57  #Split   : 5
% 10.98/4.57  #Chain   : 0
% 10.98/4.57  #Close   : 0
% 10.98/4.57  
% 10.98/4.57  Ordering : KBO
% 10.98/4.57  
% 10.98/4.57  Simplification rules
% 10.98/4.57  ----------------------
% 10.98/4.57  #Subsume      : 884
% 10.98/4.57  #Demod        : 9792
% 10.98/4.57  #Tautology    : 4097
% 10.98/4.57  #SimpNegUnit  : 5
% 10.98/4.57  #BackRed      : 0
% 10.98/4.57  
% 10.98/4.57  #Partial instantiations: 0
% 10.98/4.57  #Strategies tried      : 1
% 10.98/4.57  
% 10.98/4.57  Timing (in seconds)
% 10.98/4.57  ----------------------
% 10.98/4.58  Preprocessing        : 0.31
% 10.98/4.58  Parsing              : 0.17
% 10.98/4.58  CNF conversion       : 0.02
% 10.98/4.58  Main loop            : 3.50
% 10.98/4.58  Inferencing          : 0.68
% 10.98/4.58  Reduction            : 2.12
% 10.98/4.58  Demodulation         : 1.92
% 10.98/4.58  BG Simplification    : 0.07
% 10.98/4.58  Subsumption          : 0.49
% 10.98/4.58  Abstraction          : 0.16
% 10.98/4.58  MUC search           : 0.00
% 10.98/4.58  Cooper               : 0.00
% 10.98/4.58  Total                : 3.84
% 10.98/4.58  Index Insertion      : 0.00
% 10.98/4.58  Index Deletion       : 0.00
% 10.98/4.58  Index Matching       : 0.00
% 10.98/4.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
