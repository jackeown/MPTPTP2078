%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:23 EST 2020

% Result     : Theorem 15.02s
% Output     : CNFRefutation 15.16s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 135 expanded)
%              Number of leaves         :   35 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  101 ( 196 expanded)
%              Number of equality atoms :   19 (  49 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k3_xboole_0(k3_xboole_0(A_6,B_7),C_8) = k3_xboole_0(A_6,k3_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_460,plain,(
    ! [A_114,B_115,C_116] : k4_xboole_0(k3_xboole_0(A_114,B_115),C_116) = k3_xboole_0(A_114,k4_xboole_0(B_115,C_116)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_19,B_20] : k2_xboole_0(k3_xboole_0(A_19,B_20),k4_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_498,plain,(
    ! [A_114,B_115,C_116] : k2_xboole_0(k3_xboole_0(k3_xboole_0(A_114,B_115),C_116),k3_xboole_0(A_114,k4_xboole_0(B_115,C_116))) = k3_xboole_0(A_114,B_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_18])).

tff(c_542,plain,(
    ! [A_114,B_115,C_116] : k2_xboole_0(k3_xboole_0(A_114,k3_xboole_0(B_115,C_116)),k3_xboole_0(A_114,k4_xboole_0(B_115,C_116))) = k3_xboole_0(A_114,B_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_498])).

tff(c_652,plain,(
    ! [A_129,B_130,C_131] : r1_tarski(k2_xboole_0(k3_xboole_0(A_129,B_130),k3_xboole_0(A_129,C_131)),k2_xboole_0(B_130,C_131)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_673,plain,(
    ! [A_129,A_19,B_20] : r1_tarski(k2_xboole_0(k3_xboole_0(A_129,k3_xboole_0(A_19,B_20)),k3_xboole_0(A_129,k4_xboole_0(A_19,B_20))),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_652])).

tff(c_9943,plain,(
    ! [A_378,A_379] : r1_tarski(k3_xboole_0(A_378,A_379),A_379) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_673])).

tff(c_38,plain,(
    ! [A_37,B_38] :
      ( m1_subset_1(A_37,k1_zfmisc_1(B_38))
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_174,plain,(
    ! [B_80,A_81] :
      ( v1_relat_1(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_178,plain,(
    ! [A_37,B_38] :
      ( v1_relat_1(A_37)
      | ~ v1_relat_1(B_38)
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_38,c_174])).

tff(c_10019,plain,(
    ! [A_378,A_379] :
      ( v1_relat_1(k3_xboole_0(A_378,A_379))
      | ~ v1_relat_1(A_379) ) ),
    inference(resolution,[status(thm)],[c_9943,c_178])).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    ! [A_42,B_44] :
      ( r1_tarski(k2_relat_1(A_42),k2_relat_1(B_44))
      | ~ r1_tarski(A_42,B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_9773,plain,(
    ! [A_129,A_19] : r1_tarski(k3_xboole_0(A_129,A_19),A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_673])).

tff(c_20,plain,(
    ! [A_21,B_22] : r1_xboole_0(k4_xboole_0(A_21,B_22),B_22) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_53,plain,(
    ! [B_50,A_51] :
      ( r1_xboole_0(B_50,A_51)
      | ~ r1_xboole_0(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [B_22,A_21] : r1_xboole_0(B_22,k4_xboole_0(A_21,B_22)) ),
    inference(resolution,[status(thm)],[c_20,c_53])).

tff(c_63,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = A_56
      | ~ r1_xboole_0(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_70,plain,(
    ! [B_22,A_21] : k4_xboole_0(B_22,k4_xboole_0(A_21,B_22)) = B_22 ),
    inference(resolution,[status(thm)],[c_56,c_63])).

tff(c_265,plain,(
    ! [A_90,C_91,B_92] :
      ( r1_xboole_0(A_90,C_91)
      | ~ r1_tarski(A_90,k4_xboole_0(B_92,C_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1636,plain,(
    ! [A_182,A_183,B_184] :
      ( r1_xboole_0(A_182,k4_xboole_0(A_183,B_184))
      | ~ r1_tarski(A_182,B_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_265])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = A_23
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1660,plain,(
    ! [A_182,A_183,B_184] :
      ( k4_xboole_0(A_182,k4_xboole_0(A_183,B_184)) = A_182
      | ~ r1_tarski(A_182,B_184) ) ),
    inference(resolution,[status(thm)],[c_1636,c_22])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_706,plain,(
    ! [A_135,B_136,C_137] :
      ( r1_tarski(A_135,k4_xboole_0(B_136,C_137))
      | ~ r1_xboole_0(A_135,C_137)
      | ~ r1_tarski(A_135,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4836,plain,(
    ! [A_309,A_310,B_311] :
      ( r1_tarski(A_309,k3_xboole_0(A_310,B_311))
      | ~ r1_xboole_0(A_309,k4_xboole_0(A_310,B_311))
      | ~ r1_tarski(A_309,A_310) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_706])).

tff(c_42580,plain,(
    ! [A_934,A_935,B_936] :
      ( r1_tarski(A_934,k3_xboole_0(A_935,B_936))
      | ~ r1_tarski(A_934,A_935)
      | k4_xboole_0(A_934,k4_xboole_0(A_935,B_936)) != A_934 ) ),
    inference(resolution,[status(thm)],[c_24,c_4836])).

tff(c_46,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42683,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1'))
    | k4_xboole_0(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k4_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) != k2_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42580,c_46])).

tff(c_42900,plain,(
    k4_xboole_0(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k4_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) != k2_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_42683])).

tff(c_43404,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1660,c_42900])).

tff(c_43407,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_43404])).

tff(c_43410,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_9773,c_43407])).

tff(c_43413,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10019,c_43410])).

tff(c_43420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_43413])).

tff(c_43421,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_42683])).

tff(c_43425,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_43421])).

tff(c_43428,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_10,c_43425])).

tff(c_43431,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10019,c_43428])).

tff(c_43438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_43431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:49:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.02/6.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.16/6.55  
% 15.16/6.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.16/6.56  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 15.16/6.56  
% 15.16/6.56  %Foreground sorts:
% 15.16/6.56  
% 15.16/6.56  
% 15.16/6.56  %Background operators:
% 15.16/6.56  
% 15.16/6.56  
% 15.16/6.56  %Foreground operators:
% 15.16/6.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.16/6.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.16/6.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.16/6.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.16/6.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.16/6.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.16/6.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.16/6.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 15.16/6.56  tff('#skF_2', type, '#skF_2': $i).
% 15.16/6.56  tff('#skF_1', type, '#skF_1': $i).
% 15.16/6.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.16/6.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.16/6.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 15.16/6.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.16/6.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.16/6.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.16/6.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.16/6.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.16/6.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.16/6.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 15.16/6.56  
% 15.16/6.57  tff(f_97, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 15.16/6.57  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 15.16/6.57  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 15.16/6.57  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 15.16/6.57  tff(f_41, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 15.16/6.57  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 15.16/6.57  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 15.16/6.57  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 15.16/6.57  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 15.16/6.57  tff(f_49, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 15.16/6.57  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 15.16/6.57  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 15.16/6.57  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 15.16/6.57  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.16/6.57  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 15.16/6.57  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 15.16/6.57  tff(c_8, plain, (![A_6, B_7, C_8]: (k3_xboole_0(k3_xboole_0(A_6, B_7), C_8)=k3_xboole_0(A_6, k3_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 15.16/6.57  tff(c_460, plain, (![A_114, B_115, C_116]: (k4_xboole_0(k3_xboole_0(A_114, B_115), C_116)=k3_xboole_0(A_114, k4_xboole_0(B_115, C_116)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.16/6.57  tff(c_18, plain, (![A_19, B_20]: (k2_xboole_0(k3_xboole_0(A_19, B_20), k4_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.16/6.57  tff(c_498, plain, (![A_114, B_115, C_116]: (k2_xboole_0(k3_xboole_0(k3_xboole_0(A_114, B_115), C_116), k3_xboole_0(A_114, k4_xboole_0(B_115, C_116)))=k3_xboole_0(A_114, B_115))), inference(superposition, [status(thm), theory('equality')], [c_460, c_18])).
% 15.16/6.57  tff(c_542, plain, (![A_114, B_115, C_116]: (k2_xboole_0(k3_xboole_0(A_114, k3_xboole_0(B_115, C_116)), k3_xboole_0(A_114, k4_xboole_0(B_115, C_116)))=k3_xboole_0(A_114, B_115))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_498])).
% 15.16/6.57  tff(c_652, plain, (![A_129, B_130, C_131]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_129, B_130), k3_xboole_0(A_129, C_131)), k2_xboole_0(B_130, C_131)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.16/6.57  tff(c_673, plain, (![A_129, A_19, B_20]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_129, k3_xboole_0(A_19, B_20)), k3_xboole_0(A_129, k4_xboole_0(A_19, B_20))), A_19))), inference(superposition, [status(thm), theory('equality')], [c_18, c_652])).
% 15.16/6.57  tff(c_9943, plain, (![A_378, A_379]: (r1_tarski(k3_xboole_0(A_378, A_379), A_379))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_673])).
% 15.16/6.57  tff(c_38, plain, (![A_37, B_38]: (m1_subset_1(A_37, k1_zfmisc_1(B_38)) | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_71])).
% 15.16/6.57  tff(c_174, plain, (![B_80, A_81]: (v1_relat_1(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_78])).
% 15.16/6.57  tff(c_178, plain, (![A_37, B_38]: (v1_relat_1(A_37) | ~v1_relat_1(B_38) | ~r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_38, c_174])).
% 15.16/6.57  tff(c_10019, plain, (![A_378, A_379]: (v1_relat_1(k3_xboole_0(A_378, A_379)) | ~v1_relat_1(A_379))), inference(resolution, [status(thm)], [c_9943, c_178])).
% 15.16/6.57  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 15.16/6.57  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 15.16/6.57  tff(c_42, plain, (![A_42, B_44]: (r1_tarski(k2_relat_1(A_42), k2_relat_1(B_44)) | ~r1_tarski(A_42, B_44) | ~v1_relat_1(B_44) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_89])).
% 15.16/6.57  tff(c_9773, plain, (![A_129, A_19]: (r1_tarski(k3_xboole_0(A_129, A_19), A_19))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_673])).
% 15.16/6.57  tff(c_20, plain, (![A_21, B_22]: (r1_xboole_0(k4_xboole_0(A_21, B_22), B_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.16/6.57  tff(c_53, plain, (![B_50, A_51]: (r1_xboole_0(B_50, A_51) | ~r1_xboole_0(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_29])).
% 15.16/6.57  tff(c_56, plain, (![B_22, A_21]: (r1_xboole_0(B_22, k4_xboole_0(A_21, B_22)))), inference(resolution, [status(thm)], [c_20, c_53])).
% 15.16/6.57  tff(c_63, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=A_56 | ~r1_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.16/6.57  tff(c_70, plain, (![B_22, A_21]: (k4_xboole_0(B_22, k4_xboole_0(A_21, B_22))=B_22)), inference(resolution, [status(thm)], [c_56, c_63])).
% 15.16/6.57  tff(c_265, plain, (![A_90, C_91, B_92]: (r1_xboole_0(A_90, C_91) | ~r1_tarski(A_90, k4_xboole_0(B_92, C_91)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.16/6.57  tff(c_1636, plain, (![A_182, A_183, B_184]: (r1_xboole_0(A_182, k4_xboole_0(A_183, B_184)) | ~r1_tarski(A_182, B_184))), inference(superposition, [status(thm), theory('equality')], [c_70, c_265])).
% 15.16/6.57  tff(c_22, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=A_23 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.16/6.57  tff(c_1660, plain, (![A_182, A_183, B_184]: (k4_xboole_0(A_182, k4_xboole_0(A_183, B_184))=A_182 | ~r1_tarski(A_182, B_184))), inference(resolution, [status(thm)], [c_1636, c_22])).
% 15.16/6.57  tff(c_24, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k4_xboole_0(A_23, B_24)!=A_23)), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.16/6.57  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.16/6.57  tff(c_706, plain, (![A_135, B_136, C_137]: (r1_tarski(A_135, k4_xboole_0(B_136, C_137)) | ~r1_xboole_0(A_135, C_137) | ~r1_tarski(A_135, B_136))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.16/6.57  tff(c_4836, plain, (![A_309, A_310, B_311]: (r1_tarski(A_309, k3_xboole_0(A_310, B_311)) | ~r1_xboole_0(A_309, k4_xboole_0(A_310, B_311)) | ~r1_tarski(A_309, A_310))), inference(superposition, [status(thm), theory('equality')], [c_14, c_706])).
% 15.16/6.57  tff(c_42580, plain, (![A_934, A_935, B_936]: (r1_tarski(A_934, k3_xboole_0(A_935, B_936)) | ~r1_tarski(A_934, A_935) | k4_xboole_0(A_934, k4_xboole_0(A_935, B_936))!=A_934)), inference(resolution, [status(thm)], [c_24, c_4836])).
% 15.16/6.57  tff(c_46, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 15.16/6.57  tff(c_42683, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1')) | k4_xboole_0(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k4_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))!=k2_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42580, c_46])).
% 15.16/6.57  tff(c_42900, plain, (k4_xboole_0(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k4_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))!=k2_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_42683])).
% 15.16/6.57  tff(c_43404, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1660, c_42900])).
% 15.16/6.57  tff(c_43407, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_43404])).
% 15.16/6.57  tff(c_43410, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_9773, c_43407])).
% 15.16/6.57  tff(c_43413, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10019, c_43410])).
% 15.16/6.57  tff(c_43420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_43413])).
% 15.16/6.57  tff(c_43421, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_42683])).
% 15.16/6.57  tff(c_43425, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_43421])).
% 15.16/6.57  tff(c_43428, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_10, c_43425])).
% 15.16/6.57  tff(c_43431, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10019, c_43428])).
% 15.16/6.57  tff(c_43438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_43431])).
% 15.16/6.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.16/6.57  
% 15.16/6.57  Inference rules
% 15.16/6.57  ----------------------
% 15.16/6.57  #Ref     : 0
% 15.16/6.57  #Sup     : 10738
% 15.16/6.57  #Fact    : 0
% 15.16/6.57  #Define  : 0
% 15.16/6.57  #Split   : 2
% 15.16/6.57  #Chain   : 0
% 15.16/6.57  #Close   : 0
% 15.16/6.57  
% 15.16/6.57  Ordering : KBO
% 15.16/6.57  
% 15.16/6.57  Simplification rules
% 15.16/6.57  ----------------------
% 15.16/6.57  #Subsume      : 405
% 15.16/6.57  #Demod        : 10275
% 15.16/6.57  #Tautology    : 5813
% 15.16/6.57  #SimpNegUnit  : 12
% 15.16/6.57  #BackRed      : 8
% 15.16/6.57  
% 15.16/6.57  #Partial instantiations: 0
% 15.16/6.57  #Strategies tried      : 1
% 15.16/6.57  
% 15.16/6.57  Timing (in seconds)
% 15.16/6.57  ----------------------
% 15.27/6.58  Preprocessing        : 0.31
% 15.27/6.58  Parsing              : 0.17
% 15.27/6.58  CNF conversion       : 0.02
% 15.27/6.58  Main loop            : 5.48
% 15.27/6.58  Inferencing          : 0.87
% 15.27/6.58  Reduction            : 2.85
% 15.27/6.58  Demodulation         : 2.53
% 15.27/6.58  BG Simplification    : 0.11
% 15.27/6.58  Subsumption          : 1.33
% 15.27/6.58  Abstraction          : 0.15
% 15.27/6.58  MUC search           : 0.00
% 15.27/6.58  Cooper               : 0.00
% 15.27/6.58  Total                : 5.83
% 15.27/6.58  Index Insertion      : 0.00
% 15.27/6.58  Index Deletion       : 0.00
% 15.27/6.58  Index Matching       : 0.00
% 15.27/6.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
