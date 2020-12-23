%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:24 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 5.92s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 108 expanded)
%              Number of leaves         :   35 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 174 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_135,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_23,B_24] : r1_tarski(k4_xboole_0(A_23,B_24),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_176,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(A_83,B_84) = k1_xboole_0
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_194,plain,(
    ! [A_23,B_24] : k4_xboole_0(k4_xboole_0(A_23,B_24),A_23) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_176])).

tff(c_733,plain,(
    ! [A_123,C_124,B_125] :
      ( r1_xboole_0(A_123,k4_xboole_0(C_124,B_125))
      | ~ r1_tarski(A_123,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_746,plain,(
    ! [A_126,A_127] :
      ( r1_xboole_0(A_126,k1_xboole_0)
      | ~ r1_tarski(A_126,A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_733])).

tff(c_780,plain,(
    ! [B_2] : r1_xboole_0(B_2,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_746])).

tff(c_2634,plain,(
    ! [A_215,B_216,C_217] :
      ( r1_tarski(A_215,B_216)
      | ~ r1_xboole_0(A_215,C_217)
      | ~ r1_tarski(A_215,k2_xboole_0(B_216,C_217)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6534,plain,(
    ! [B_339,C_340] :
      ( r1_tarski(k2_xboole_0(B_339,C_340),B_339)
      | ~ r1_xboole_0(k2_xboole_0(B_339,C_340),C_340) ) ),
    inference(resolution,[status(thm)],[c_6,c_2634])).

tff(c_6551,plain,(
    ! [B_341] : r1_tarski(k2_xboole_0(B_341,k1_xboole_0),B_341) ),
    inference(resolution,[status(thm)],[c_780,c_6534])).

tff(c_783,plain,(
    ! [A_129,C_130,B_131] :
      ( r1_tarski(A_129,C_130)
      | ~ r1_tarski(k2_xboole_0(A_129,B_131),C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_799,plain,(
    ! [A_132,B_133] : r1_tarski(A_132,k2_xboole_0(A_132,B_133)) ),
    inference(resolution,[status(thm)],[c_6,c_783])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_810,plain,(
    ! [A_132,B_133] :
      ( k2_xboole_0(A_132,B_133) = A_132
      | ~ r1_tarski(k2_xboole_0(A_132,B_133),A_132) ) ),
    inference(resolution,[status(thm)],[c_799,c_2])).

tff(c_6617,plain,(
    ! [B_342] : k2_xboole_0(B_342,k1_xboole_0) = B_342 ),
    inference(resolution,[status(thm)],[c_6551,c_810])).

tff(c_1259,plain,(
    ! [A_162,B_163,C_164] : r1_tarski(k2_xboole_0(k3_xboole_0(A_162,B_163),k3_xboole_0(A_162,C_164)),k2_xboole_0(B_163,C_164)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_tarski(A_11,C_13)
      | ~ r1_tarski(k2_xboole_0(A_11,B_12),C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1283,plain,(
    ! [A_162,B_163,C_164] : r1_tarski(k3_xboole_0(A_162,B_163),k2_xboole_0(B_163,C_164)) ),
    inference(resolution,[status(thm)],[c_1259,c_18])).

tff(c_6688,plain,(
    ! [A_162,B_342] : r1_tarski(k3_xboole_0(A_162,B_342),B_342) ),
    inference(superposition,[status(thm),theory(equality)],[c_6617,c_1283])).

tff(c_80,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_64,plain,(
    ! [A_48,B_49] :
      ( v1_relat_1(k3_xboole_0(A_48,B_49))
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_78,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3709,plain,(
    ! [A_259,B_260] :
      ( r1_tarski(k2_relat_1(A_259),k2_relat_1(B_260))
      | ~ r1_tarski(A_259,B_260)
      | ~ v1_relat_1(B_260)
      | ~ v1_relat_1(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_20,plain,(
    ! [A_14,B_15] : r1_tarski(k3_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2286,plain,(
    ! [A_205,B_206] :
      ( r1_tarski(k2_relat_1(A_205),k2_relat_1(B_206))
      | ~ r1_tarski(A_205,B_206)
      | ~ v1_relat_1(B_206)
      | ~ v1_relat_1(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1047,plain,(
    ! [A_152,B_153,C_154] :
      ( r1_tarski(A_152,k3_xboole_0(B_153,C_154))
      | ~ r1_tarski(A_152,C_154)
      | ~ r1_tarski(A_152,B_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_76,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1072,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1047,c_76])).

tff(c_1323,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1072])).

tff(c_2289,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2286,c_1323])).

tff(c_2299,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_20,c_2289])).

tff(c_2305,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2299])).

tff(c_2309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2305])).

tff(c_2310,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1072])).

tff(c_3718,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_3709,c_2310])).

tff(c_3732,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3718])).

tff(c_4682,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3732])).

tff(c_4685,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_4682])).

tff(c_4689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4685])).

tff(c_4690,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_3732])).

tff(c_6770,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6688,c_4690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:25:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.27  
% 5.92/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.92/2.28  
% 5.92/2.28  %Foreground sorts:
% 5.92/2.28  
% 5.92/2.28  
% 5.92/2.28  %Background operators:
% 5.92/2.28  
% 5.92/2.28  
% 5.92/2.28  %Foreground operators:
% 5.92/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.92/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.92/2.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.92/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.92/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.92/2.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.92/2.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.92/2.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.92/2.28  tff('#skF_3', type, '#skF_3': $i).
% 5.92/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.92/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.92/2.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.92/2.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.92/2.28  tff('#skF_4', type, '#skF_4': $i).
% 5.92/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.92/2.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.92/2.28  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 5.92/2.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.92/2.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.92/2.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.92/2.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.92/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.92/2.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.92/2.28  
% 5.92/2.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.92/2.29  tff(f_63, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.92/2.29  tff(f_67, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 5.92/2.29  tff(f_81, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 5.92/2.29  tff(f_77, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 5.92/2.29  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.92/2.29  tff(f_61, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 5.92/2.29  tff(f_143, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 5.92/2.29  tff(f_112, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 5.92/2.29  tff(f_135, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 5.92/2.29  tff(f_51, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.92/2.29  tff(f_57, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.92/2.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.92/2.29  tff(c_28, plain, (![A_23, B_24]: (r1_tarski(k4_xboole_0(A_23, B_24), A_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.92/2.29  tff(c_176, plain, (![A_83, B_84]: (k4_xboole_0(A_83, B_84)=k1_xboole_0 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.92/2.29  tff(c_194, plain, (![A_23, B_24]: (k4_xboole_0(k4_xboole_0(A_23, B_24), A_23)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_176])).
% 5.92/2.29  tff(c_733, plain, (![A_123, C_124, B_125]: (r1_xboole_0(A_123, k4_xboole_0(C_124, B_125)) | ~r1_tarski(A_123, B_125))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.92/2.29  tff(c_746, plain, (![A_126, A_127]: (r1_xboole_0(A_126, k1_xboole_0) | ~r1_tarski(A_126, A_127))), inference(superposition, [status(thm), theory('equality')], [c_194, c_733])).
% 5.92/2.29  tff(c_780, plain, (![B_2]: (r1_xboole_0(B_2, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_746])).
% 5.92/2.29  tff(c_2634, plain, (![A_215, B_216, C_217]: (r1_tarski(A_215, B_216) | ~r1_xboole_0(A_215, C_217) | ~r1_tarski(A_215, k2_xboole_0(B_216, C_217)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.92/2.29  tff(c_6534, plain, (![B_339, C_340]: (r1_tarski(k2_xboole_0(B_339, C_340), B_339) | ~r1_xboole_0(k2_xboole_0(B_339, C_340), C_340))), inference(resolution, [status(thm)], [c_6, c_2634])).
% 5.92/2.29  tff(c_6551, plain, (![B_341]: (r1_tarski(k2_xboole_0(B_341, k1_xboole_0), B_341))), inference(resolution, [status(thm)], [c_780, c_6534])).
% 5.92/2.29  tff(c_783, plain, (![A_129, C_130, B_131]: (r1_tarski(A_129, C_130) | ~r1_tarski(k2_xboole_0(A_129, B_131), C_130))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.92/2.29  tff(c_799, plain, (![A_132, B_133]: (r1_tarski(A_132, k2_xboole_0(A_132, B_133)))), inference(resolution, [status(thm)], [c_6, c_783])).
% 5.92/2.29  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.92/2.29  tff(c_810, plain, (![A_132, B_133]: (k2_xboole_0(A_132, B_133)=A_132 | ~r1_tarski(k2_xboole_0(A_132, B_133), A_132))), inference(resolution, [status(thm)], [c_799, c_2])).
% 5.92/2.29  tff(c_6617, plain, (![B_342]: (k2_xboole_0(B_342, k1_xboole_0)=B_342)), inference(resolution, [status(thm)], [c_6551, c_810])).
% 5.92/2.29  tff(c_1259, plain, (![A_162, B_163, C_164]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_162, B_163), k3_xboole_0(A_162, C_164)), k2_xboole_0(B_163, C_164)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.92/2.29  tff(c_18, plain, (![A_11, C_13, B_12]: (r1_tarski(A_11, C_13) | ~r1_tarski(k2_xboole_0(A_11, B_12), C_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.92/2.29  tff(c_1283, plain, (![A_162, B_163, C_164]: (r1_tarski(k3_xboole_0(A_162, B_163), k2_xboole_0(B_163, C_164)))), inference(resolution, [status(thm)], [c_1259, c_18])).
% 5.92/2.29  tff(c_6688, plain, (![A_162, B_342]: (r1_tarski(k3_xboole_0(A_162, B_342), B_342))), inference(superposition, [status(thm), theory('equality')], [c_6617, c_1283])).
% 5.92/2.29  tff(c_80, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.92/2.29  tff(c_64, plain, (![A_48, B_49]: (v1_relat_1(k3_xboole_0(A_48, B_49)) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.92/2.29  tff(c_78, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.92/2.29  tff(c_3709, plain, (![A_259, B_260]: (r1_tarski(k2_relat_1(A_259), k2_relat_1(B_260)) | ~r1_tarski(A_259, B_260) | ~v1_relat_1(B_260) | ~v1_relat_1(A_259))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.92/2.29  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(k3_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.92/2.29  tff(c_2286, plain, (![A_205, B_206]: (r1_tarski(k2_relat_1(A_205), k2_relat_1(B_206)) | ~r1_tarski(A_205, B_206) | ~v1_relat_1(B_206) | ~v1_relat_1(A_205))), inference(cnfTransformation, [status(thm)], [f_135])).
% 5.92/2.29  tff(c_1047, plain, (![A_152, B_153, C_154]: (r1_tarski(A_152, k3_xboole_0(B_153, C_154)) | ~r1_tarski(A_152, C_154) | ~r1_tarski(A_152, B_153))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.92/2.29  tff(c_76, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 5.92/2.29  tff(c_1072, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1047, c_76])).
% 5.92/2.29  tff(c_1323, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1072])).
% 5.92/2.29  tff(c_2289, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2286, c_1323])).
% 5.92/2.29  tff(c_2299, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_20, c_2289])).
% 5.92/2.29  tff(c_2305, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_2299])).
% 5.92/2.29  tff(c_2309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_2305])).
% 5.92/2.29  tff(c_2310, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1072])).
% 5.92/2.29  tff(c_3718, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_3709, c_2310])).
% 5.92/2.29  tff(c_3732, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3718])).
% 5.92/2.29  tff(c_4682, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_3732])).
% 5.92/2.29  tff(c_4685, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_4682])).
% 5.92/2.29  tff(c_4689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_4685])).
% 5.92/2.29  tff(c_4690, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_3732])).
% 5.92/2.29  tff(c_6770, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6688, c_4690])).
% 5.92/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.29  
% 5.92/2.29  Inference rules
% 5.92/2.29  ----------------------
% 5.92/2.29  #Ref     : 0
% 5.92/2.29  #Sup     : 1604
% 5.92/2.29  #Fact    : 0
% 5.92/2.29  #Define  : 0
% 5.92/2.29  #Split   : 4
% 5.92/2.29  #Chain   : 0
% 5.92/2.29  #Close   : 0
% 5.92/2.29  
% 5.92/2.29  Ordering : KBO
% 5.92/2.29  
% 5.92/2.29  Simplification rules
% 5.92/2.29  ----------------------
% 5.92/2.29  #Subsume      : 219
% 5.92/2.29  #Demod        : 1344
% 5.92/2.29  #Tautology    : 1030
% 5.92/2.29  #SimpNegUnit  : 4
% 5.92/2.29  #BackRed      : 10
% 5.92/2.29  
% 5.92/2.29  #Partial instantiations: 0
% 5.92/2.29  #Strategies tried      : 1
% 5.92/2.29  
% 5.92/2.29  Timing (in seconds)
% 5.92/2.29  ----------------------
% 5.92/2.29  Preprocessing        : 0.37
% 5.92/2.29  Parsing              : 0.21
% 5.92/2.29  CNF conversion       : 0.03
% 5.92/2.29  Main loop            : 1.09
% 5.92/2.29  Inferencing          : 0.35
% 5.92/2.29  Reduction            : 0.42
% 5.92/2.29  Demodulation         : 0.32
% 5.92/2.29  BG Simplification    : 0.04
% 5.92/2.29  Subsumption          : 0.20
% 5.92/2.29  Abstraction          : 0.05
% 5.92/2.29  MUC search           : 0.00
% 5.92/2.29  Cooper               : 0.00
% 5.92/2.29  Total                : 1.49
% 5.92/2.29  Index Insertion      : 0.00
% 5.92/2.30  Index Deletion       : 0.00
% 5.92/2.30  Index Matching       : 0.00
% 5.92/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
