%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:44 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 130 expanded)
%              Number of leaves         :   34 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  108 ( 234 expanded)
%              Number of equality atoms :   14 (  34 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_68,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(k1_setfam_1(B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_setfam_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(c_62,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_74,plain,(
    ! [A_77,B_78] : k1_enumset1(A_77,A_77,B_78) = k2_tarski(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [E_14,A_8,B_9] : r2_hidden(E_14,k1_enumset1(A_8,B_9,E_14)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_83,plain,(
    ! [B_78,A_77] : r2_hidden(B_78,k2_tarski(A_77,B_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_14])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_144,plain,(
    ! [B_100,C_101,A_102] :
      ( r1_tarski(k1_setfam_1(B_100),C_101)
      | ~ r1_tarski(A_102,C_101)
      | ~ r2_hidden(A_102,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_151,plain,(
    ! [B_103,B_104] :
      ( r1_tarski(k1_setfam_1(B_103),B_104)
      | ~ r2_hidden(B_104,B_103) ) ),
    inference(resolution,[status(thm)],[c_6,c_144])).

tff(c_52,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(A_44,k1_zfmisc_1(B_45))
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_109,plain,(
    ! [B_87,A_88] :
      ( v1_relat_1(B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_88))
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_113,plain,(
    ! [A_44,B_45] :
      ( v1_relat_1(A_44)
      | ~ v1_relat_1(B_45)
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_52,c_109])).

tff(c_170,plain,(
    ! [B_105,B_106] :
      ( v1_relat_1(k1_setfam_1(B_105))
      | ~ v1_relat_1(B_106)
      | ~ r2_hidden(B_106,B_105) ) ),
    inference(resolution,[status(thm)],[c_151,c_113])).

tff(c_172,plain,(
    ! [A_77,B_78] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(A_77,B_78)))
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_83,c_170])).

tff(c_182,plain,(
    ! [A_77,B_78] :
      ( v1_relat_1(k3_xboole_0(A_77,B_78))
      | ~ v1_relat_1(B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_172])).

tff(c_66,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_188,plain,(
    ! [A_107,B_108,C_109] :
      ( r1_tarski(A_107,k3_xboole_0(B_108,C_109))
      | ~ r1_tarski(A_107,C_109)
      | ~ r1_tarski(A_107,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_124,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(B_93,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,k3_xboole_0(A_3,B_4)) ) ),
    inference(resolution,[status(thm)],[c_8,c_124])).

tff(c_194,plain,(
    ! [B_108,C_109] :
      ( k3_xboole_0(B_108,C_109) = B_108
      | ~ r1_tarski(B_108,C_109)
      | ~ r1_tarski(B_108,B_108) ) ),
    inference(resolution,[status(thm)],[c_188,c_129])).

tff(c_211,plain,(
    ! [B_112,C_113] :
      ( k3_xboole_0(B_112,C_113) = B_112
      | ~ r1_tarski(B_112,C_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_194])).

tff(c_227,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_211])).

tff(c_1060,plain,(
    ! [B_214,A_215,B_216] :
      ( r1_tarski(k1_setfam_1(B_214),A_215)
      | ~ r2_hidden(k3_xboole_0(A_215,B_216),B_214) ) ),
    inference(resolution,[status(thm)],[c_8,c_144])).

tff(c_1070,plain,(
    ! [A_77,A_215,B_216] : r1_tarski(k1_setfam_1(k2_tarski(A_77,k3_xboole_0(A_215,B_216))),A_215) ),
    inference(resolution,[status(thm)],[c_83,c_1060])).

tff(c_1094,plain,(
    ! [A_217,A_218,B_219] : r1_tarski(k3_xboole_0(A_217,k3_xboole_0(A_218,B_219)),A_218) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1070])).

tff(c_1114,plain,(
    ! [A_217,B_2] : r1_tarski(k3_xboole_0(A_217,B_2),B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_1094])).

tff(c_2357,plain,(
    ! [C_299,A_300,B_301] :
      ( r1_tarski(k5_relat_1(C_299,A_300),k5_relat_1(C_299,B_301))
      | ~ r1_tarski(A_300,B_301)
      | ~ v1_relat_1(C_299)
      | ~ v1_relat_1(B_301)
      | ~ v1_relat_1(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_964,plain,(
    ! [C_196,A_197,B_198] :
      ( r1_tarski(k5_relat_1(C_196,A_197),k5_relat_1(C_196,B_198))
      | ~ r1_tarski(A_197,B_198)
      | ~ v1_relat_1(C_196)
      | ~ v1_relat_1(B_198)
      | ~ v1_relat_1(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_60,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k5_relat_1('#skF_3','#skF_4'),k5_relat_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_209,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_188,c_60])).

tff(c_255,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_967,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_964,c_255])).

tff(c_980,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_8,c_967])).

tff(c_987,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_182,c_980])).

tff(c_994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_987])).

tff(c_995,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_2363,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_2357,c_995])).

tff(c_2377,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_66,c_1114,c_2363])).

tff(c_2384,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_182,c_2377])).

tff(c_2391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:50:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.65  
% 3.47/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.65  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.47/1.65  
% 3.47/1.65  %Foreground sorts:
% 3.47/1.65  
% 3.47/1.65  
% 3.47/1.65  %Background operators:
% 3.47/1.65  
% 3.47/1.65  
% 3.47/1.65  %Foreground operators:
% 3.47/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.65  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.47/1.65  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.47/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.47/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.47/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.47/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.47/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.65  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.47/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.65  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.47/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.47/1.65  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.47/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.47/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.65  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.47/1.65  
% 3.83/1.66  tff(f_108, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 3.83/1.66  tff(f_68, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.83/1.66  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.83/1.66  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.83/1.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.83/1.66  tff(f_78, axiom, (![A, B, C]: ((r2_hidden(A, B) & r1_tarski(A, C)) => r1_tarski(k1_setfam_1(B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_setfam_1)).
% 3.83/1.66  tff(f_72, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.83/1.66  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.83/1.66  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.83/1.66  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.83/1.66  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 3.83/1.66  tff(c_62, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.83/1.66  tff(c_48, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.83/1.66  tff(c_74, plain, (![A_77, B_78]: (k1_enumset1(A_77, A_77, B_78)=k2_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.83/1.66  tff(c_14, plain, (![E_14, A_8, B_9]: (r2_hidden(E_14, k1_enumset1(A_8, B_9, E_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.83/1.66  tff(c_83, plain, (![B_78, A_77]: (r2_hidden(B_78, k2_tarski(A_77, B_78)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_14])).
% 3.83/1.66  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.83/1.66  tff(c_144, plain, (![B_100, C_101, A_102]: (r1_tarski(k1_setfam_1(B_100), C_101) | ~r1_tarski(A_102, C_101) | ~r2_hidden(A_102, B_100))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.83/1.66  tff(c_151, plain, (![B_103, B_104]: (r1_tarski(k1_setfam_1(B_103), B_104) | ~r2_hidden(B_104, B_103))), inference(resolution, [status(thm)], [c_6, c_144])).
% 3.83/1.66  tff(c_52, plain, (![A_44, B_45]: (m1_subset_1(A_44, k1_zfmisc_1(B_45)) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.83/1.66  tff(c_109, plain, (![B_87, A_88]: (v1_relat_1(B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_88)) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.83/1.66  tff(c_113, plain, (![A_44, B_45]: (v1_relat_1(A_44) | ~v1_relat_1(B_45) | ~r1_tarski(A_44, B_45))), inference(resolution, [status(thm)], [c_52, c_109])).
% 3.83/1.66  tff(c_170, plain, (![B_105, B_106]: (v1_relat_1(k1_setfam_1(B_105)) | ~v1_relat_1(B_106) | ~r2_hidden(B_106, B_105))), inference(resolution, [status(thm)], [c_151, c_113])).
% 3.83/1.66  tff(c_172, plain, (![A_77, B_78]: (v1_relat_1(k1_setfam_1(k2_tarski(A_77, B_78))) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_83, c_170])).
% 3.83/1.66  tff(c_182, plain, (![A_77, B_78]: (v1_relat_1(k3_xboole_0(A_77, B_78)) | ~v1_relat_1(B_78))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_172])).
% 3.83/1.66  tff(c_66, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.83/1.66  tff(c_188, plain, (![A_107, B_108, C_109]: (r1_tarski(A_107, k3_xboole_0(B_108, C_109)) | ~r1_tarski(A_107, C_109) | ~r1_tarski(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.83/1.66  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.83/1.66  tff(c_124, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(B_93, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.83/1.66  tff(c_129, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, k3_xboole_0(A_3, B_4)))), inference(resolution, [status(thm)], [c_8, c_124])).
% 3.83/1.66  tff(c_194, plain, (![B_108, C_109]: (k3_xboole_0(B_108, C_109)=B_108 | ~r1_tarski(B_108, C_109) | ~r1_tarski(B_108, B_108))), inference(resolution, [status(thm)], [c_188, c_129])).
% 3.83/1.66  tff(c_211, plain, (![B_112, C_113]: (k3_xboole_0(B_112, C_113)=B_112 | ~r1_tarski(B_112, C_113))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_194])).
% 3.83/1.66  tff(c_227, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_211])).
% 3.83/1.66  tff(c_1060, plain, (![B_214, A_215, B_216]: (r1_tarski(k1_setfam_1(B_214), A_215) | ~r2_hidden(k3_xboole_0(A_215, B_216), B_214))), inference(resolution, [status(thm)], [c_8, c_144])).
% 3.83/1.66  tff(c_1070, plain, (![A_77, A_215, B_216]: (r1_tarski(k1_setfam_1(k2_tarski(A_77, k3_xboole_0(A_215, B_216))), A_215))), inference(resolution, [status(thm)], [c_83, c_1060])).
% 3.83/1.66  tff(c_1094, plain, (![A_217, A_218, B_219]: (r1_tarski(k3_xboole_0(A_217, k3_xboole_0(A_218, B_219)), A_218))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1070])).
% 3.83/1.66  tff(c_1114, plain, (![A_217, B_2]: (r1_tarski(k3_xboole_0(A_217, B_2), B_2))), inference(superposition, [status(thm), theory('equality')], [c_227, c_1094])).
% 3.83/1.66  tff(c_2357, plain, (![C_299, A_300, B_301]: (r1_tarski(k5_relat_1(C_299, A_300), k5_relat_1(C_299, B_301)) | ~r1_tarski(A_300, B_301) | ~v1_relat_1(C_299) | ~v1_relat_1(B_301) | ~v1_relat_1(A_300))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.83/1.66  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.83/1.66  tff(c_964, plain, (![C_196, A_197, B_198]: (r1_tarski(k5_relat_1(C_196, A_197), k5_relat_1(C_196, B_198)) | ~r1_tarski(A_197, B_198) | ~v1_relat_1(C_196) | ~v1_relat_1(B_198) | ~v1_relat_1(A_197))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.83/1.66  tff(c_60, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k5_relat_1('#skF_3', '#skF_4'), k5_relat_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.83/1.66  tff(c_209, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5')) | ~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_188, c_60])).
% 3.83/1.66  tff(c_255, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_209])).
% 3.83/1.66  tff(c_967, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_964, c_255])).
% 3.83/1.66  tff(c_980, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_8, c_967])).
% 3.83/1.66  tff(c_987, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_182, c_980])).
% 3.83/1.66  tff(c_994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_987])).
% 3.83/1.66  tff(c_995, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_209])).
% 3.83/1.66  tff(c_2363, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_2357, c_995])).
% 3.83/1.66  tff(c_2377, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_66, c_1114, c_2363])).
% 3.83/1.66  tff(c_2384, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_182, c_2377])).
% 3.83/1.66  tff(c_2391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_2384])).
% 3.83/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.66  
% 3.83/1.66  Inference rules
% 3.83/1.66  ----------------------
% 3.83/1.66  #Ref     : 0
% 3.83/1.66  #Sup     : 583
% 3.83/1.66  #Fact    : 0
% 3.83/1.66  #Define  : 0
% 3.83/1.66  #Split   : 2
% 3.83/1.66  #Chain   : 0
% 3.83/1.66  #Close   : 0
% 3.83/1.66  
% 3.83/1.66  Ordering : KBO
% 3.83/1.66  
% 3.83/1.66  Simplification rules
% 3.83/1.66  ----------------------
% 3.83/1.67  #Subsume      : 119
% 3.83/1.67  #Demod        : 274
% 3.83/1.67  #Tautology    : 243
% 3.83/1.67  #SimpNegUnit  : 0
% 3.83/1.67  #BackRed      : 0
% 3.83/1.67  
% 3.83/1.67  #Partial instantiations: 0
% 3.83/1.67  #Strategies tried      : 1
% 3.83/1.67  
% 3.83/1.67  Timing (in seconds)
% 3.83/1.67  ----------------------
% 3.83/1.67  Preprocessing        : 0.35
% 3.83/1.67  Parsing              : 0.19
% 3.83/1.67  CNF conversion       : 0.03
% 3.83/1.67  Main loop            : 0.52
% 3.83/1.67  Inferencing          : 0.18
% 3.83/1.67  Reduction            : 0.18
% 3.83/1.67  Demodulation         : 0.13
% 3.83/1.67  BG Simplification    : 0.03
% 3.83/1.67  Subsumption          : 0.10
% 3.83/1.67  Abstraction          : 0.03
% 3.83/1.67  MUC search           : 0.00
% 3.83/1.67  Cooper               : 0.00
% 3.83/1.67  Total                : 0.90
% 3.83/1.67  Index Insertion      : 0.00
% 3.83/1.67  Index Deletion       : 0.00
% 3.83/1.67  Index Matching       : 0.00
% 3.83/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
