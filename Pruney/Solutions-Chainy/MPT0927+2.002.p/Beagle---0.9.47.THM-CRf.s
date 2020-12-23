%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:23 EST 2020

% Result     : Theorem 10.89s
% Output     : CNFRefutation 11.21s
% Verified   : 
% Statistics : Number of formulae       :  343 (1631 expanded)
%              Number of leaves         :   42 ( 532 expanded)
%              Depth                    :   12
%              Number of atoms          :  607 (5441 expanded)
%              Number of equality atoms :  251 (2048 expanded)
%              Maximal formula depth    :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_13 > #skF_9 > #skF_8 > #skF_2 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(A))
       => ! [F] :
            ( m1_subset_1(F,k1_zfmisc_1(B))
           => ! [G] :
                ( m1_subset_1(G,k1_zfmisc_1(C))
               => ! [H] :
                    ( m1_subset_1(H,k1_zfmisc_1(D))
                   => ! [I] :
                        ( m1_subset_1(I,k4_zfmisc_1(A,B,C,D))
                       => ( r2_hidden(I,k4_zfmisc_1(E,F,G,H))
                         => ( r2_hidden(k8_mcart_1(A,B,C,D,I),E)
                            & r2_hidden(k9_mcart_1(A,B,C,D,I),F)
                            & r2_hidden(k10_mcart_1(A,B,C,D,I),G)
                            & r2_hidden(k11_mcart_1(A,B,C,D,I),H) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_mcart_1)).

tff(f_49,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_59,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ( k8_mcart_1(A,B,C,D,E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k9_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k10_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(E))
                & k11_mcart_1(A,B,C,D,E) = k2_mcart_1(E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_26,plain,(
    ! [A_15] : ~ v1_xboole_0(k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_94,plain,(
    ! [A_71,B_72] :
      ( r2_hidden(A_71,B_72)
      | v1_xboole_0(B_72)
      | ~ m1_subset_1(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_102,plain,(
    ! [A_71,A_10] :
      ( r1_tarski(A_71,A_10)
      | v1_xboole_0(k1_zfmisc_1(A_10))
      | ~ m1_subset_1(A_71,k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_94,c_14])).

tff(c_111,plain,(
    ! [A_73,A_74] :
      ( r1_tarski(A_73,A_74)
      | ~ m1_subset_1(A_73,k1_zfmisc_1(A_74)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_102])).

tff(c_124,plain,(
    r1_tarski('#skF_11','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_111])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9182,plain,(
    ! [C_1193,B_1194,A_1195] :
      ( r2_hidden(C_1193,B_1194)
      | ~ r2_hidden(C_1193,A_1195)
      | ~ r1_tarski(A_1195,B_1194) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9201,plain,(
    ! [A_1196,B_1197] :
      ( r2_hidden('#skF_1'(A_1196),B_1197)
      | ~ r1_tarski(A_1196,B_1197)
      | v1_xboole_0(A_1196) ) ),
    inference(resolution,[status(thm)],[c_4,c_9182])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9222,plain,(
    ! [B_1198,A_1199] :
      ( ~ v1_xboole_0(B_1198)
      | ~ r1_tarski(A_1199,B_1198)
      | v1_xboole_0(A_1199) ) ),
    inference(resolution,[status(thm)],[c_9201,c_2])).

tff(c_9251,plain,
    ( ~ v1_xboole_0('#skF_7')
    | v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_124,c_9222])).

tff(c_9266,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_9251])).

tff(c_52,plain,(
    m1_subset_1('#skF_12',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_125,plain,(
    r1_tarski('#skF_12','#skF_8') ),
    inference(resolution,[status(thm)],[c_52,c_111])).

tff(c_9250,plain,
    ( ~ v1_xboole_0('#skF_8')
    | v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_125,c_9222])).

tff(c_9267,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_9250])).

tff(c_56,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_126,plain,(
    r1_tarski('#skF_10','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_111])).

tff(c_9249,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_126,c_9222])).

tff(c_9265,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_9249])).

tff(c_48,plain,(
    r2_hidden('#skF_13',k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_9268,plain,(
    ! [A_1201,B_1202,C_1203,D_1204] : k2_zfmisc_1(k3_zfmisc_1(A_1201,B_1202,C_1203),D_1204) = k4_zfmisc_1(A_1201,B_1202,C_1203,D_1204) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ! [A_25,C_27,B_26] :
      ( r2_hidden(k2_mcart_1(A_25),C_27)
      | ~ r2_hidden(A_25,k2_zfmisc_1(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_9891,plain,(
    ! [A_1295,B_1298,A_1296,C_1299,D_1297] :
      ( r2_hidden(k2_mcart_1(A_1295),D_1297)
      | ~ r2_hidden(A_1295,k4_zfmisc_1(A_1296,B_1298,C_1299,D_1297)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9268,c_34])).

tff(c_9929,plain,(
    r2_hidden(k2_mcart_1('#skF_13'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_48,c_9891])).

tff(c_46,plain,
    ( ~ r2_hidden(k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_12')
    | ~ r2_hidden(k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_11')
    | ~ r2_hidden(k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_10')
    | ~ r2_hidden(k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_128,plain,(
    ~ r2_hidden(k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_180,plain,(
    ! [C_86,B_87,A_88] :
      ( r2_hidden(C_86,B_87)
      | ~ r2_hidden(C_86,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_223,plain,(
    ! [A_93,B_94] :
      ( r2_hidden('#skF_1'(A_93),B_94)
      | ~ r1_tarski(A_93,B_94)
      | v1_xboole_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_4,c_180])).

tff(c_244,plain,(
    ! [B_95,A_96] :
      ( ~ v1_xboole_0(B_95)
      | ~ r1_tarski(A_96,B_95)
      | v1_xboole_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_223,c_2])).

tff(c_270,plain,
    ( ~ v1_xboole_0('#skF_8')
    | v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_125,c_244])).

tff(c_292,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_269,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_126,c_244])).

tff(c_290,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_58,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_127,plain,(
    r1_tarski('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_111])).

tff(c_268,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_127,c_244])).

tff(c_273,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_50,plain,(
    m1_subset_1('#skF_13',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_670,plain,(
    ! [B_166,C_165,D_168,E_167,A_164] :
      ( k11_mcart_1(A_164,B_166,C_165,D_168,E_167) = k2_mcart_1(E_167)
      | ~ m1_subset_1(E_167,k4_zfmisc_1(A_164,B_166,C_165,D_168))
      | k1_xboole_0 = D_168
      | k1_xboole_0 = C_165
      | k1_xboole_0 = B_166
      | k1_xboole_0 = A_164 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_674,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13') = k2_mcart_1('#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_670])).

tff(c_738,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_674])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_740,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_12])).

tff(c_742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_740])).

tff(c_744,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_674])).

tff(c_757,plain,(
    ! [C_176,B_177,D_179,E_178,A_175] :
      ( k2_mcart_1(k1_mcart_1(E_178)) = k10_mcart_1(A_175,B_177,C_176,D_179,E_178)
      | ~ m1_subset_1(E_178,k4_zfmisc_1(A_175,B_177,C_176,D_179))
      | k1_xboole_0 = D_179
      | k1_xboole_0 = C_176
      | k1_xboole_0 = B_177
      | k1_xboole_0 = A_175 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_760,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_13')) = k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_757])).

tff(c_763,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_13')) = k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_744,c_760])).

tff(c_847,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_763])).

tff(c_852,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_847,c_12])).

tff(c_854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_852])).

tff(c_856,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_763])).

tff(c_271,plain,
    ( ~ v1_xboole_0('#skF_7')
    | v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_124,c_244])).

tff(c_291,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_913,plain,(
    ! [E_197,C_195,A_194,B_196,D_198] :
      ( k8_mcart_1(A_194,B_196,C_195,D_198,E_197) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_197)))
      | ~ m1_subset_1(E_197,k4_zfmisc_1(A_194,B_196,C_195,D_198))
      | k1_xboole_0 = D_198
      | k1_xboole_0 = C_195
      | k1_xboole_0 = B_196
      | k1_xboole_0 = A_194 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_915,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_913])).

tff(c_918,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_744,c_856,c_915])).

tff(c_2737,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_918])).

tff(c_2744,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2737,c_12])).

tff(c_2746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_291,c_2744])).

tff(c_2748,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_918])).

tff(c_830,plain,(
    ! [B_185,D_187,C_184,E_186,A_183] :
      ( k9_mcart_1(A_183,B_185,C_184,D_187,E_186) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_186)))
      | ~ m1_subset_1(E_186,k4_zfmisc_1(A_183,B_185,C_184,D_187))
      | k1_xboole_0 = D_187
      | k1_xboole_0 = C_184
      | k1_xboole_0 = B_185
      | k1_xboole_0 = A_183 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_832,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_830])).

tff(c_835,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_744,c_832])).

tff(c_2776,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_856,c_2748,c_835])).

tff(c_2777,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2776])).

tff(c_2785,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2777,c_12])).

tff(c_2787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_2785])).

tff(c_2789,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2776])).

tff(c_2747,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13') ),
    inference(splitRight,[status(thm)],[c_918])).

tff(c_3135,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_2789,c_2747])).

tff(c_274,plain,(
    ! [A_97,B_98,C_99,D_100] : k2_zfmisc_1(k3_zfmisc_1(A_97,B_98,C_99),D_100) = k4_zfmisc_1(A_97,B_98,C_99,D_100) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    ! [A_25,B_26,C_27] :
      ( r2_hidden(k1_mcart_1(A_25),B_26)
      | ~ r2_hidden(A_25,k2_zfmisc_1(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3718,plain,(
    ! [A_470,B_473,A_471,C_472,D_474] :
      ( r2_hidden(k1_mcart_1(A_470),k3_zfmisc_1(A_471,B_473,C_472))
      | ~ r2_hidden(A_470,k4_zfmisc_1(A_471,B_473,C_472,D_474)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_36])).

tff(c_3772,plain,(
    r2_hidden(k1_mcart_1('#skF_13'),k3_zfmisc_1('#skF_9','#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_48,c_3718])).

tff(c_163,plain,(
    ! [A_83,B_84,C_85] : k2_zfmisc_1(k2_zfmisc_1(A_83,B_84),C_85) = k3_zfmisc_1(A_83,B_84,C_85) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_171,plain,(
    ! [A_25,A_83,B_84,C_85] :
      ( r2_hidden(k1_mcart_1(A_25),k2_zfmisc_1(A_83,B_84))
      | ~ r2_hidden(A_25,k3_zfmisc_1(A_83,B_84,C_85)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_36])).

tff(c_3783,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_13')),k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_3772,c_171])).

tff(c_3793,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))),'#skF_9') ),
    inference(resolution,[status(thm)],[c_3783,c_36])).

tff(c_3801,plain,(
    r2_hidden(k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3135,c_3793])).

tff(c_3803,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_3801])).

tff(c_3804,plain,(
    v1_xboole_0('#skF_12') ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_3918,plain,(
    ! [B_505,A_502,C_504,A_503,D_506] :
      ( r2_hidden(k2_mcart_1(A_502),D_506)
      | ~ r2_hidden(A_502,k4_zfmisc_1(A_503,B_505,C_504,D_506)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_34])).

tff(c_3936,plain,(
    r2_hidden(k2_mcart_1('#skF_13'),'#skF_12') ),
    inference(resolution,[status(thm)],[c_48,c_3918])).

tff(c_3942,plain,(
    ~ v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_3936,c_2])).

tff(c_3947,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3804,c_3942])).

tff(c_3948,plain,(
    v1_xboole_0('#skF_11') ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_30,plain,(
    ! [A_18,B_19,C_20] : k2_zfmisc_1(k2_zfmisc_1(A_18,B_19),C_20) = k3_zfmisc_1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_208,plain,(
    ! [A_90,C_91,B_92] :
      ( r2_hidden(k2_mcart_1(A_90),C_91)
      | ~ r2_hidden(A_90,k2_zfmisc_1(B_92,C_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4663,plain,(
    ! [B_600,C_601] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_600,C_601))),C_601)
      | v1_xboole_0(k2_zfmisc_1(B_600,C_601)) ) ),
    inference(resolution,[status(thm)],[c_4,c_208])).

tff(c_4700,plain,(
    ! [C_602,B_603] :
      ( ~ v1_xboole_0(C_602)
      | v1_xboole_0(k2_zfmisc_1(B_603,C_602)) ) ),
    inference(resolution,[status(thm)],[c_4663,c_2])).

tff(c_4706,plain,(
    ! [C_20,A_18,B_19] :
      ( ~ v1_xboole_0(C_20)
      | v1_xboole_0(k3_zfmisc_1(A_18,B_19,C_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_4700])).

tff(c_32,plain,(
    ! [A_21,B_22,C_23,D_24] : k2_zfmisc_1(k3_zfmisc_1(A_21,B_22,C_23),D_24) = k4_zfmisc_1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_150,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_hidden(k1_mcart_1(A_80),B_81)
      | ~ r2_hidden(A_80,k2_zfmisc_1(B_81,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4600,plain,(
    ! [B_595,C_596] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_595,C_596))),B_595)
      | v1_xboole_0(k2_zfmisc_1(B_595,C_596)) ) ),
    inference(resolution,[status(thm)],[c_4,c_150])).

tff(c_4640,plain,(
    ! [B_597,C_598] :
      ( ~ v1_xboole_0(B_597)
      | v1_xboole_0(k2_zfmisc_1(B_597,C_598)) ) ),
    inference(resolution,[status(thm)],[c_4600,c_2])).

tff(c_4878,plain,(
    ! [A_626,B_627,C_628,D_629] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_626,B_627,C_628))
      | v1_xboole_0(k4_zfmisc_1(A_626,B_627,C_628,D_629)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_4640])).

tff(c_74,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_9','#skF_10','#skF_11','#skF_12')) ),
    inference(resolution,[status(thm)],[c_48,c_2])).

tff(c_4882,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_9','#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_4878,c_74])).

tff(c_4888,plain,(
    ~ v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_4706,c_4882])).

tff(c_4893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3948,c_4888])).

tff(c_4894,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_5101,plain,(
    ! [B_670,C_671] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_670,C_671))),C_671)
      | v1_xboole_0(k2_zfmisc_1(B_670,C_671)) ) ),
    inference(resolution,[status(thm)],[c_4,c_208])).

tff(c_5131,plain,(
    ! [C_671,B_670] :
      ( ~ v1_xboole_0(C_671)
      | v1_xboole_0(k2_zfmisc_1(B_670,C_671)) ) ),
    inference(resolution,[status(thm)],[c_5101,c_2])).

tff(c_5057,plain,(
    ! [B_663,C_664] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_663,C_664))),B_663)
      | v1_xboole_0(k2_zfmisc_1(B_663,C_664)) ) ),
    inference(resolution,[status(thm)],[c_4,c_150])).

tff(c_5093,plain,(
    ! [B_665,C_666] :
      ( ~ v1_xboole_0(B_665)
      | v1_xboole_0(k2_zfmisc_1(B_665,C_666)) ) ),
    inference(resolution,[status(thm)],[c_5057,c_2])).

tff(c_5099,plain,(
    ! [A_18,B_19,C_20] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_18,B_19))
      | v1_xboole_0(k3_zfmisc_1(A_18,B_19,C_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_5093])).

tff(c_7048,plain,(
    ! [A_895,B_896,C_897,D_898] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_895,B_896,C_897))
      | v1_xboole_0(k4_zfmisc_1(A_895,B_896,C_897,D_898)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_5093])).

tff(c_7052,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_9','#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_7048,c_74])).

tff(c_7060,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_5099,c_7052])).

tff(c_7115,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_5131,c_7060])).

tff(c_7122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4894,c_7115])).

tff(c_7123,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_8630,plain,(
    ! [B_1108,C_1109] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1108,C_1109))),B_1108)
      | v1_xboole_0(k2_zfmisc_1(B_1108,C_1109)) ) ),
    inference(resolution,[status(thm)],[c_4,c_150])).

tff(c_8663,plain,(
    ! [B_1108,C_1109] :
      ( ~ v1_xboole_0(B_1108)
      | v1_xboole_0(k2_zfmisc_1(B_1108,C_1109)) ) ),
    inference(resolution,[status(thm)],[c_8630,c_2])).

tff(c_8666,plain,(
    ! [B_1110,C_1111] :
      ( ~ v1_xboole_0(B_1110)
      | v1_xboole_0(k2_zfmisc_1(B_1110,C_1111)) ) ),
    inference(resolution,[status(thm)],[c_8630,c_2])).

tff(c_8672,plain,(
    ! [A_18,B_19,C_20] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_18,B_19))
      | v1_xboole_0(k3_zfmisc_1(A_18,B_19,C_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_8666])).

tff(c_9086,plain,(
    ! [A_1175,B_1176,C_1177,D_1178] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_1175,B_1176,C_1177))
      | v1_xboole_0(k4_zfmisc_1(A_1175,B_1176,C_1177,D_1178)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_8666])).

tff(c_9090,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_9','#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_9086,c_74])).

tff(c_9097,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_8672,c_9090])).

tff(c_9101,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_8663,c_9097])).

tff(c_9108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7123,c_9101])).

tff(c_9110,plain,(
    r2_hidden(k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_9131,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_9110,c_2])).

tff(c_9231,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_127,c_9222])).

tff(c_9248,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_9131,c_9231])).

tff(c_9866,plain,(
    ! [E_1284,C_1282,D_1285,A_1281,B_1283] :
      ( k11_mcart_1(A_1281,B_1283,C_1282,D_1285,E_1284) = k2_mcart_1(E_1284)
      | ~ m1_subset_1(E_1284,k4_zfmisc_1(A_1281,B_1283,C_1282,D_1285))
      | k1_xboole_0 = D_1285
      | k1_xboole_0 = C_1282
      | k1_xboole_0 = B_1283
      | k1_xboole_0 = A_1281 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_9870,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13') = k2_mcart_1('#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_9866])).

tff(c_9884,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_9870])).

tff(c_9886,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9884,c_12])).

tff(c_9888,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9248,c_9886])).

tff(c_9889,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8'
    | k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13') = k2_mcart_1('#skF_13') ),
    inference(splitRight,[status(thm)],[c_9870])).

tff(c_10001,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13') = k2_mcart_1('#skF_13') ),
    inference(splitLeft,[status(thm)],[c_9889])).

tff(c_9109,plain,
    ( ~ r2_hidden(k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_10')
    | ~ r2_hidden(k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_11')
    | ~ r2_hidden(k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_9132,plain,(
    ~ r2_hidden(k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_9109])).

tff(c_10007,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_13'),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10001,c_9132])).

tff(c_10010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9929,c_10007])).

tff(c_10011,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_9889])).

tff(c_10013,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10011])).

tff(c_10017,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10013,c_12])).

tff(c_10019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9265,c_10017])).

tff(c_10020,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_10011])).

tff(c_10028,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_10020])).

tff(c_10034,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10028,c_12])).

tff(c_10036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9267,c_10034])).

tff(c_10038,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_10020])).

tff(c_9890,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_9870])).

tff(c_10021,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_10011])).

tff(c_10022,plain,(
    ! [D_1313,B_1311,E_1312,A_1309,C_1310] :
      ( k8_mcart_1(A_1309,B_1311,C_1310,D_1313,E_1312) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_1312)))
      | ~ m1_subset_1(E_1312,k4_zfmisc_1(A_1309,B_1311,C_1310,D_1313))
      | k1_xboole_0 = D_1313
      | k1_xboole_0 = C_1310
      | k1_xboole_0 = B_1311
      | k1_xboole_0 = A_1309 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10024,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_10022])).

tff(c_10027,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_9890,c_10021,c_10024])).

tff(c_10039,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_10038,c_10027])).

tff(c_10040,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_10039])).

tff(c_10047,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10040,c_12])).

tff(c_10049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9266,c_10047])).

tff(c_10051,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_10039])).

tff(c_10037,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_10020])).

tff(c_10052,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10051,c_10037])).

tff(c_10053,plain,(
    v1_xboole_0('#skF_12') ),
    inference(splitRight,[status(thm)],[c_9250])).

tff(c_9167,plain,(
    ! [A_1190,C_1191,B_1192] :
      ( r2_hidden(k2_mcart_1(A_1190),C_1191)
      | ~ r2_hidden(A_1190,k2_zfmisc_1(B_1192,C_1191)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10172,plain,(
    ! [B_1340,C_1341] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1340,C_1341))),C_1341)
      | v1_xboole_0(k2_zfmisc_1(B_1340,C_1341)) ) ),
    inference(resolution,[status(thm)],[c_4,c_9167])).

tff(c_10210,plain,(
    ! [C_1343,B_1344] :
      ( ~ v1_xboole_0(C_1343)
      | v1_xboole_0(k2_zfmisc_1(B_1344,C_1343)) ) ),
    inference(resolution,[status(thm)],[c_10172,c_2])).

tff(c_10218,plain,(
    ! [D_1348,A_1349,B_1350,C_1351] :
      ( ~ v1_xboole_0(D_1348)
      | v1_xboole_0(k4_zfmisc_1(A_1349,B_1350,C_1351,D_1348)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_10210])).

tff(c_10221,plain,(
    ~ v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_10218,c_74])).

tff(c_10225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10053,c_10221])).

tff(c_10226,plain,(
    v1_xboole_0('#skF_11') ),
    inference(splitRight,[status(thm)],[c_9251])).

tff(c_11054,plain,(
    ! [B_1458,C_1459] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1458,C_1459))),C_1459)
      | v1_xboole_0(k2_zfmisc_1(B_1458,C_1459)) ) ),
    inference(resolution,[status(thm)],[c_4,c_9167])).

tff(c_11091,plain,(
    ! [C_1460,B_1461] :
      ( ~ v1_xboole_0(C_1460)
      | v1_xboole_0(k2_zfmisc_1(B_1461,C_1460)) ) ),
    inference(resolution,[status(thm)],[c_11054,c_2])).

tff(c_11097,plain,(
    ! [C_20,A_18,B_19] :
      ( ~ v1_xboole_0(C_20)
      | v1_xboole_0(k3_zfmisc_1(A_18,B_19,C_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_11091])).

tff(c_9152,plain,(
    ! [A_1187,B_1188,C_1189] :
      ( r2_hidden(k1_mcart_1(A_1187),B_1188)
      | ~ r2_hidden(A_1187,k2_zfmisc_1(B_1188,C_1189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10465,plain,(
    ! [B_1391,C_1392] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1391,C_1392))),B_1391)
      | v1_xboole_0(k2_zfmisc_1(B_1391,C_1392)) ) ),
    inference(resolution,[status(thm)],[c_4,c_9152])).

tff(c_10501,plain,(
    ! [B_1393,C_1394] :
      ( ~ v1_xboole_0(B_1393)
      | v1_xboole_0(k2_zfmisc_1(B_1393,C_1394)) ) ),
    inference(resolution,[status(thm)],[c_10465,c_2])).

tff(c_11499,plain,(
    ! [A_1510,B_1511,C_1512,D_1513] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_1510,B_1511,C_1512))
      | v1_xboole_0(k4_zfmisc_1(A_1510,B_1511,C_1512,D_1513)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_10501])).

tff(c_11503,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_9','#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_11499,c_74])).

tff(c_11506,plain,(
    ~ v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_11097,c_11503])).

tff(c_11513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10226,c_11506])).

tff(c_11514,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_9249])).

tff(c_11640,plain,(
    ! [B_1541,C_1542] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1541,C_1542))),C_1542)
      | v1_xboole_0(k2_zfmisc_1(B_1541,C_1542)) ) ),
    inference(resolution,[status(thm)],[c_4,c_9167])).

tff(c_11670,plain,(
    ! [C_1542,B_1541] :
      ( ~ v1_xboole_0(C_1542)
      | v1_xboole_0(k2_zfmisc_1(B_1541,C_1542)) ) ),
    inference(resolution,[status(thm)],[c_11640,c_2])).

tff(c_11697,plain,(
    ! [B_1554,C_1555] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1554,C_1555))),B_1554)
      | v1_xboole_0(k2_zfmisc_1(B_1554,C_1555)) ) ),
    inference(resolution,[status(thm)],[c_4,c_9152])).

tff(c_11733,plain,(
    ! [B_1556,C_1557] :
      ( ~ v1_xboole_0(B_1556)
      | v1_xboole_0(k2_zfmisc_1(B_1556,C_1557)) ) ),
    inference(resolution,[status(thm)],[c_11697,c_2])).

tff(c_11739,plain,(
    ! [A_18,B_19,C_20] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_18,B_19))
      | v1_xboole_0(k3_zfmisc_1(A_18,B_19,C_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_11733])).

tff(c_12851,plain,(
    ! [A_1676,B_1677,C_1678,D_1679] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_1676,B_1677,C_1678))
      | v1_xboole_0(k4_zfmisc_1(A_1676,B_1677,C_1678,D_1679)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_11733])).

tff(c_12855,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_9','#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_12851,c_74])).

tff(c_12862,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_11739,c_12855])).

tff(c_12869,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_11670,c_12862])).

tff(c_12874,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11514,c_12869])).

tff(c_12875,plain,
    ( ~ r2_hidden(k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_11')
    | ~ r2_hidden(k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_9109])).

tff(c_13128,plain,(
    ~ r2_hidden(k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_12875])).

tff(c_12876,plain,(
    r2_hidden(k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_12') ),
    inference(splitRight,[status(thm)],[c_9109])).

tff(c_12880,plain,(
    ~ v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_12876,c_2])).

tff(c_12896,plain,(
    ! [C_1683,B_1684,A_1685] :
      ( r2_hidden(C_1683,B_1684)
      | ~ r2_hidden(C_1683,A_1685)
      | ~ r1_tarski(A_1685,B_1684) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12960,plain,(
    ! [A_1693,B_1694] :
      ( r2_hidden('#skF_1'(A_1693),B_1694)
      | ~ r1_tarski(A_1693,B_1694)
      | v1_xboole_0(A_1693) ) ),
    inference(resolution,[status(thm)],[c_4,c_12896])).

tff(c_12981,plain,(
    ! [B_1695,A_1696] :
      ( ~ v1_xboole_0(B_1695)
      | ~ r1_tarski(A_1696,B_1695)
      | v1_xboole_0(A_1696) ) ),
    inference(resolution,[status(thm)],[c_12960,c_2])).

tff(c_12996,plain,
    ( ~ v1_xboole_0('#skF_8')
    | v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_125,c_12981])).

tff(c_13011,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_12880,c_12996])).

tff(c_13008,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_126,c_12981])).

tff(c_13030,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_13008])).

tff(c_12990,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_127,c_12981])).

tff(c_13007,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_9131,c_12990])).

tff(c_13481,plain,(
    ! [E_1760,C_1758,D_1761,B_1759,A_1757] :
      ( k11_mcart_1(A_1757,B_1759,C_1758,D_1761,E_1760) = k2_mcart_1(E_1760)
      | ~ m1_subset_1(E_1760,k4_zfmisc_1(A_1757,B_1759,C_1758,D_1761))
      | k1_xboole_0 = D_1761
      | k1_xboole_0 = C_1758
      | k1_xboole_0 = B_1759
      | k1_xboole_0 = A_1757 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_13485,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13') = k2_mcart_1('#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_13481])).

tff(c_13492,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_13485])).

tff(c_13494,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13492,c_12])).

tff(c_13496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13007,c_13494])).

tff(c_13498,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_13485])).

tff(c_13508,plain,(
    ! [B_1764,C_1763,D_1766,E_1765,A_1762] :
      ( k2_mcart_1(k1_mcart_1(E_1765)) = k10_mcart_1(A_1762,B_1764,C_1763,D_1766,E_1765)
      | ~ m1_subset_1(E_1765,k4_zfmisc_1(A_1762,B_1764,C_1763,D_1766))
      | k1_xboole_0 = D_1766
      | k1_xboole_0 = C_1763
      | k1_xboole_0 = B_1764
      | k1_xboole_0 = A_1762 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_13511,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_13')) = k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_13508])).

tff(c_13514,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_13')) = k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_13498,c_13511])).

tff(c_13715,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_13514])).

tff(c_13720,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13715,c_12])).

tff(c_13722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13030,c_13720])).

tff(c_13724,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_13514])).

tff(c_13012,plain,
    ( ~ v1_xboole_0('#skF_7')
    | v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_124,c_12981])).

tff(c_13031,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_13012])).

tff(c_13783,plain,(
    ! [D_1806,C_1803,B_1804,A_1802,E_1805] :
      ( k8_mcart_1(A_1802,B_1804,C_1803,D_1806,E_1805) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_1805)))
      | ~ m1_subset_1(E_1805,k4_zfmisc_1(A_1802,B_1804,C_1803,D_1806))
      | k1_xboole_0 = D_1806
      | k1_xboole_0 = C_1803
      | k1_xboole_0 = B_1804
      | k1_xboole_0 = A_1802 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_13785,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_13783])).

tff(c_13788,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_13498,c_13724,c_13785])).

tff(c_14607,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_13788])).

tff(c_14614,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14607,c_12])).

tff(c_14616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13031,c_14614])).

tff(c_14618,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_13788])).

tff(c_13663,plain,(
    ! [B_1782,C_1781,D_1784,E_1783,A_1780] :
      ( k9_mcart_1(A_1780,B_1782,C_1781,D_1784,E_1783) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_1783)))
      | ~ m1_subset_1(E_1783,k4_zfmisc_1(A_1780,B_1782,C_1781,D_1784))
      | k1_xboole_0 = D_1784
      | k1_xboole_0 = C_1781
      | k1_xboole_0 = B_1782
      | k1_xboole_0 = A_1780 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_13665,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_13663])).

tff(c_13668,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_13498,c_13665])).

tff(c_14824,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_13724,c_14618,c_13668])).

tff(c_14825,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_14824])).

tff(c_14833,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14825,c_12])).

tff(c_14835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13011,c_14833])).

tff(c_14836,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13') ),
    inference(splitRight,[status(thm)],[c_14824])).

tff(c_13014,plain,(
    ! [A_1697,B_1698,C_1699,D_1700] : k2_zfmisc_1(k3_zfmisc_1(A_1697,B_1698,C_1699),D_1700) = k4_zfmisc_1(A_1697,B_1698,C_1699,D_1700) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_15605,plain,(
    ! [D_2002,A_2004,B_2003,C_2000,A_2001] :
      ( r2_hidden(k1_mcart_1(A_2001),k3_zfmisc_1(A_2004,B_2003,C_2000))
      | ~ r2_hidden(A_2001,k4_zfmisc_1(A_2004,B_2003,C_2000,D_2002)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13014,c_36])).

tff(c_15663,plain,(
    r2_hidden(k1_mcart_1('#skF_13'),k3_zfmisc_1('#skF_9','#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_48,c_15605])).

tff(c_12918,plain,(
    ! [A_1686,B_1687,C_1688] :
      ( r2_hidden(k1_mcart_1(A_1686),B_1687)
      | ~ r2_hidden(A_1686,k2_zfmisc_1(B_1687,C_1688)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12920,plain,(
    ! [A_1686,A_18,B_19,C_20] :
      ( r2_hidden(k1_mcart_1(A_1686),k2_zfmisc_1(A_18,B_19))
      | ~ r2_hidden(A_1686,k3_zfmisc_1(A_18,B_19,C_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_12918])).

tff(c_15674,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_13')),k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_15663,c_12920])).

tff(c_15680,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))),'#skF_10') ),
    inference(resolution,[status(thm)],[c_15674,c_34])).

tff(c_15689,plain,(
    r2_hidden(k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14836,c_15680])).

tff(c_15691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13128,c_15689])).

tff(c_15692,plain,(
    ~ r2_hidden(k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_12875])).

tff(c_16916,plain,(
    ! [D_2146,C_2143,B_2144,E_2145,A_2142] :
      ( k11_mcart_1(A_2142,B_2144,C_2143,D_2146,E_2145) = k2_mcart_1(E_2145)
      | ~ m1_subset_1(E_2145,k4_zfmisc_1(A_2142,B_2144,C_2143,D_2146))
      | k1_xboole_0 = D_2146
      | k1_xboole_0 = C_2143
      | k1_xboole_0 = B_2144
      | k1_xboole_0 = A_2142 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16920,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13') = k2_mcart_1('#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_16916])).

tff(c_16966,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_16920])).

tff(c_16968,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16966,c_12])).

tff(c_16970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13007,c_16968])).

tff(c_16972,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_16920])).

tff(c_16975,plain,(
    ! [C_2152,E_2154,B_2153,D_2155,A_2151] :
      ( k2_mcart_1(k1_mcart_1(E_2154)) = k10_mcart_1(A_2151,B_2153,C_2152,D_2155,E_2154)
      | ~ m1_subset_1(E_2154,k4_zfmisc_1(A_2151,B_2153,C_2152,D_2155))
      | k1_xboole_0 = D_2155
      | k1_xboole_0 = C_2152
      | k1_xboole_0 = B_2153
      | k1_xboole_0 = A_2151 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_16978,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_13')) = k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_16975])).

tff(c_16981,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_13')) = k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_16972,c_16978])).

tff(c_17050,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_16981])).

tff(c_17055,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17050,c_12])).

tff(c_17057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13030,c_17055])).

tff(c_17059,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_16981])).

tff(c_17113,plain,(
    ! [D_2172,B_2170,C_2169,E_2171,A_2168] :
      ( k8_mcart_1(A_2168,B_2170,C_2169,D_2172,E_2171) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_2171)))
      | ~ m1_subset_1(E_2171,k4_zfmisc_1(A_2168,B_2170,C_2169,D_2172))
      | k1_xboole_0 = D_2172
      | k1_xboole_0 = C_2169
      | k1_xboole_0 = B_2170
      | k1_xboole_0 = A_2168 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_17115,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_17113])).

tff(c_17118,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_16972,c_17059,c_17115])).

tff(c_17276,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_17118])).

tff(c_17283,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17276,c_12])).

tff(c_17285,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13031,c_17283])).

tff(c_17287,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_17118])).

tff(c_17029,plain,(
    ! [A_2158,D_2162,C_2159,B_2160,E_2161] :
      ( k9_mcart_1(A_2158,B_2160,C_2159,D_2162,E_2161) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_2161)))
      | ~ m1_subset_1(E_2161,k4_zfmisc_1(A_2158,B_2160,C_2159,D_2162))
      | k1_xboole_0 = D_2162
      | k1_xboole_0 = C_2159
      | k1_xboole_0 = B_2160
      | k1_xboole_0 = A_2158 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_17031,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_50,c_17029])).

tff(c_17034,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_16972,c_17031])).

tff(c_17357,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))) = k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13')
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_17059,c_17287,c_17034])).

tff(c_17358,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_17357])).

tff(c_17366,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17358,c_12])).

tff(c_17368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13011,c_17366])).

tff(c_17370,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_17357])).

tff(c_17058,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8'
    | k2_mcart_1(k1_mcart_1('#skF_13')) = k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13') ),
    inference(splitRight,[status(thm)],[c_16981])).

tff(c_17732,plain,(
    k2_mcart_1(k1_mcart_1('#skF_13')) = k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_17370,c_17287,c_17058])).

tff(c_18551,plain,(
    ! [D_2345,B_2346,A_2344,C_2343,A_2347] :
      ( r2_hidden(k1_mcart_1(A_2344),k3_zfmisc_1(A_2347,B_2346,C_2343))
      | ~ r2_hidden(A_2344,k4_zfmisc_1(A_2347,B_2346,C_2343,D_2345)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13014,c_36])).

tff(c_18613,plain,(
    r2_hidden(k1_mcart_1('#skF_13'),k3_zfmisc_1('#skF_9','#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_48,c_18551])).

tff(c_12945,plain,(
    ! [A_1690,C_1691,B_1692] :
      ( r2_hidden(k2_mcart_1(A_1690),C_1691)
      | ~ r2_hidden(A_1690,k2_zfmisc_1(B_1692,C_1691)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12947,plain,(
    ! [A_1690,C_20,A_18,B_19] :
      ( r2_hidden(k2_mcart_1(A_1690),C_20)
      | ~ r2_hidden(A_1690,k3_zfmisc_1(A_18,B_19,C_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_12945])).

tff(c_18618,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_13')),'#skF_11') ),
    inference(resolution,[status(thm)],[c_18613,c_12947])).

tff(c_18626,plain,(
    r2_hidden(k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_13'),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17732,c_18618])).

tff(c_18628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15692,c_18626])).

tff(c_18629,plain,(
    v1_xboole_0('#skF_11') ),
    inference(splitRight,[status(thm)],[c_13012])).

tff(c_18981,plain,(
    ! [B_2391,C_2392] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_2391,C_2392))),C_2392)
      | v1_xboole_0(k2_zfmisc_1(B_2391,C_2392)) ) ),
    inference(resolution,[status(thm)],[c_4,c_12945])).

tff(c_19023,plain,(
    ! [C_2395,B_2396] :
      ( ~ v1_xboole_0(C_2395)
      | v1_xboole_0(k2_zfmisc_1(B_2396,C_2395)) ) ),
    inference(resolution,[status(thm)],[c_18981,c_2])).

tff(c_19029,plain,(
    ! [C_20,A_18,B_19] :
      ( ~ v1_xboole_0(C_20)
      | v1_xboole_0(k3_zfmisc_1(A_18,B_19,C_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_19023])).

tff(c_19411,plain,(
    ! [B_2451,C_2452] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_2451,C_2452))),B_2451)
      | v1_xboole_0(k2_zfmisc_1(B_2451,C_2452)) ) ),
    inference(resolution,[status(thm)],[c_4,c_12918])).

tff(c_19485,plain,(
    ! [B_2456,C_2457] :
      ( ~ v1_xboole_0(B_2456)
      | v1_xboole_0(k2_zfmisc_1(B_2456,C_2457)) ) ),
    inference(resolution,[status(thm)],[c_19411,c_2])).

tff(c_19706,plain,(
    ! [A_2473,B_2474,C_2475,D_2476] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_2473,B_2474,C_2475))
      | v1_xboole_0(k4_zfmisc_1(A_2473,B_2474,C_2475,D_2476)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_19485])).

tff(c_19710,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_9','#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_19706,c_74])).

tff(c_19716,plain,(
    ~ v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_19029,c_19710])).

tff(c_19721,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18629,c_19716])).

tff(c_19722,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_13008])).

tff(c_21539,plain,(
    ! [B_2694,C_2695] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_2694,C_2695))),C_2695)
      | v1_xboole_0(k2_zfmisc_1(B_2694,C_2695)) ) ),
    inference(resolution,[status(thm)],[c_4,c_12945])).

tff(c_21569,plain,(
    ! [C_2695,B_2694] :
      ( ~ v1_xboole_0(C_2695)
      | v1_xboole_0(k2_zfmisc_1(B_2694,C_2695)) ) ),
    inference(resolution,[status(thm)],[c_21539,c_2])).

tff(c_19827,plain,(
    ! [B_2499,C_2500] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_2499,C_2500))),B_2499)
      | v1_xboole_0(k2_zfmisc_1(B_2499,C_2500)) ) ),
    inference(resolution,[status(thm)],[c_4,c_12918])).

tff(c_19868,plain,(
    ! [B_2503,C_2504] :
      ( ~ v1_xboole_0(B_2503)
      | v1_xboole_0(k2_zfmisc_1(B_2503,C_2504)) ) ),
    inference(resolution,[status(thm)],[c_19827,c_2])).

tff(c_19874,plain,(
    ! [A_18,B_19,C_20] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_18,B_19))
      | v1_xboole_0(k3_zfmisc_1(A_18,B_19,C_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_19868])).

tff(c_21800,plain,(
    ! [A_2731,B_2732,C_2733,D_2734] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_2731,B_2732,C_2733))
      | v1_xboole_0(k4_zfmisc_1(A_2731,B_2732,C_2733,D_2734)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_19868])).

tff(c_21804,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_9','#skF_10','#skF_11')) ),
    inference(resolution,[status(thm)],[c_21800,c_74])).

tff(c_21812,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_19874,c_21804])).

tff(c_21815,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_21569,c_21812])).

tff(c_21822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19722,c_21815])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.89/4.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.89/4.31  
% 10.89/4.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.89/4.31  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_13 > #skF_9 > #skF_8 > #skF_2 > #skF_12 > #skF_4
% 10.89/4.31  
% 10.89/4.31  %Foreground sorts:
% 10.89/4.31  
% 10.89/4.31  
% 10.89/4.31  %Background operators:
% 10.89/4.31  
% 10.89/4.31  
% 10.89/4.31  %Foreground operators:
% 10.89/4.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.89/4.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.89/4.31  tff('#skF_11', type, '#skF_11': $i).
% 10.89/4.31  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 10.89/4.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.89/4.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.89/4.31  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 10.89/4.31  tff('#skF_7', type, '#skF_7': $i).
% 10.89/4.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.89/4.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.89/4.31  tff('#skF_10', type, '#skF_10': $i).
% 10.89/4.31  tff('#skF_5', type, '#skF_5': $i).
% 10.89/4.31  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 10.89/4.31  tff('#skF_6', type, '#skF_6': $i).
% 10.89/4.31  tff('#skF_13', type, '#skF_13': $i).
% 10.89/4.31  tff('#skF_9', type, '#skF_9': $i).
% 10.89/4.31  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 10.89/4.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.89/4.31  tff('#skF_8', type, '#skF_8': $i).
% 10.89/4.31  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 10.89/4.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.89/4.31  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 10.89/4.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.89/4.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.89/4.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.89/4.31  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 10.89/4.31  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 10.89/4.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.89/4.31  tff('#skF_12', type, '#skF_12': $i).
% 10.89/4.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.89/4.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.89/4.31  
% 11.21/4.35  tff(f_115, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(A)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(B)) => (![G]: (m1_subset_1(G, k1_zfmisc_1(C)) => (![H]: (m1_subset_1(H, k1_zfmisc_1(D)) => (![I]: (m1_subset_1(I, k4_zfmisc_1(A, B, C, D)) => (r2_hidden(I, k4_zfmisc_1(E, F, G, H)) => (((r2_hidden(k8_mcart_1(A, B, C, D, I), E) & r2_hidden(k9_mcart_1(A, B, C, D, I), F)) & r2_hidden(k10_mcart_1(A, B, C, D, I), G)) & r2_hidden(k11_mcart_1(A, B, C, D, I), H))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_mcart_1)).
% 11.21/4.35  tff(f_49, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.21/4.35  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 11.21/4.35  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.21/4.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 11.21/4.35  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.21/4.35  tff(f_59, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 11.21/4.35  tff(f_65, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 11.21/4.35  tff(f_90, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 11.21/4.35  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 11.21/4.35  tff(f_57, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 11.21/4.35  tff(c_54, plain, (m1_subset_1('#skF_11', k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.21/4.35  tff(c_26, plain, (![A_15]: (~v1_xboole_0(k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.21/4.35  tff(c_94, plain, (![A_71, B_72]: (r2_hidden(A_71, B_72) | v1_xboole_0(B_72) | ~m1_subset_1(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.21/4.35  tff(c_14, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 11.21/4.35  tff(c_102, plain, (![A_71, A_10]: (r1_tarski(A_71, A_10) | v1_xboole_0(k1_zfmisc_1(A_10)) | ~m1_subset_1(A_71, k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_94, c_14])).
% 11.21/4.35  tff(c_111, plain, (![A_73, A_74]: (r1_tarski(A_73, A_74) | ~m1_subset_1(A_73, k1_zfmisc_1(A_74)))), inference(negUnitSimplification, [status(thm)], [c_26, c_102])).
% 11.21/4.35  tff(c_124, plain, (r1_tarski('#skF_11', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_111])).
% 11.21/4.35  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.21/4.35  tff(c_9182, plain, (![C_1193, B_1194, A_1195]: (r2_hidden(C_1193, B_1194) | ~r2_hidden(C_1193, A_1195) | ~r1_tarski(A_1195, B_1194))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.21/4.35  tff(c_9201, plain, (![A_1196, B_1197]: (r2_hidden('#skF_1'(A_1196), B_1197) | ~r1_tarski(A_1196, B_1197) | v1_xboole_0(A_1196))), inference(resolution, [status(thm)], [c_4, c_9182])).
% 11.21/4.35  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.21/4.35  tff(c_9222, plain, (![B_1198, A_1199]: (~v1_xboole_0(B_1198) | ~r1_tarski(A_1199, B_1198) | v1_xboole_0(A_1199))), inference(resolution, [status(thm)], [c_9201, c_2])).
% 11.21/4.35  tff(c_9251, plain, (~v1_xboole_0('#skF_7') | v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_124, c_9222])).
% 11.21/4.35  tff(c_9266, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_9251])).
% 11.21/4.35  tff(c_52, plain, (m1_subset_1('#skF_12', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.21/4.35  tff(c_125, plain, (r1_tarski('#skF_12', '#skF_8')), inference(resolution, [status(thm)], [c_52, c_111])).
% 11.21/4.35  tff(c_9250, plain, (~v1_xboole_0('#skF_8') | v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_125, c_9222])).
% 11.21/4.35  tff(c_9267, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_9250])).
% 11.21/4.35  tff(c_56, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.21/4.35  tff(c_126, plain, (r1_tarski('#skF_10', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_111])).
% 11.21/4.35  tff(c_9249, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_126, c_9222])).
% 11.21/4.35  tff(c_9265, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_9249])).
% 11.21/4.35  tff(c_48, plain, (r2_hidden('#skF_13', k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.21/4.35  tff(c_9268, plain, (![A_1201, B_1202, C_1203, D_1204]: (k2_zfmisc_1(k3_zfmisc_1(A_1201, B_1202, C_1203), D_1204)=k4_zfmisc_1(A_1201, B_1202, C_1203, D_1204))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.21/4.35  tff(c_34, plain, (![A_25, C_27, B_26]: (r2_hidden(k2_mcart_1(A_25), C_27) | ~r2_hidden(A_25, k2_zfmisc_1(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.21/4.35  tff(c_9891, plain, (![A_1295, B_1298, A_1296, C_1299, D_1297]: (r2_hidden(k2_mcart_1(A_1295), D_1297) | ~r2_hidden(A_1295, k4_zfmisc_1(A_1296, B_1298, C_1299, D_1297)))), inference(superposition, [status(thm), theory('equality')], [c_9268, c_34])).
% 11.21/4.35  tff(c_9929, plain, (r2_hidden(k2_mcart_1('#skF_13'), '#skF_12')), inference(resolution, [status(thm)], [c_48, c_9891])).
% 11.21/4.35  tff(c_46, plain, (~r2_hidden(k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_12') | ~r2_hidden(k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_11') | ~r2_hidden(k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_10') | ~r2_hidden(k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.21/4.35  tff(c_128, plain, (~r2_hidden(k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_9')), inference(splitLeft, [status(thm)], [c_46])).
% 11.21/4.35  tff(c_180, plain, (![C_86, B_87, A_88]: (r2_hidden(C_86, B_87) | ~r2_hidden(C_86, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.21/4.35  tff(c_223, plain, (![A_93, B_94]: (r2_hidden('#skF_1'(A_93), B_94) | ~r1_tarski(A_93, B_94) | v1_xboole_0(A_93))), inference(resolution, [status(thm)], [c_4, c_180])).
% 11.21/4.35  tff(c_244, plain, (![B_95, A_96]: (~v1_xboole_0(B_95) | ~r1_tarski(A_96, B_95) | v1_xboole_0(A_96))), inference(resolution, [status(thm)], [c_223, c_2])).
% 11.21/4.35  tff(c_270, plain, (~v1_xboole_0('#skF_8') | v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_125, c_244])).
% 11.21/4.35  tff(c_292, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_270])).
% 11.21/4.35  tff(c_269, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_126, c_244])).
% 11.21/4.35  tff(c_290, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_269])).
% 11.21/4.35  tff(c_58, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.21/4.35  tff(c_127, plain, (r1_tarski('#skF_9', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_111])).
% 11.21/4.35  tff(c_268, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_127, c_244])).
% 11.21/4.35  tff(c_273, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_268])).
% 11.21/4.35  tff(c_50, plain, (m1_subset_1('#skF_13', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 11.21/4.35  tff(c_670, plain, (![B_166, C_165, D_168, E_167, A_164]: (k11_mcart_1(A_164, B_166, C_165, D_168, E_167)=k2_mcart_1(E_167) | ~m1_subset_1(E_167, k4_zfmisc_1(A_164, B_166, C_165, D_168)) | k1_xboole_0=D_168 | k1_xboole_0=C_165 | k1_xboole_0=B_166 | k1_xboole_0=A_164)), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.35  tff(c_674, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13')=k2_mcart_1('#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_670])).
% 11.21/4.35  tff(c_738, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_674])).
% 11.21/4.35  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.21/4.35  tff(c_740, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_738, c_12])).
% 11.21/4.35  tff(c_742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_273, c_740])).
% 11.21/4.35  tff(c_744, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_674])).
% 11.21/4.35  tff(c_757, plain, (![C_176, B_177, D_179, E_178, A_175]: (k2_mcart_1(k1_mcart_1(E_178))=k10_mcart_1(A_175, B_177, C_176, D_179, E_178) | ~m1_subset_1(E_178, k4_zfmisc_1(A_175, B_177, C_176, D_179)) | k1_xboole_0=D_179 | k1_xboole_0=C_176 | k1_xboole_0=B_177 | k1_xboole_0=A_175)), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.35  tff(c_760, plain, (k2_mcart_1(k1_mcart_1('#skF_13'))=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_757])).
% 11.21/4.35  tff(c_763, plain, (k2_mcart_1(k1_mcart_1('#skF_13'))=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_744, c_760])).
% 11.21/4.35  tff(c_847, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_763])).
% 11.21/4.35  tff(c_852, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_847, c_12])).
% 11.21/4.35  tff(c_854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_290, c_852])).
% 11.21/4.35  tff(c_856, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_763])).
% 11.21/4.35  tff(c_271, plain, (~v1_xboole_0('#skF_7') | v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_124, c_244])).
% 11.21/4.35  tff(c_291, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_271])).
% 11.21/4.35  tff(c_913, plain, (![E_197, C_195, A_194, B_196, D_198]: (k8_mcart_1(A_194, B_196, C_195, D_198, E_197)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_197))) | ~m1_subset_1(E_197, k4_zfmisc_1(A_194, B_196, C_195, D_198)) | k1_xboole_0=D_198 | k1_xboole_0=C_195 | k1_xboole_0=B_196 | k1_xboole_0=A_194)), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.35  tff(c_915, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_913])).
% 11.21/4.35  tff(c_918, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_744, c_856, c_915])).
% 11.21/4.35  tff(c_2737, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_918])).
% 11.21/4.35  tff(c_2744, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2737, c_12])).
% 11.21/4.35  tff(c_2746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_291, c_2744])).
% 11.21/4.35  tff(c_2748, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_918])).
% 11.21/4.35  tff(c_830, plain, (![B_185, D_187, C_184, E_186, A_183]: (k9_mcart_1(A_183, B_185, C_184, D_187, E_186)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_186))) | ~m1_subset_1(E_186, k4_zfmisc_1(A_183, B_185, C_184, D_187)) | k1_xboole_0=D_187 | k1_xboole_0=C_184 | k1_xboole_0=B_185 | k1_xboole_0=A_183)), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.35  tff(c_832, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_830])).
% 11.21/4.35  tff(c_835, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_744, c_832])).
% 11.21/4.35  tff(c_2776, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_856, c_2748, c_835])).
% 11.21/4.35  tff(c_2777, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_2776])).
% 11.21/4.35  tff(c_2785, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2777, c_12])).
% 11.21/4.35  tff(c_2787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_292, c_2785])).
% 11.21/4.35  tff(c_2789, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_2776])).
% 11.21/4.35  tff(c_2747, plain, (k1_xboole_0='#skF_8' | k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13')), inference(splitRight, [status(thm)], [c_918])).
% 11.21/4.35  tff(c_3135, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_2789, c_2747])).
% 11.21/4.35  tff(c_274, plain, (![A_97, B_98, C_99, D_100]: (k2_zfmisc_1(k3_zfmisc_1(A_97, B_98, C_99), D_100)=k4_zfmisc_1(A_97, B_98, C_99, D_100))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.21/4.35  tff(c_36, plain, (![A_25, B_26, C_27]: (r2_hidden(k1_mcart_1(A_25), B_26) | ~r2_hidden(A_25, k2_zfmisc_1(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.21/4.35  tff(c_3718, plain, (![A_470, B_473, A_471, C_472, D_474]: (r2_hidden(k1_mcart_1(A_470), k3_zfmisc_1(A_471, B_473, C_472)) | ~r2_hidden(A_470, k4_zfmisc_1(A_471, B_473, C_472, D_474)))), inference(superposition, [status(thm), theory('equality')], [c_274, c_36])).
% 11.21/4.35  tff(c_3772, plain, (r2_hidden(k1_mcart_1('#skF_13'), k3_zfmisc_1('#skF_9', '#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_48, c_3718])).
% 11.21/4.35  tff(c_163, plain, (![A_83, B_84, C_85]: (k2_zfmisc_1(k2_zfmisc_1(A_83, B_84), C_85)=k3_zfmisc_1(A_83, B_84, C_85))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.21/4.35  tff(c_171, plain, (![A_25, A_83, B_84, C_85]: (r2_hidden(k1_mcart_1(A_25), k2_zfmisc_1(A_83, B_84)) | ~r2_hidden(A_25, k3_zfmisc_1(A_83, B_84, C_85)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_36])).
% 11.21/4.35  tff(c_3783, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_13')), k2_zfmisc_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_3772, c_171])).
% 11.21/4.35  tff(c_3793, plain, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))), '#skF_9')), inference(resolution, [status(thm)], [c_3783, c_36])).
% 11.21/4.35  tff(c_3801, plain, (r2_hidden(k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3135, c_3793])).
% 11.21/4.35  tff(c_3803, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_3801])).
% 11.21/4.35  tff(c_3804, plain, (v1_xboole_0('#skF_12')), inference(splitRight, [status(thm)], [c_270])).
% 11.21/4.35  tff(c_3918, plain, (![B_505, A_502, C_504, A_503, D_506]: (r2_hidden(k2_mcart_1(A_502), D_506) | ~r2_hidden(A_502, k4_zfmisc_1(A_503, B_505, C_504, D_506)))), inference(superposition, [status(thm), theory('equality')], [c_274, c_34])).
% 11.21/4.35  tff(c_3936, plain, (r2_hidden(k2_mcart_1('#skF_13'), '#skF_12')), inference(resolution, [status(thm)], [c_48, c_3918])).
% 11.21/4.35  tff(c_3942, plain, (~v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_3936, c_2])).
% 11.21/4.35  tff(c_3947, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3804, c_3942])).
% 11.21/4.35  tff(c_3948, plain, (v1_xboole_0('#skF_11')), inference(splitRight, [status(thm)], [c_271])).
% 11.21/4.35  tff(c_30, plain, (![A_18, B_19, C_20]: (k2_zfmisc_1(k2_zfmisc_1(A_18, B_19), C_20)=k3_zfmisc_1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.21/4.35  tff(c_208, plain, (![A_90, C_91, B_92]: (r2_hidden(k2_mcart_1(A_90), C_91) | ~r2_hidden(A_90, k2_zfmisc_1(B_92, C_91)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.21/4.35  tff(c_4663, plain, (![B_600, C_601]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_600, C_601))), C_601) | v1_xboole_0(k2_zfmisc_1(B_600, C_601)))), inference(resolution, [status(thm)], [c_4, c_208])).
% 11.21/4.35  tff(c_4700, plain, (![C_602, B_603]: (~v1_xboole_0(C_602) | v1_xboole_0(k2_zfmisc_1(B_603, C_602)))), inference(resolution, [status(thm)], [c_4663, c_2])).
% 11.21/4.35  tff(c_4706, plain, (![C_20, A_18, B_19]: (~v1_xboole_0(C_20) | v1_xboole_0(k3_zfmisc_1(A_18, B_19, C_20)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_4700])).
% 11.21/4.35  tff(c_32, plain, (![A_21, B_22, C_23, D_24]: (k2_zfmisc_1(k3_zfmisc_1(A_21, B_22, C_23), D_24)=k4_zfmisc_1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.21/4.35  tff(c_150, plain, (![A_80, B_81, C_82]: (r2_hidden(k1_mcart_1(A_80), B_81) | ~r2_hidden(A_80, k2_zfmisc_1(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.21/4.35  tff(c_4600, plain, (![B_595, C_596]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_595, C_596))), B_595) | v1_xboole_0(k2_zfmisc_1(B_595, C_596)))), inference(resolution, [status(thm)], [c_4, c_150])).
% 11.21/4.35  tff(c_4640, plain, (![B_597, C_598]: (~v1_xboole_0(B_597) | v1_xboole_0(k2_zfmisc_1(B_597, C_598)))), inference(resolution, [status(thm)], [c_4600, c_2])).
% 11.21/4.35  tff(c_4878, plain, (![A_626, B_627, C_628, D_629]: (~v1_xboole_0(k3_zfmisc_1(A_626, B_627, C_628)) | v1_xboole_0(k4_zfmisc_1(A_626, B_627, C_628, D_629)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_4640])).
% 11.21/4.35  tff(c_74, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_9', '#skF_10', '#skF_11', '#skF_12'))), inference(resolution, [status(thm)], [c_48, c_2])).
% 11.21/4.35  tff(c_4882, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_9', '#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_4878, c_74])).
% 11.21/4.35  tff(c_4888, plain, (~v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_4706, c_4882])).
% 11.21/4.35  tff(c_4893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3948, c_4888])).
% 11.21/4.35  tff(c_4894, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_269])).
% 11.21/4.35  tff(c_5101, plain, (![B_670, C_671]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_670, C_671))), C_671) | v1_xboole_0(k2_zfmisc_1(B_670, C_671)))), inference(resolution, [status(thm)], [c_4, c_208])).
% 11.21/4.35  tff(c_5131, plain, (![C_671, B_670]: (~v1_xboole_0(C_671) | v1_xboole_0(k2_zfmisc_1(B_670, C_671)))), inference(resolution, [status(thm)], [c_5101, c_2])).
% 11.21/4.35  tff(c_5057, plain, (![B_663, C_664]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_663, C_664))), B_663) | v1_xboole_0(k2_zfmisc_1(B_663, C_664)))), inference(resolution, [status(thm)], [c_4, c_150])).
% 11.21/4.35  tff(c_5093, plain, (![B_665, C_666]: (~v1_xboole_0(B_665) | v1_xboole_0(k2_zfmisc_1(B_665, C_666)))), inference(resolution, [status(thm)], [c_5057, c_2])).
% 11.21/4.35  tff(c_5099, plain, (![A_18, B_19, C_20]: (~v1_xboole_0(k2_zfmisc_1(A_18, B_19)) | v1_xboole_0(k3_zfmisc_1(A_18, B_19, C_20)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_5093])).
% 11.21/4.35  tff(c_7048, plain, (![A_895, B_896, C_897, D_898]: (~v1_xboole_0(k3_zfmisc_1(A_895, B_896, C_897)) | v1_xboole_0(k4_zfmisc_1(A_895, B_896, C_897, D_898)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_5093])).
% 11.21/4.35  tff(c_7052, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_9', '#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_7048, c_74])).
% 11.21/4.35  tff(c_7060, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_5099, c_7052])).
% 11.21/4.35  tff(c_7115, plain, (~v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_5131, c_7060])).
% 11.21/4.35  tff(c_7122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4894, c_7115])).
% 11.21/4.35  tff(c_7123, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_268])).
% 11.21/4.35  tff(c_8630, plain, (![B_1108, C_1109]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1108, C_1109))), B_1108) | v1_xboole_0(k2_zfmisc_1(B_1108, C_1109)))), inference(resolution, [status(thm)], [c_4, c_150])).
% 11.21/4.35  tff(c_8663, plain, (![B_1108, C_1109]: (~v1_xboole_0(B_1108) | v1_xboole_0(k2_zfmisc_1(B_1108, C_1109)))), inference(resolution, [status(thm)], [c_8630, c_2])).
% 11.21/4.35  tff(c_8666, plain, (![B_1110, C_1111]: (~v1_xboole_0(B_1110) | v1_xboole_0(k2_zfmisc_1(B_1110, C_1111)))), inference(resolution, [status(thm)], [c_8630, c_2])).
% 11.21/4.35  tff(c_8672, plain, (![A_18, B_19, C_20]: (~v1_xboole_0(k2_zfmisc_1(A_18, B_19)) | v1_xboole_0(k3_zfmisc_1(A_18, B_19, C_20)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_8666])).
% 11.21/4.35  tff(c_9086, plain, (![A_1175, B_1176, C_1177, D_1178]: (~v1_xboole_0(k3_zfmisc_1(A_1175, B_1176, C_1177)) | v1_xboole_0(k4_zfmisc_1(A_1175, B_1176, C_1177, D_1178)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_8666])).
% 11.21/4.35  tff(c_9090, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_9', '#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_9086, c_74])).
% 11.21/4.35  tff(c_9097, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_8672, c_9090])).
% 11.21/4.35  tff(c_9101, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_8663, c_9097])).
% 11.21/4.35  tff(c_9108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7123, c_9101])).
% 11.21/4.35  tff(c_9110, plain, (r2_hidden(k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_9')), inference(splitRight, [status(thm)], [c_46])).
% 11.21/4.35  tff(c_9131, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_9110, c_2])).
% 11.21/4.35  tff(c_9231, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_127, c_9222])).
% 11.21/4.35  tff(c_9248, plain, (~v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_9131, c_9231])).
% 11.21/4.35  tff(c_9866, plain, (![E_1284, C_1282, D_1285, A_1281, B_1283]: (k11_mcart_1(A_1281, B_1283, C_1282, D_1285, E_1284)=k2_mcart_1(E_1284) | ~m1_subset_1(E_1284, k4_zfmisc_1(A_1281, B_1283, C_1282, D_1285)) | k1_xboole_0=D_1285 | k1_xboole_0=C_1282 | k1_xboole_0=B_1283 | k1_xboole_0=A_1281)), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.35  tff(c_9870, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13')=k2_mcart_1('#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_9866])).
% 11.21/4.35  tff(c_9884, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_9870])).
% 11.21/4.35  tff(c_9886, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9884, c_12])).
% 11.21/4.35  tff(c_9888, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9248, c_9886])).
% 11.21/4.35  tff(c_9889, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8' | k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13')=k2_mcart_1('#skF_13')), inference(splitRight, [status(thm)], [c_9870])).
% 11.21/4.35  tff(c_10001, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13')=k2_mcart_1('#skF_13')), inference(splitLeft, [status(thm)], [c_9889])).
% 11.21/4.35  tff(c_9109, plain, (~r2_hidden(k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_10') | ~r2_hidden(k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_11') | ~r2_hidden(k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_12')), inference(splitRight, [status(thm)], [c_46])).
% 11.21/4.35  tff(c_9132, plain, (~r2_hidden(k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_12')), inference(splitLeft, [status(thm)], [c_9109])).
% 11.21/4.35  tff(c_10007, plain, (~r2_hidden(k2_mcart_1('#skF_13'), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_10001, c_9132])).
% 11.21/4.35  tff(c_10010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9929, c_10007])).
% 11.21/4.35  tff(c_10011, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_9889])).
% 11.21/4.35  tff(c_10013, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_10011])).
% 11.21/4.35  tff(c_10017, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10013, c_12])).
% 11.21/4.35  tff(c_10019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9265, c_10017])).
% 11.21/4.35  tff(c_10020, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_10011])).
% 11.21/4.35  tff(c_10028, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_10020])).
% 11.21/4.35  tff(c_10034, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_10028, c_12])).
% 11.21/4.35  tff(c_10036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9267, c_10034])).
% 11.21/4.35  tff(c_10038, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_10020])).
% 11.21/4.35  tff(c_9890, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_9870])).
% 11.21/4.35  tff(c_10021, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_10011])).
% 11.21/4.35  tff(c_10022, plain, (![D_1313, B_1311, E_1312, A_1309, C_1310]: (k8_mcart_1(A_1309, B_1311, C_1310, D_1313, E_1312)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_1312))) | ~m1_subset_1(E_1312, k4_zfmisc_1(A_1309, B_1311, C_1310, D_1313)) | k1_xboole_0=D_1313 | k1_xboole_0=C_1310 | k1_xboole_0=B_1311 | k1_xboole_0=A_1309)), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.35  tff(c_10024, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_10022])).
% 11.21/4.35  tff(c_10027, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_9890, c_10021, c_10024])).
% 11.21/4.35  tff(c_10039, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_10038, c_10027])).
% 11.21/4.35  tff(c_10040, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_10039])).
% 11.21/4.35  tff(c_10047, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_10040, c_12])).
% 11.21/4.35  tff(c_10049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9266, c_10047])).
% 11.21/4.35  tff(c_10051, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_10039])).
% 11.21/4.35  tff(c_10037, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_10020])).
% 11.21/4.35  tff(c_10052, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10051, c_10037])).
% 11.21/4.35  tff(c_10053, plain, (v1_xboole_0('#skF_12')), inference(splitRight, [status(thm)], [c_9250])).
% 11.21/4.35  tff(c_9167, plain, (![A_1190, C_1191, B_1192]: (r2_hidden(k2_mcart_1(A_1190), C_1191) | ~r2_hidden(A_1190, k2_zfmisc_1(B_1192, C_1191)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.21/4.35  tff(c_10172, plain, (![B_1340, C_1341]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1340, C_1341))), C_1341) | v1_xboole_0(k2_zfmisc_1(B_1340, C_1341)))), inference(resolution, [status(thm)], [c_4, c_9167])).
% 11.21/4.35  tff(c_10210, plain, (![C_1343, B_1344]: (~v1_xboole_0(C_1343) | v1_xboole_0(k2_zfmisc_1(B_1344, C_1343)))), inference(resolution, [status(thm)], [c_10172, c_2])).
% 11.21/4.35  tff(c_10218, plain, (![D_1348, A_1349, B_1350, C_1351]: (~v1_xboole_0(D_1348) | v1_xboole_0(k4_zfmisc_1(A_1349, B_1350, C_1351, D_1348)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_10210])).
% 11.21/4.35  tff(c_10221, plain, (~v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_10218, c_74])).
% 11.21/4.35  tff(c_10225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10053, c_10221])).
% 11.21/4.35  tff(c_10226, plain, (v1_xboole_0('#skF_11')), inference(splitRight, [status(thm)], [c_9251])).
% 11.21/4.35  tff(c_11054, plain, (![B_1458, C_1459]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1458, C_1459))), C_1459) | v1_xboole_0(k2_zfmisc_1(B_1458, C_1459)))), inference(resolution, [status(thm)], [c_4, c_9167])).
% 11.21/4.35  tff(c_11091, plain, (![C_1460, B_1461]: (~v1_xboole_0(C_1460) | v1_xboole_0(k2_zfmisc_1(B_1461, C_1460)))), inference(resolution, [status(thm)], [c_11054, c_2])).
% 11.21/4.35  tff(c_11097, plain, (![C_20, A_18, B_19]: (~v1_xboole_0(C_20) | v1_xboole_0(k3_zfmisc_1(A_18, B_19, C_20)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_11091])).
% 11.21/4.35  tff(c_9152, plain, (![A_1187, B_1188, C_1189]: (r2_hidden(k1_mcart_1(A_1187), B_1188) | ~r2_hidden(A_1187, k2_zfmisc_1(B_1188, C_1189)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.21/4.35  tff(c_10465, plain, (![B_1391, C_1392]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1391, C_1392))), B_1391) | v1_xboole_0(k2_zfmisc_1(B_1391, C_1392)))), inference(resolution, [status(thm)], [c_4, c_9152])).
% 11.21/4.35  tff(c_10501, plain, (![B_1393, C_1394]: (~v1_xboole_0(B_1393) | v1_xboole_0(k2_zfmisc_1(B_1393, C_1394)))), inference(resolution, [status(thm)], [c_10465, c_2])).
% 11.21/4.35  tff(c_11499, plain, (![A_1510, B_1511, C_1512, D_1513]: (~v1_xboole_0(k3_zfmisc_1(A_1510, B_1511, C_1512)) | v1_xboole_0(k4_zfmisc_1(A_1510, B_1511, C_1512, D_1513)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_10501])).
% 11.21/4.35  tff(c_11503, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_9', '#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_11499, c_74])).
% 11.21/4.35  tff(c_11506, plain, (~v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_11097, c_11503])).
% 11.21/4.35  tff(c_11513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10226, c_11506])).
% 11.21/4.35  tff(c_11514, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_9249])).
% 11.21/4.35  tff(c_11640, plain, (![B_1541, C_1542]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1541, C_1542))), C_1542) | v1_xboole_0(k2_zfmisc_1(B_1541, C_1542)))), inference(resolution, [status(thm)], [c_4, c_9167])).
% 11.21/4.35  tff(c_11670, plain, (![C_1542, B_1541]: (~v1_xboole_0(C_1542) | v1_xboole_0(k2_zfmisc_1(B_1541, C_1542)))), inference(resolution, [status(thm)], [c_11640, c_2])).
% 11.21/4.35  tff(c_11697, plain, (![B_1554, C_1555]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1554, C_1555))), B_1554) | v1_xboole_0(k2_zfmisc_1(B_1554, C_1555)))), inference(resolution, [status(thm)], [c_4, c_9152])).
% 11.21/4.35  tff(c_11733, plain, (![B_1556, C_1557]: (~v1_xboole_0(B_1556) | v1_xboole_0(k2_zfmisc_1(B_1556, C_1557)))), inference(resolution, [status(thm)], [c_11697, c_2])).
% 11.21/4.35  tff(c_11739, plain, (![A_18, B_19, C_20]: (~v1_xboole_0(k2_zfmisc_1(A_18, B_19)) | v1_xboole_0(k3_zfmisc_1(A_18, B_19, C_20)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_11733])).
% 11.21/4.35  tff(c_12851, plain, (![A_1676, B_1677, C_1678, D_1679]: (~v1_xboole_0(k3_zfmisc_1(A_1676, B_1677, C_1678)) | v1_xboole_0(k4_zfmisc_1(A_1676, B_1677, C_1678, D_1679)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_11733])).
% 11.21/4.35  tff(c_12855, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_9', '#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_12851, c_74])).
% 11.21/4.35  tff(c_12862, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_11739, c_12855])).
% 11.21/4.35  tff(c_12869, plain, (~v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_11670, c_12862])).
% 11.21/4.35  tff(c_12874, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11514, c_12869])).
% 11.21/4.35  tff(c_12875, plain, (~r2_hidden(k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_11') | ~r2_hidden(k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_10')), inference(splitRight, [status(thm)], [c_9109])).
% 11.21/4.35  tff(c_13128, plain, (~r2_hidden(k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_10')), inference(splitLeft, [status(thm)], [c_12875])).
% 11.21/4.35  tff(c_12876, plain, (r2_hidden(k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_12')), inference(splitRight, [status(thm)], [c_9109])).
% 11.21/4.35  tff(c_12880, plain, (~v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_12876, c_2])).
% 11.21/4.35  tff(c_12896, plain, (![C_1683, B_1684, A_1685]: (r2_hidden(C_1683, B_1684) | ~r2_hidden(C_1683, A_1685) | ~r1_tarski(A_1685, B_1684))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.21/4.35  tff(c_12960, plain, (![A_1693, B_1694]: (r2_hidden('#skF_1'(A_1693), B_1694) | ~r1_tarski(A_1693, B_1694) | v1_xboole_0(A_1693))), inference(resolution, [status(thm)], [c_4, c_12896])).
% 11.21/4.35  tff(c_12981, plain, (![B_1695, A_1696]: (~v1_xboole_0(B_1695) | ~r1_tarski(A_1696, B_1695) | v1_xboole_0(A_1696))), inference(resolution, [status(thm)], [c_12960, c_2])).
% 11.21/4.35  tff(c_12996, plain, (~v1_xboole_0('#skF_8') | v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_125, c_12981])).
% 11.21/4.35  tff(c_13011, plain, (~v1_xboole_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_12880, c_12996])).
% 11.21/4.35  tff(c_13008, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_126, c_12981])).
% 11.21/4.35  tff(c_13030, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_13008])).
% 11.21/4.35  tff(c_12990, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_127, c_12981])).
% 11.21/4.35  tff(c_13007, plain, (~v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_9131, c_12990])).
% 11.21/4.35  tff(c_13481, plain, (![E_1760, C_1758, D_1761, B_1759, A_1757]: (k11_mcart_1(A_1757, B_1759, C_1758, D_1761, E_1760)=k2_mcart_1(E_1760) | ~m1_subset_1(E_1760, k4_zfmisc_1(A_1757, B_1759, C_1758, D_1761)) | k1_xboole_0=D_1761 | k1_xboole_0=C_1758 | k1_xboole_0=B_1759 | k1_xboole_0=A_1757)), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.35  tff(c_13485, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13')=k2_mcart_1('#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_13481])).
% 11.21/4.35  tff(c_13492, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_13485])).
% 11.21/4.35  tff(c_13494, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13492, c_12])).
% 11.21/4.35  tff(c_13496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13007, c_13494])).
% 11.21/4.35  tff(c_13498, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_13485])).
% 11.21/4.35  tff(c_13508, plain, (![B_1764, C_1763, D_1766, E_1765, A_1762]: (k2_mcart_1(k1_mcart_1(E_1765))=k10_mcart_1(A_1762, B_1764, C_1763, D_1766, E_1765) | ~m1_subset_1(E_1765, k4_zfmisc_1(A_1762, B_1764, C_1763, D_1766)) | k1_xboole_0=D_1766 | k1_xboole_0=C_1763 | k1_xboole_0=B_1764 | k1_xboole_0=A_1762)), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.35  tff(c_13511, plain, (k2_mcart_1(k1_mcart_1('#skF_13'))=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_13508])).
% 11.21/4.35  tff(c_13514, plain, (k2_mcart_1(k1_mcart_1('#skF_13'))=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_13498, c_13511])).
% 11.21/4.35  tff(c_13715, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_13514])).
% 11.21/4.35  tff(c_13720, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13715, c_12])).
% 11.21/4.35  tff(c_13722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13030, c_13720])).
% 11.21/4.35  tff(c_13724, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_13514])).
% 11.21/4.35  tff(c_13012, plain, (~v1_xboole_0('#skF_7') | v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_124, c_12981])).
% 11.21/4.35  tff(c_13031, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_13012])).
% 11.21/4.35  tff(c_13783, plain, (![D_1806, C_1803, B_1804, A_1802, E_1805]: (k8_mcart_1(A_1802, B_1804, C_1803, D_1806, E_1805)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_1805))) | ~m1_subset_1(E_1805, k4_zfmisc_1(A_1802, B_1804, C_1803, D_1806)) | k1_xboole_0=D_1806 | k1_xboole_0=C_1803 | k1_xboole_0=B_1804 | k1_xboole_0=A_1802)), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.35  tff(c_13785, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_13783])).
% 11.21/4.35  tff(c_13788, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_13498, c_13724, c_13785])).
% 11.21/4.35  tff(c_14607, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_13788])).
% 11.21/4.35  tff(c_14614, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14607, c_12])).
% 11.21/4.35  tff(c_14616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13031, c_14614])).
% 11.21/4.35  tff(c_14618, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_13788])).
% 11.21/4.35  tff(c_13663, plain, (![B_1782, C_1781, D_1784, E_1783, A_1780]: (k9_mcart_1(A_1780, B_1782, C_1781, D_1784, E_1783)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_1783))) | ~m1_subset_1(E_1783, k4_zfmisc_1(A_1780, B_1782, C_1781, D_1784)) | k1_xboole_0=D_1784 | k1_xboole_0=C_1781 | k1_xboole_0=B_1782 | k1_xboole_0=A_1780)), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.35  tff(c_13665, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_13663])).
% 11.21/4.35  tff(c_13668, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_13498, c_13665])).
% 11.21/4.35  tff(c_14824, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_13724, c_14618, c_13668])).
% 11.21/4.35  tff(c_14825, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_14824])).
% 11.21/4.35  tff(c_14833, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_14825, c_12])).
% 11.21/4.35  tff(c_14835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13011, c_14833])).
% 11.21/4.35  tff(c_14836, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13')), inference(splitRight, [status(thm)], [c_14824])).
% 11.21/4.35  tff(c_13014, plain, (![A_1697, B_1698, C_1699, D_1700]: (k2_zfmisc_1(k3_zfmisc_1(A_1697, B_1698, C_1699), D_1700)=k4_zfmisc_1(A_1697, B_1698, C_1699, D_1700))), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.21/4.35  tff(c_15605, plain, (![D_2002, A_2004, B_2003, C_2000, A_2001]: (r2_hidden(k1_mcart_1(A_2001), k3_zfmisc_1(A_2004, B_2003, C_2000)) | ~r2_hidden(A_2001, k4_zfmisc_1(A_2004, B_2003, C_2000, D_2002)))), inference(superposition, [status(thm), theory('equality')], [c_13014, c_36])).
% 11.21/4.35  tff(c_15663, plain, (r2_hidden(k1_mcart_1('#skF_13'), k3_zfmisc_1('#skF_9', '#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_48, c_15605])).
% 11.21/4.35  tff(c_12918, plain, (![A_1686, B_1687, C_1688]: (r2_hidden(k1_mcart_1(A_1686), B_1687) | ~r2_hidden(A_1686, k2_zfmisc_1(B_1687, C_1688)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.21/4.35  tff(c_12920, plain, (![A_1686, A_18, B_19, C_20]: (r2_hidden(k1_mcart_1(A_1686), k2_zfmisc_1(A_18, B_19)) | ~r2_hidden(A_1686, k3_zfmisc_1(A_18, B_19, C_20)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_12918])).
% 11.21/4.35  tff(c_15674, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_13')), k2_zfmisc_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_15663, c_12920])).
% 11.21/4.35  tff(c_15680, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13'))), '#skF_10')), inference(resolution, [status(thm)], [c_15674, c_34])).
% 11.21/4.35  tff(c_15689, plain, (r2_hidden(k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_14836, c_15680])).
% 11.21/4.35  tff(c_15691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13128, c_15689])).
% 11.21/4.35  tff(c_15692, plain, (~r2_hidden(k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_11')), inference(splitRight, [status(thm)], [c_12875])).
% 11.21/4.35  tff(c_16916, plain, (![D_2146, C_2143, B_2144, E_2145, A_2142]: (k11_mcart_1(A_2142, B_2144, C_2143, D_2146, E_2145)=k2_mcart_1(E_2145) | ~m1_subset_1(E_2145, k4_zfmisc_1(A_2142, B_2144, C_2143, D_2146)) | k1_xboole_0=D_2146 | k1_xboole_0=C_2143 | k1_xboole_0=B_2144 | k1_xboole_0=A_2142)), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.35  tff(c_16920, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13')=k2_mcart_1('#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_16916])).
% 11.21/4.35  tff(c_16966, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_16920])).
% 11.21/4.35  tff(c_16968, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16966, c_12])).
% 11.21/4.35  tff(c_16970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13007, c_16968])).
% 11.21/4.35  tff(c_16972, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_16920])).
% 11.21/4.35  tff(c_16975, plain, (![C_2152, E_2154, B_2153, D_2155, A_2151]: (k2_mcart_1(k1_mcart_1(E_2154))=k10_mcart_1(A_2151, B_2153, C_2152, D_2155, E_2154) | ~m1_subset_1(E_2154, k4_zfmisc_1(A_2151, B_2153, C_2152, D_2155)) | k1_xboole_0=D_2155 | k1_xboole_0=C_2152 | k1_xboole_0=B_2153 | k1_xboole_0=A_2151)), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.35  tff(c_16978, plain, (k2_mcart_1(k1_mcart_1('#skF_13'))=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_16975])).
% 11.21/4.35  tff(c_16981, plain, (k2_mcart_1(k1_mcart_1('#skF_13'))=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_16972, c_16978])).
% 11.21/4.35  tff(c_17050, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_16981])).
% 11.21/4.35  tff(c_17055, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_17050, c_12])).
% 11.21/4.35  tff(c_17057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13030, c_17055])).
% 11.21/4.35  tff(c_17059, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_16981])).
% 11.21/4.35  tff(c_17113, plain, (![D_2172, B_2170, C_2169, E_2171, A_2168]: (k8_mcart_1(A_2168, B_2170, C_2169, D_2172, E_2171)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_2171))) | ~m1_subset_1(E_2171, k4_zfmisc_1(A_2168, B_2170, C_2169, D_2172)) | k1_xboole_0=D_2172 | k1_xboole_0=C_2169 | k1_xboole_0=B_2170 | k1_xboole_0=A_2168)), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.35  tff(c_17115, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_17113])).
% 11.21/4.35  tff(c_17118, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_16972, c_17059, c_17115])).
% 11.21/4.35  tff(c_17276, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_17118])).
% 11.21/4.35  tff(c_17283, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_17276, c_12])).
% 11.21/4.35  tff(c_17285, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13031, c_17283])).
% 11.21/4.35  tff(c_17287, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_17118])).
% 11.21/4.35  tff(c_17029, plain, (![A_2158, D_2162, C_2159, B_2160, E_2161]: (k9_mcart_1(A_2158, B_2160, C_2159, D_2162, E_2161)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_2161))) | ~m1_subset_1(E_2161, k4_zfmisc_1(A_2158, B_2160, C_2159, D_2162)) | k1_xboole_0=D_2162 | k1_xboole_0=C_2159 | k1_xboole_0=B_2160 | k1_xboole_0=A_2158)), inference(cnfTransformation, [status(thm)], [f_90])).
% 11.21/4.35  tff(c_17031, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_50, c_17029])).
% 11.21/4.35  tff(c_17034, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_16972, c_17031])).
% 11.21/4.35  tff(c_17357, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_13')))=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13') | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_17059, c_17287, c_17034])).
% 11.21/4.35  tff(c_17358, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_17357])).
% 11.21/4.35  tff(c_17366, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17358, c_12])).
% 11.21/4.35  tff(c_17368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13011, c_17366])).
% 11.21/4.35  tff(c_17370, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_17357])).
% 11.21/4.35  tff(c_17058, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8' | k2_mcart_1(k1_mcart_1('#skF_13'))=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13')), inference(splitRight, [status(thm)], [c_16981])).
% 11.21/4.35  tff(c_17732, plain, (k2_mcart_1(k1_mcart_1('#skF_13'))=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13')), inference(negUnitSimplification, [status(thm)], [c_17370, c_17287, c_17058])).
% 11.21/4.35  tff(c_18551, plain, (![D_2345, B_2346, A_2344, C_2343, A_2347]: (r2_hidden(k1_mcart_1(A_2344), k3_zfmisc_1(A_2347, B_2346, C_2343)) | ~r2_hidden(A_2344, k4_zfmisc_1(A_2347, B_2346, C_2343, D_2345)))), inference(superposition, [status(thm), theory('equality')], [c_13014, c_36])).
% 11.21/4.35  tff(c_18613, plain, (r2_hidden(k1_mcart_1('#skF_13'), k3_zfmisc_1('#skF_9', '#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_48, c_18551])).
% 11.21/4.35  tff(c_12945, plain, (![A_1690, C_1691, B_1692]: (r2_hidden(k2_mcart_1(A_1690), C_1691) | ~r2_hidden(A_1690, k2_zfmisc_1(B_1692, C_1691)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.21/4.35  tff(c_12947, plain, (![A_1690, C_20, A_18, B_19]: (r2_hidden(k2_mcart_1(A_1690), C_20) | ~r2_hidden(A_1690, k3_zfmisc_1(A_18, B_19, C_20)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_12945])).
% 11.21/4.35  tff(c_18618, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_13')), '#skF_11')), inference(resolution, [status(thm)], [c_18613, c_12947])).
% 11.21/4.35  tff(c_18626, plain, (r2_hidden(k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_13'), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_17732, c_18618])).
% 11.21/4.35  tff(c_18628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15692, c_18626])).
% 11.21/4.35  tff(c_18629, plain, (v1_xboole_0('#skF_11')), inference(splitRight, [status(thm)], [c_13012])).
% 11.21/4.35  tff(c_18981, plain, (![B_2391, C_2392]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_2391, C_2392))), C_2392) | v1_xboole_0(k2_zfmisc_1(B_2391, C_2392)))), inference(resolution, [status(thm)], [c_4, c_12945])).
% 11.21/4.35  tff(c_19023, plain, (![C_2395, B_2396]: (~v1_xboole_0(C_2395) | v1_xboole_0(k2_zfmisc_1(B_2396, C_2395)))), inference(resolution, [status(thm)], [c_18981, c_2])).
% 11.21/4.35  tff(c_19029, plain, (![C_20, A_18, B_19]: (~v1_xboole_0(C_20) | v1_xboole_0(k3_zfmisc_1(A_18, B_19, C_20)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_19023])).
% 11.21/4.35  tff(c_19411, plain, (![B_2451, C_2452]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_2451, C_2452))), B_2451) | v1_xboole_0(k2_zfmisc_1(B_2451, C_2452)))), inference(resolution, [status(thm)], [c_4, c_12918])).
% 11.21/4.35  tff(c_19485, plain, (![B_2456, C_2457]: (~v1_xboole_0(B_2456) | v1_xboole_0(k2_zfmisc_1(B_2456, C_2457)))), inference(resolution, [status(thm)], [c_19411, c_2])).
% 11.21/4.35  tff(c_19706, plain, (![A_2473, B_2474, C_2475, D_2476]: (~v1_xboole_0(k3_zfmisc_1(A_2473, B_2474, C_2475)) | v1_xboole_0(k4_zfmisc_1(A_2473, B_2474, C_2475, D_2476)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_19485])).
% 11.21/4.35  tff(c_19710, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_9', '#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_19706, c_74])).
% 11.21/4.35  tff(c_19716, plain, (~v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_19029, c_19710])).
% 11.21/4.35  tff(c_19721, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18629, c_19716])).
% 11.21/4.35  tff(c_19722, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_13008])).
% 11.21/4.35  tff(c_21539, plain, (![B_2694, C_2695]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_2694, C_2695))), C_2695) | v1_xboole_0(k2_zfmisc_1(B_2694, C_2695)))), inference(resolution, [status(thm)], [c_4, c_12945])).
% 11.21/4.35  tff(c_21569, plain, (![C_2695, B_2694]: (~v1_xboole_0(C_2695) | v1_xboole_0(k2_zfmisc_1(B_2694, C_2695)))), inference(resolution, [status(thm)], [c_21539, c_2])).
% 11.21/4.35  tff(c_19827, plain, (![B_2499, C_2500]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_2499, C_2500))), B_2499) | v1_xboole_0(k2_zfmisc_1(B_2499, C_2500)))), inference(resolution, [status(thm)], [c_4, c_12918])).
% 11.21/4.35  tff(c_19868, plain, (![B_2503, C_2504]: (~v1_xboole_0(B_2503) | v1_xboole_0(k2_zfmisc_1(B_2503, C_2504)))), inference(resolution, [status(thm)], [c_19827, c_2])).
% 11.21/4.35  tff(c_19874, plain, (![A_18, B_19, C_20]: (~v1_xboole_0(k2_zfmisc_1(A_18, B_19)) | v1_xboole_0(k3_zfmisc_1(A_18, B_19, C_20)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_19868])).
% 11.21/4.35  tff(c_21800, plain, (![A_2731, B_2732, C_2733, D_2734]: (~v1_xboole_0(k3_zfmisc_1(A_2731, B_2732, C_2733)) | v1_xboole_0(k4_zfmisc_1(A_2731, B_2732, C_2733, D_2734)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_19868])).
% 11.21/4.35  tff(c_21804, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_9', '#skF_10', '#skF_11'))), inference(resolution, [status(thm)], [c_21800, c_74])).
% 11.21/4.35  tff(c_21812, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_19874, c_21804])).
% 11.21/4.35  tff(c_21815, plain, (~v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_21569, c_21812])).
% 11.21/4.35  tff(c_21822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19722, c_21815])).
% 11.21/4.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.21/4.35  
% 11.21/4.35  Inference rules
% 11.21/4.35  ----------------------
% 11.21/4.35  #Ref     : 0
% 11.21/4.35  #Sup     : 5136
% 11.21/4.35  #Fact    : 0
% 11.21/4.35  #Define  : 0
% 11.21/4.35  #Split   : 319
% 11.21/4.35  #Chain   : 0
% 11.21/4.35  #Close   : 0
% 11.21/4.35  
% 11.21/4.35  Ordering : KBO
% 11.21/4.35  
% 11.21/4.35  Simplification rules
% 11.21/4.35  ----------------------
% 11.21/4.35  #Subsume      : 1864
% 11.21/4.35  #Demod        : 1279
% 11.21/4.35  #Tautology    : 317
% 11.21/4.35  #SimpNegUnit  : 410
% 11.21/4.35  #BackRed      : 412
% 11.21/4.35  
% 11.21/4.35  #Partial instantiations: 0
% 11.21/4.35  #Strategies tried      : 1
% 11.21/4.35  
% 11.21/4.35  Timing (in seconds)
% 11.21/4.35  ----------------------
% 11.21/4.35  Preprocessing        : 0.36
% 11.21/4.35  Parsing              : 0.18
% 11.21/4.35  CNF conversion       : 0.03
% 11.21/4.35  Main loop            : 3.15
% 11.21/4.35  Inferencing          : 0.99
% 11.21/4.35  Reduction            : 0.98
% 11.21/4.35  Demodulation         : 0.61
% 11.21/4.35  BG Simplification    : 0.11
% 11.21/4.35  Subsumption          : 0.76
% 11.21/4.36  Abstraction          : 0.12
% 11.21/4.36  MUC search           : 0.00
% 11.21/4.36  Cooper               : 0.00
% 11.21/4.36  Total                : 3.61
% 11.21/4.36  Index Insertion      : 0.00
% 11.21/4.36  Index Deletion       : 0.00
% 11.21/4.36  Index Matching       : 0.00
% 11.21/4.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
