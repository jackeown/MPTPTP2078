%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:18 EST 2020

% Result     : Theorem 15.95s
% Output     : CNFRefutation 16.13s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 550 expanded)
%              Number of leaves         :   42 ( 212 expanded)
%              Depth                    :   18
%              Number of atoms          :  221 (1939 expanded)
%              Number of equality atoms :  117 (1037 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( m1_subset_1(F,k4_zfmisc_1(A,B,C,D))
       => ( ! [G] :
              ( m1_subset_1(G,A)
             => ! [H] :
                  ( m1_subset_1(H,B)
                 => ! [I] :
                      ( m1_subset_1(I,C)
                     => ! [J] :
                          ( m1_subset_1(J,D)
                         => ( F = k4_mcart_1(G,H,I,J)
                           => E = I ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k10_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).

tff(f_113,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k11_mcart_1(A,B,C,D,E),D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k10_mcart_1(A,B,C,D,E),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k9_mcart_1(A,B,C,D,E),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

tff(f_57,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k8_mcart_1(A,B,C,D,E),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_mcart_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_483,plain,(
    ! [C_190,B_191,D_193,A_192,E_189] :
      ( k11_mcart_1(A_192,B_191,C_190,D_193,E_189) = k2_mcart_1(E_189)
      | ~ m1_subset_1(E_189,k4_zfmisc_1(A_192,B_191,C_190,D_193))
      | k1_xboole_0 = D_193
      | k1_xboole_0 = C_190
      | k1_xboole_0 = B_191
      | k1_xboole_0 = A_192 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_502,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = k2_mcart_1('#skF_6')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_483])).

tff(c_521,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = k2_mcart_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_50,c_502])).

tff(c_18,plain,(
    ! [A_25,E_29,C_27,D_28,B_26] :
      ( m1_subset_1(k11_mcart_1(A_25,B_26,C_27,D_28,E_29),D_28)
      | ~ m1_subset_1(E_29,k4_zfmisc_1(A_25,B_26,C_27,D_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_529,plain,
    ( m1_subset_1(k2_mcart_1('#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_6',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_18])).

tff(c_533,plain,(
    m1_subset_1(k2_mcart_1('#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_529])).

tff(c_197,plain,(
    ! [A_127,B_128,C_129,D_130] : k2_zfmisc_1(k3_zfmisc_1(A_127,B_128,C_129),D_130) = k4_zfmisc_1(A_127,B_128,C_129,D_130) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_209,plain,(
    ! [A_127,B_128,C_129,D_130] : v1_relat_1(k4_zfmisc_1(A_127,B_128,C_129,D_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_6])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_193,plain,(
    ! [A_125,B_126] :
      ( k4_tarski(k1_mcart_1(A_125),k2_mcart_1(A_125)) = A_125
      | ~ r2_hidden(A_125,B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1950,plain,(
    ! [A_298,B_299] :
      ( k4_tarski(k1_mcart_1(A_298),k2_mcart_1(A_298)) = A_298
      | ~ v1_relat_1(B_299)
      | v1_xboole_0(B_299)
      | ~ m1_subset_1(A_298,B_299) ) ),
    inference(resolution,[status(thm)],[c_4,c_193])).

tff(c_1962,plain,
    ( k4_tarski(k1_mcart_1('#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6'
    | ~ v1_relat_1(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4'))
    | v1_xboole_0(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_1950])).

tff(c_1970,plain,
    ( k4_tarski(k1_mcart_1('#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6'
    | v1_xboole_0(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_1962])).

tff(c_1971,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1970])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1975,plain,(
    k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1971,c_2])).

tff(c_30,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( k4_zfmisc_1(A_45,B_46,C_47,D_48) != k1_xboole_0
      | k1_xboole_0 = D_48
      | k1_xboole_0 = C_47
      | k1_xboole_0 = B_46
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1991,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1975,c_30])).

tff(c_2005,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_50,c_1991])).

tff(c_2006,plain,(
    k4_tarski(k1_mcart_1('#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1970])).

tff(c_16,plain,(
    ! [C_22,D_23,A_20,B_21,E_24] :
      ( m1_subset_1(k10_mcart_1(A_20,B_21,C_22,D_23,E_24),C_22)
      | ~ m1_subset_1(E_24,k4_zfmisc_1(A_20,B_21,C_22,D_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_48,plain,(
    k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_145,plain,(
    ! [A_105,B_106,C_107] : k2_zfmisc_1(k2_zfmisc_1(A_105,B_106),C_107) = k3_zfmisc_1(A_105,B_106,C_107) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_155,plain,(
    ! [A_105,B_106,C_107] : v1_relat_1(k3_zfmisc_1(A_105,B_106,C_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_6])).

tff(c_555,plain,(
    ! [C_197,D_200,E_196,B_198,A_199] :
      ( k2_mcart_1(k1_mcart_1(E_196)) = k10_mcart_1(A_199,B_198,C_197,D_200,E_196)
      | ~ m1_subset_1(E_196,k4_zfmisc_1(A_199,B_198,C_197,D_200))
      | k1_xboole_0 = D_200
      | k1_xboole_0 = C_197
      | k1_xboole_0 = B_198
      | k1_xboole_0 = A_199 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_574,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_6')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_555])).

tff(c_593,plain,(
    k2_mcart_1(k1_mcart_1('#skF_6')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_50,c_574])).

tff(c_2007,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1970])).

tff(c_26,plain,(
    ! [A_40,B_41,C_42] :
      ( r2_hidden(k1_mcart_1(A_40),B_41)
      | ~ r2_hidden(A_40,k2_zfmisc_1(B_41,C_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2043,plain,(
    ! [D_307,A_303,C_305,A_306,B_304] :
      ( r2_hidden(k1_mcart_1(A_303),k3_zfmisc_1(A_306,B_304,C_305))
      | ~ r2_hidden(A_303,k4_zfmisc_1(A_306,B_304,C_305,D_307)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_26])).

tff(c_16521,plain,(
    ! [B_884,A_883,D_880,C_881,A_882] :
      ( r2_hidden(k1_mcart_1(A_883),k3_zfmisc_1(A_882,B_884,C_881))
      | v1_xboole_0(k4_zfmisc_1(A_882,B_884,C_881,D_880))
      | ~ m1_subset_1(A_883,k4_zfmisc_1(A_882,B_884,C_881,D_880)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2043])).

tff(c_16539,plain,
    ( r2_hidden(k1_mcart_1('#skF_6'),k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | v1_xboole_0(k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_16521])).

tff(c_16556,plain,(
    r2_hidden(k1_mcart_1('#skF_6'),k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_2007,c_16539])).

tff(c_28,plain,(
    ! [A_43,B_44] :
      ( k4_tarski(k1_mcart_1(A_43),k2_mcart_1(A_43)) = A_43
      | ~ r2_hidden(A_43,B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16564,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_6')),k2_mcart_1(k1_mcart_1('#skF_6'))) = k1_mcart_1('#skF_6')
    | ~ v1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16556,c_28])).

tff(c_16570,plain,(
    k4_tarski(k1_mcart_1(k1_mcart_1('#skF_6')),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')) = k1_mcart_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_593,c_16564])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k4_tarski(k4_tarski(A_6,B_7),C_8) = k3_mcart_1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16598,plain,(
    ! [C_8] : k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')),k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),C_8) = k4_tarski(k1_mcart_1('#skF_6'),C_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_16570,c_8])).

tff(c_22,plain,(
    ! [A_35,B_36,C_37,D_38,E_39] :
      ( m1_subset_1(k9_mcart_1(A_35,B_36,C_37,D_38,E_39),B_36)
      | ~ m1_subset_1(E_39,k4_zfmisc_1(A_35,B_36,C_37,D_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_20,plain,(
    ! [D_33,A_30,C_32,B_31,E_34] :
      ( m1_subset_1(k8_mcart_1(A_30,B_31,C_32,D_33,E_34),A_30)
      | ~ m1_subset_1(E_34,k4_zfmisc_1(A_30,B_31,C_32,D_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_681,plain,(
    ! [E_205,D_209,C_206,A_208,B_207] :
      ( k9_mcart_1(A_208,B_207,C_206,D_209,E_205) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_205)))
      | ~ m1_subset_1(E_205,k4_zfmisc_1(A_208,B_207,C_206,D_209))
      | k1_xboole_0 = D_209
      | k1_xboole_0 = C_206
      | k1_xboole_0 = B_207
      | k1_xboole_0 = A_208 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_695,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_681])).

tff(c_710,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_50,c_695])).

tff(c_816,plain,(
    ! [C_215,A_217,B_216,D_218,E_214] :
      ( k8_mcart_1(A_217,B_216,C_215,D_218,E_214) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_214)))
      | ~ m1_subset_1(E_214,k4_zfmisc_1(A_217,B_216,C_215,D_218))
      | k1_xboole_0 = D_218
      | k1_xboole_0 = C_215
      | k1_xboole_0 = B_216
      | k1_xboole_0 = A_217 ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_830,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_816])).

tff(c_845,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_50,c_830])).

tff(c_153,plain,(
    ! [A_40,A_105,B_106,C_107] :
      ( r2_hidden(k1_mcart_1(A_40),k2_zfmisc_1(A_105,B_106))
      | ~ r2_hidden(A_40,k3_zfmisc_1(A_105,B_106,C_107)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_26])).

tff(c_16567,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_6')),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16556,c_153])).

tff(c_16574,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6'))),k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')))) = k1_mcart_1(k1_mcart_1('#skF_6'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16567,c_28])).

tff(c_16581,plain,(
    k4_tarski(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6')) = k1_mcart_1(k1_mcart_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_710,c_845,c_16574])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14,D_15] : k4_tarski(k3_mcart_1(A_12,B_13,C_14),D_15) = k4_mcart_1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_164,plain,(
    ! [A_108,B_109,C_110] : k4_tarski(k4_tarski(A_108,B_109),C_110) = k3_mcart_1(A_108,B_109,C_110) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_173,plain,(
    ! [A_6,B_7,C_8,C_110] : k3_mcart_1(k4_tarski(A_6,B_7),C_8,C_110) = k4_tarski(k3_mcart_1(A_6,B_7,C_8),C_110) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_164])).

tff(c_1118,plain,(
    ! [A_6,B_7,C_8,C_110] : k3_mcart_1(k4_tarski(A_6,B_7),C_8,C_110) = k4_mcart_1(A_6,B_7,C_8,C_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_173])).

tff(c_19234,plain,(
    ! [C_995,C_996] : k4_mcart_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),C_995,C_996) = k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')),C_995,C_996) ),
    inference(superposition,[status(thm),theory(equality)],[c_16581,c_1118])).

tff(c_58,plain,(
    ! [I_82,G_70,H_78,J_84] :
      ( I_82 = '#skF_5'
      | k4_mcart_1(G_70,H_78,I_82,J_84) != '#skF_6'
      | ~ m1_subset_1(J_84,'#skF_4')
      | ~ m1_subset_1(I_82,'#skF_3')
      | ~ m1_subset_1(H_78,'#skF_2')
      | ~ m1_subset_1(G_70,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_19243,plain,(
    ! [C_995,C_996] :
      ( C_995 = '#skF_5'
      | k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')),C_995,C_996) != '#skF_6'
      | ~ m1_subset_1(C_996,'#skF_4')
      | ~ m1_subset_1(C_995,'#skF_3')
      | ~ m1_subset_1(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2')
      | ~ m1_subset_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19234,c_58])).

tff(c_19669,plain,(
    ~ m1_subset_1(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_19243])).

tff(c_19672,plain,(
    ~ m1_subset_1('#skF_6',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_19669])).

tff(c_19676,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_19672])).

tff(c_19677,plain,(
    ! [C_995,C_996] :
      ( ~ m1_subset_1(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2')
      | C_995 = '#skF_5'
      | k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')),C_995,C_996) != '#skF_6'
      | ~ m1_subset_1(C_996,'#skF_4')
      | ~ m1_subset_1(C_995,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_19243])).

tff(c_19870,plain,(
    ~ m1_subset_1(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_19677])).

tff(c_19873,plain,(
    ~ m1_subset_1('#skF_6',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_19870])).

tff(c_19877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_19873])).

tff(c_20042,plain,(
    ! [C_1031,C_1032] :
      ( C_1031 = '#skF_5'
      | k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')),C_1031,C_1032) != '#skF_6'
      | ~ m1_subset_1(C_1032,'#skF_4')
      | ~ m1_subset_1(C_1031,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_19677])).

tff(c_20045,plain,(
    ! [C_8] :
      ( k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6') = '#skF_5'
      | k4_tarski(k1_mcart_1('#skF_6'),C_8) != '#skF_6'
      | ~ m1_subset_1(C_8,'#skF_4')
      | ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16598,c_20042])).

tff(c_20046,plain,(
    ! [C_8] :
      ( k4_tarski(k1_mcart_1('#skF_6'),C_8) != '#skF_6'
      | ~ m1_subset_1(C_8,'#skF_4')
      | ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_20045])).

tff(c_20336,plain,(
    ~ m1_subset_1(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20046])).

tff(c_20339,plain,(
    ~ m1_subset_1('#skF_6',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_16,c_20336])).

tff(c_20343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_20339])).

tff(c_20346,plain,(
    ! [C_1046] :
      ( k4_tarski(k1_mcart_1('#skF_6'),C_1046) != '#skF_6'
      | ~ m1_subset_1(C_1046,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_20046])).

tff(c_20349,plain,(
    ~ m1_subset_1(k2_mcart_1('#skF_6'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2006,c_20346])).

tff(c_20353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_20349])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.95/8.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.95/8.63  
% 15.95/8.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.95/8.63  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 15.95/8.63  
% 15.95/8.63  %Foreground sorts:
% 15.95/8.63  
% 15.95/8.63  
% 15.95/8.63  %Background operators:
% 15.95/8.63  
% 15.95/8.63  
% 15.95/8.63  %Foreground operators:
% 15.95/8.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.95/8.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.95/8.63  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 15.95/8.63  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 15.95/8.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.95/8.63  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 15.95/8.63  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 15.95/8.63  tff('#skF_5', type, '#skF_5': $i).
% 15.95/8.63  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 15.95/8.63  tff('#skF_6', type, '#skF_6': $i).
% 15.95/8.63  tff('#skF_2', type, '#skF_2': $i).
% 15.95/8.63  tff('#skF_3', type, '#skF_3': $i).
% 15.95/8.63  tff('#skF_1', type, '#skF_1': $i).
% 15.95/8.63  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 15.95/8.63  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 15.95/8.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.95/8.63  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 15.95/8.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.95/8.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.95/8.63  tff('#skF_4', type, '#skF_4': $i).
% 15.95/8.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.95/8.63  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 15.95/8.63  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 15.95/8.63  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 15.95/8.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 15.95/8.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.95/8.63  
% 16.13/8.65  tff(f_142, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = I)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k10_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_mcart_1)).
% 16.13/8.65  tff(f_113, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 16.13/8.65  tff(f_53, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k11_mcart_1(A, B, C, D, E), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_mcart_1)).
% 16.13/8.65  tff(f_45, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 16.13/8.65  tff(f_37, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 16.13/8.65  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 16.13/8.65  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 16.13/8.65  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 16.13/8.65  tff(f_88, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 16.13/8.65  tff(f_49, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k10_mcart_1(A, B, C, D, E), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_mcart_1)).
% 16.13/8.65  tff(f_41, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 16.13/8.65  tff(f_67, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 16.13/8.65  tff(f_39, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 16.13/8.65  tff(f_61, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k9_mcart_1(A, B, C, D, E), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_mcart_1)).
% 16.13/8.65  tff(f_57, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k8_mcart_1(A, B, C, D, E), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_mcart_1)).
% 16.13/8.65  tff(f_43, axiom, (![A, B, C, D]: (k4_mcart_1(A, B, C, D) = k4_tarski(k3_mcart_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_mcart_1)).
% 16.13/8.65  tff(c_60, plain, (m1_subset_1('#skF_6', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.13/8.65  tff(c_56, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.13/8.65  tff(c_54, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.13/8.65  tff(c_52, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.13/8.65  tff(c_50, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.13/8.65  tff(c_483, plain, (![C_190, B_191, D_193, A_192, E_189]: (k11_mcart_1(A_192, B_191, C_190, D_193, E_189)=k2_mcart_1(E_189) | ~m1_subset_1(E_189, k4_zfmisc_1(A_192, B_191, C_190, D_193)) | k1_xboole_0=D_193 | k1_xboole_0=C_190 | k1_xboole_0=B_191 | k1_xboole_0=A_192)), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.13/8.65  tff(c_502, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_mcart_1('#skF_6') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_60, c_483])).
% 16.13/8.65  tff(c_521, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_mcart_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_50, c_502])).
% 16.13/8.65  tff(c_18, plain, (![A_25, E_29, C_27, D_28, B_26]: (m1_subset_1(k11_mcart_1(A_25, B_26, C_27, D_28, E_29), D_28) | ~m1_subset_1(E_29, k4_zfmisc_1(A_25, B_26, C_27, D_28)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.13/8.65  tff(c_529, plain, (m1_subset_1(k2_mcart_1('#skF_6'), '#skF_4') | ~m1_subset_1('#skF_6', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_521, c_18])).
% 16.13/8.65  tff(c_533, plain, (m1_subset_1(k2_mcart_1('#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_529])).
% 16.13/8.65  tff(c_197, plain, (![A_127, B_128, C_129, D_130]: (k2_zfmisc_1(k3_zfmisc_1(A_127, B_128, C_129), D_130)=k4_zfmisc_1(A_127, B_128, C_129, D_130))), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.13/8.65  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.13/8.65  tff(c_209, plain, (![A_127, B_128, C_129, D_130]: (v1_relat_1(k4_zfmisc_1(A_127, B_128, C_129, D_130)))), inference(superposition, [status(thm), theory('equality')], [c_197, c_6])).
% 16.13/8.65  tff(c_4, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.13/8.65  tff(c_193, plain, (![A_125, B_126]: (k4_tarski(k1_mcart_1(A_125), k2_mcart_1(A_125))=A_125 | ~r2_hidden(A_125, B_126) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.13/8.65  tff(c_1950, plain, (![A_298, B_299]: (k4_tarski(k1_mcart_1(A_298), k2_mcart_1(A_298))=A_298 | ~v1_relat_1(B_299) | v1_xboole_0(B_299) | ~m1_subset_1(A_298, B_299))), inference(resolution, [status(thm)], [c_4, c_193])).
% 16.13/8.65  tff(c_1962, plain, (k4_tarski(k1_mcart_1('#skF_6'), k2_mcart_1('#skF_6'))='#skF_6' | ~v1_relat_1(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')) | v1_xboole_0(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_1950])).
% 16.13/8.65  tff(c_1970, plain, (k4_tarski(k1_mcart_1('#skF_6'), k2_mcart_1('#skF_6'))='#skF_6' | v1_xboole_0(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_1962])).
% 16.13/8.65  tff(c_1971, plain, (v1_xboole_0(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_1970])).
% 16.13/8.65  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.13/8.65  tff(c_1975, plain, (k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1971, c_2])).
% 16.13/8.65  tff(c_30, plain, (![A_45, B_46, C_47, D_48]: (k4_zfmisc_1(A_45, B_46, C_47, D_48)!=k1_xboole_0 | k1_xboole_0=D_48 | k1_xboole_0=C_47 | k1_xboole_0=B_46 | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.13/8.65  tff(c_1991, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1975, c_30])).
% 16.13/8.65  tff(c_2005, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_50, c_1991])).
% 16.13/8.65  tff(c_2006, plain, (k4_tarski(k1_mcart_1('#skF_6'), k2_mcart_1('#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1970])).
% 16.13/8.65  tff(c_16, plain, (![C_22, D_23, A_20, B_21, E_24]: (m1_subset_1(k10_mcart_1(A_20, B_21, C_22, D_23, E_24), C_22) | ~m1_subset_1(E_24, k4_zfmisc_1(A_20, B_21, C_22, D_23)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.13/8.65  tff(c_48, plain, (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.13/8.65  tff(c_145, plain, (![A_105, B_106, C_107]: (k2_zfmisc_1(k2_zfmisc_1(A_105, B_106), C_107)=k3_zfmisc_1(A_105, B_106, C_107))), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.13/8.65  tff(c_155, plain, (![A_105, B_106, C_107]: (v1_relat_1(k3_zfmisc_1(A_105, B_106, C_107)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_6])).
% 16.13/8.65  tff(c_555, plain, (![C_197, D_200, E_196, B_198, A_199]: (k2_mcart_1(k1_mcart_1(E_196))=k10_mcart_1(A_199, B_198, C_197, D_200, E_196) | ~m1_subset_1(E_196, k4_zfmisc_1(A_199, B_198, C_197, D_200)) | k1_xboole_0=D_200 | k1_xboole_0=C_197 | k1_xboole_0=B_198 | k1_xboole_0=A_199)), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.13/8.65  tff(c_574, plain, (k2_mcart_1(k1_mcart_1('#skF_6'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_60, c_555])).
% 16.13/8.65  tff(c_593, plain, (k2_mcart_1(k1_mcart_1('#skF_6'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_50, c_574])).
% 16.13/8.65  tff(c_2007, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1970])).
% 16.13/8.65  tff(c_26, plain, (![A_40, B_41, C_42]: (r2_hidden(k1_mcart_1(A_40), B_41) | ~r2_hidden(A_40, k2_zfmisc_1(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.13/8.65  tff(c_2043, plain, (![D_307, A_303, C_305, A_306, B_304]: (r2_hidden(k1_mcart_1(A_303), k3_zfmisc_1(A_306, B_304, C_305)) | ~r2_hidden(A_303, k4_zfmisc_1(A_306, B_304, C_305, D_307)))), inference(superposition, [status(thm), theory('equality')], [c_197, c_26])).
% 16.13/8.65  tff(c_16521, plain, (![B_884, A_883, D_880, C_881, A_882]: (r2_hidden(k1_mcart_1(A_883), k3_zfmisc_1(A_882, B_884, C_881)) | v1_xboole_0(k4_zfmisc_1(A_882, B_884, C_881, D_880)) | ~m1_subset_1(A_883, k4_zfmisc_1(A_882, B_884, C_881, D_880)))), inference(resolution, [status(thm)], [c_4, c_2043])).
% 16.13/8.65  tff(c_16539, plain, (r2_hidden(k1_mcart_1('#skF_6'), k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | v1_xboole_0(k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_16521])).
% 16.13/8.65  tff(c_16556, plain, (r2_hidden(k1_mcart_1('#skF_6'), k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_2007, c_16539])).
% 16.13/8.65  tff(c_28, plain, (![A_43, B_44]: (k4_tarski(k1_mcart_1(A_43), k2_mcart_1(A_43))=A_43 | ~r2_hidden(A_43, B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.13/8.65  tff(c_16564, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_6')), k2_mcart_1(k1_mcart_1('#skF_6')))=k1_mcart_1('#skF_6') | ~v1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_16556, c_28])).
% 16.13/8.65  tff(c_16570, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_6')), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'))=k1_mcart_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_593, c_16564])).
% 16.13/8.65  tff(c_8, plain, (![A_6, B_7, C_8]: (k4_tarski(k4_tarski(A_6, B_7), C_8)=k3_mcart_1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.13/8.65  tff(c_16598, plain, (![C_8]: (k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')), k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), C_8)=k4_tarski(k1_mcart_1('#skF_6'), C_8))), inference(superposition, [status(thm), theory('equality')], [c_16570, c_8])).
% 16.13/8.65  tff(c_22, plain, (![A_35, B_36, C_37, D_38, E_39]: (m1_subset_1(k9_mcart_1(A_35, B_36, C_37, D_38, E_39), B_36) | ~m1_subset_1(E_39, k4_zfmisc_1(A_35, B_36, C_37, D_38)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.13/8.65  tff(c_20, plain, (![D_33, A_30, C_32, B_31, E_34]: (m1_subset_1(k8_mcart_1(A_30, B_31, C_32, D_33, E_34), A_30) | ~m1_subset_1(E_34, k4_zfmisc_1(A_30, B_31, C_32, D_33)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.13/8.65  tff(c_681, plain, (![E_205, D_209, C_206, A_208, B_207]: (k9_mcart_1(A_208, B_207, C_206, D_209, E_205)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_205))) | ~m1_subset_1(E_205, k4_zfmisc_1(A_208, B_207, C_206, D_209)) | k1_xboole_0=D_209 | k1_xboole_0=C_206 | k1_xboole_0=B_207 | k1_xboole_0=A_208)), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.13/8.65  tff(c_695, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_60, c_681])).
% 16.13/8.65  tff(c_710, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_50, c_695])).
% 16.13/8.65  tff(c_816, plain, (![C_215, A_217, B_216, D_218, E_214]: (k8_mcart_1(A_217, B_216, C_215, D_218, E_214)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_214))) | ~m1_subset_1(E_214, k4_zfmisc_1(A_217, B_216, C_215, D_218)) | k1_xboole_0=D_218 | k1_xboole_0=C_215 | k1_xboole_0=B_216 | k1_xboole_0=A_217)), inference(cnfTransformation, [status(thm)], [f_113])).
% 16.13/8.65  tff(c_830, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_60, c_816])).
% 16.13/8.65  tff(c_845, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_50, c_830])).
% 16.13/8.65  tff(c_153, plain, (![A_40, A_105, B_106, C_107]: (r2_hidden(k1_mcart_1(A_40), k2_zfmisc_1(A_105, B_106)) | ~r2_hidden(A_40, k3_zfmisc_1(A_105, B_106, C_107)))), inference(superposition, [status(thm), theory('equality')], [c_145, c_26])).
% 16.13/8.65  tff(c_16567, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_6')), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_16556, c_153])).
% 16.13/8.65  tff(c_16574, plain, (k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6'))), k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6'))))=k1_mcart_1(k1_mcart_1('#skF_6')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_16567, c_28])).
% 16.13/8.65  tff(c_16581, plain, (k4_tarski(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'))=k1_mcart_1(k1_mcart_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_710, c_845, c_16574])).
% 16.13/8.65  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (k4_tarski(k3_mcart_1(A_12, B_13, C_14), D_15)=k4_mcart_1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.13/8.65  tff(c_164, plain, (![A_108, B_109, C_110]: (k4_tarski(k4_tarski(A_108, B_109), C_110)=k3_mcart_1(A_108, B_109, C_110))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.13/8.65  tff(c_173, plain, (![A_6, B_7, C_8, C_110]: (k3_mcart_1(k4_tarski(A_6, B_7), C_8, C_110)=k4_tarski(k3_mcart_1(A_6, B_7, C_8), C_110))), inference(superposition, [status(thm), theory('equality')], [c_8, c_164])).
% 16.13/8.65  tff(c_1118, plain, (![A_6, B_7, C_8, C_110]: (k3_mcart_1(k4_tarski(A_6, B_7), C_8, C_110)=k4_mcart_1(A_6, B_7, C_8, C_110))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_173])).
% 16.13/8.65  tff(c_19234, plain, (![C_995, C_996]: (k4_mcart_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), C_995, C_996)=k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')), C_995, C_996))), inference(superposition, [status(thm), theory('equality')], [c_16581, c_1118])).
% 16.13/8.65  tff(c_58, plain, (![I_82, G_70, H_78, J_84]: (I_82='#skF_5' | k4_mcart_1(G_70, H_78, I_82, J_84)!='#skF_6' | ~m1_subset_1(J_84, '#skF_4') | ~m1_subset_1(I_82, '#skF_3') | ~m1_subset_1(H_78, '#skF_2') | ~m1_subset_1(G_70, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 16.13/8.65  tff(c_19243, plain, (![C_995, C_996]: (C_995='#skF_5' | k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')), C_995, C_996)!='#skF_6' | ~m1_subset_1(C_996, '#skF_4') | ~m1_subset_1(C_995, '#skF_3') | ~m1_subset_1(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2') | ~m1_subset_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_19234, c_58])).
% 16.13/8.65  tff(c_19669, plain, (~m1_subset_1(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_1')), inference(splitLeft, [status(thm)], [c_19243])).
% 16.13/8.65  tff(c_19672, plain, (~m1_subset_1('#skF_6', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_19669])).
% 16.13/8.65  tff(c_19676, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_19672])).
% 16.13/8.65  tff(c_19677, plain, (![C_995, C_996]: (~m1_subset_1(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2') | C_995='#skF_5' | k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')), C_995, C_996)!='#skF_6' | ~m1_subset_1(C_996, '#skF_4') | ~m1_subset_1(C_995, '#skF_3'))), inference(splitRight, [status(thm)], [c_19243])).
% 16.13/8.65  tff(c_19870, plain, (~m1_subset_1(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2')), inference(splitLeft, [status(thm)], [c_19677])).
% 16.13/8.65  tff(c_19873, plain, (~m1_subset_1('#skF_6', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_19870])).
% 16.13/8.65  tff(c_19877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_19873])).
% 16.13/8.65  tff(c_20042, plain, (![C_1031, C_1032]: (C_1031='#skF_5' | k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_6')), C_1031, C_1032)!='#skF_6' | ~m1_subset_1(C_1032, '#skF_4') | ~m1_subset_1(C_1031, '#skF_3'))), inference(splitRight, [status(thm)], [c_19677])).
% 16.13/8.65  tff(c_20045, plain, (![C_8]: (k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6')='#skF_5' | k4_tarski(k1_mcart_1('#skF_6'), C_8)!='#skF_6' | ~m1_subset_1(C_8, '#skF_4') | ~m1_subset_1(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_16598, c_20042])).
% 16.13/8.65  tff(c_20046, plain, (![C_8]: (k4_tarski(k1_mcart_1('#skF_6'), C_8)!='#skF_6' | ~m1_subset_1(C_8, '#skF_4') | ~m1_subset_1(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_20045])).
% 16.13/8.65  tff(c_20336, plain, (~m1_subset_1(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_20046])).
% 16.13/8.65  tff(c_20339, plain, (~m1_subset_1('#skF_6', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_20336])).
% 16.13/8.65  tff(c_20343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_20339])).
% 16.13/8.65  tff(c_20346, plain, (![C_1046]: (k4_tarski(k1_mcart_1('#skF_6'), C_1046)!='#skF_6' | ~m1_subset_1(C_1046, '#skF_4'))), inference(splitRight, [status(thm)], [c_20046])).
% 16.13/8.65  tff(c_20349, plain, (~m1_subset_1(k2_mcart_1('#skF_6'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2006, c_20346])).
% 16.13/8.65  tff(c_20353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_533, c_20349])).
% 16.13/8.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.13/8.65  
% 16.13/8.65  Inference rules
% 16.13/8.65  ----------------------
% 16.13/8.65  #Ref     : 0
% 16.13/8.65  #Sup     : 5899
% 16.13/8.65  #Fact    : 0
% 16.13/8.65  #Define  : 0
% 16.13/8.65  #Split   : 15
% 16.13/8.65  #Chain   : 0
% 16.13/8.65  #Close   : 0
% 16.13/8.65  
% 16.13/8.65  Ordering : KBO
% 16.13/8.65  
% 16.13/8.65  Simplification rules
% 16.13/8.65  ----------------------
% 16.13/8.65  #Subsume      : 968
% 16.13/8.65  #Demod        : 1185
% 16.13/8.65  #Tautology    : 497
% 16.13/8.65  #SimpNegUnit  : 12
% 16.13/8.65  #BackRed      : 2
% 16.13/8.65  
% 16.13/8.65  #Partial instantiations: 0
% 16.13/8.65  #Strategies tried      : 1
% 16.13/8.65  
% 16.13/8.65  Timing (in seconds)
% 16.13/8.65  ----------------------
% 16.13/8.65  Preprocessing        : 0.34
% 16.13/8.65  Parsing              : 0.17
% 16.13/8.65  CNF conversion       : 0.03
% 16.13/8.65  Main loop            : 7.54
% 16.13/8.65  Inferencing          : 1.25
% 16.13/8.65  Reduction            : 1.17
% 16.13/8.65  Demodulation         : 0.83
% 16.13/8.65  BG Simplification    : 0.16
% 16.13/8.65  Subsumption          : 4.64
% 16.13/8.65  Abstraction          : 0.19
% 16.13/8.65  MUC search           : 0.00
% 16.13/8.65  Cooper               : 0.00
% 16.13/8.65  Total                : 7.91
% 16.13/8.65  Index Insertion      : 0.00
% 16.13/8.65  Index Deletion       : 0.00
% 16.13/8.65  Index Matching       : 0.00
% 16.13/8.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
