%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:24 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 4.03s
% Verified   : 
% Statistics : Number of formulae       :  264 ( 890 expanded)
%              Number of leaves         :   33 ( 290 expanded)
%              Depth                    :   11
%              Number of atoms          :  431 (3238 expanded)
%              Number of equality atoms :  198 (1330 expanded)
%              Maximal formula depth    :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
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

tff(f_33,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_68,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1019,plain,(
    ! [C_392,B_393,A_394] :
      ( ~ v1_xboole_0(C_392)
      | ~ m1_subset_1(B_393,k1_zfmisc_1(C_392))
      | ~ r2_hidden(A_394,B_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1029,plain,(
    ! [A_394] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_394,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_28,c_1019])).

tff(c_1050,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1029])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1028,plain,(
    ! [A_394] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_394,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_1019])).

tff(c_1032,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1028])).

tff(c_619,plain,(
    ! [C_248,B_249,A_250] :
      ( ~ v1_xboole_0(C_248)
      | ~ m1_subset_1(B_249,k1_zfmisc_1(C_248))
      | ~ r2_hidden(A_250,B_249) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_628,plain,(
    ! [A_250] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_250,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_619])).

tff(c_632,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_628])).

tff(c_629,plain,(
    ! [A_250] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_250,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_28,c_619])).

tff(c_651,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_629])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_630,plain,(
    ! [A_250] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_250,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_619])).

tff(c_650,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_630])).

tff(c_24,plain,(
    r2_hidden('#skF_9',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_634,plain,(
    ! [A_251,B_252,C_253,D_254] : k2_zfmisc_1(k3_zfmisc_1(A_251,B_252,C_253),D_254) = k4_zfmisc_1(A_251,B_252,C_253,D_254) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,C_13,B_12] :
      ( r2_hidden(k2_mcart_1(A_11),C_13)
      | ~ r2_hidden(A_11,k2_zfmisc_1(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_653,plain,(
    ! [A_263,B_259,A_261,C_260,D_262] :
      ( r2_hidden(k2_mcart_1(A_261),D_262)
      | ~ r2_hidden(A_261,k4_zfmisc_1(A_263,B_259,C_260,D_262)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_10])).

tff(c_656,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_24,c_653])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_631,plain,(
    ! [A_250] :
      ( ~ v1_xboole_0('#skF_1')
      | ~ r2_hidden(A_250,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_619])).

tff(c_633,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_631])).

tff(c_26,plain,(
    m1_subset_1('#skF_9',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_678,plain,(
    ! [D_268,A_272,C_270,E_269,B_271] :
      ( k11_mcart_1(A_272,B_271,C_270,D_268,E_269) = k2_mcart_1(E_269)
      | ~ m1_subset_1(E_269,k4_zfmisc_1(A_272,B_271,C_270,D_268))
      | k1_xboole_0 = D_268
      | k1_xboole_0 = C_270
      | k1_xboole_0 = B_271
      | k1_xboole_0 = A_272 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_682,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_678])).

tff(c_766,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_682])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_769,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_2])).

tff(c_771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_633,c_769])).

tff(c_772,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_682])).

tff(c_774,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_772])).

tff(c_22,plain,
    ( ~ r2_hidden(k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_8')
    | ~ r2_hidden(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_7')
    | ~ r2_hidden(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_6')
    | ~ r2_hidden(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_53,plain,(
    ~ r2_hidden(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_54,plain,(
    ! [C_52,B_53,A_54] :
      ( ~ v1_xboole_0(C_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(C_52))
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [A_54] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_54,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_28,c_54])).

tff(c_73,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_66,plain,(
    ! [A_54] :
      ( ~ v1_xboole_0('#skF_1')
      | ~ r2_hidden(A_54,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_54])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_95,plain,(
    ! [E_72,C_73,B_74,D_71,A_75] :
      ( k11_mcart_1(A_75,B_74,C_73,D_71,E_72) = k2_mcart_1(E_72)
      | ~ m1_subset_1(E_72,k4_zfmisc_1(A_75,B_74,C_73,D_71))
      | k1_xboole_0 = D_71
      | k1_xboole_0 = C_73
      | k1_xboole_0 = B_74
      | k1_xboole_0 = A_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_99,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_95])).

tff(c_126,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_128,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_2])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_128])).

tff(c_132,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_65,plain,(
    ! [A_54] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_54,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_54])).

tff(c_72,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_172,plain,(
    ! [A_98,C_96,E_95,D_94,B_97] :
      ( k2_mcart_1(k1_mcart_1(E_95)) = k10_mcart_1(A_98,B_97,C_96,D_94,E_95)
      | ~ m1_subset_1(E_95,k4_zfmisc_1(A_98,B_97,C_96,D_94))
      | k1_xboole_0 = D_94
      | k1_xboole_0 = C_96
      | k1_xboole_0 = B_97
      | k1_xboole_0 = A_98 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_175,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_172])).

tff(c_178,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_175])).

tff(c_227,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_232,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_2])).

tff(c_234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_232])).

tff(c_236,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_63,plain,(
    ! [A_54] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_54,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_54])).

tff(c_67,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_219,plain,(
    ! [A_108,D_104,B_107,E_105,C_106] :
      ( k9_mcart_1(A_108,B_107,C_106,D_104,E_105) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_105)))
      | ~ m1_subset_1(E_105,k4_zfmisc_1(A_108,B_107,C_106,D_104))
      | k1_xboole_0 = D_104
      | k1_xboole_0 = C_106
      | k1_xboole_0 = B_107
      | k1_xboole_0 = A_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_223,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_219])).

tff(c_226,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_223])).

tff(c_237,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_226])).

tff(c_238,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_244,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_2])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_244])).

tff(c_248,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_255,plain,(
    ! [A_113,D_109,C_111,E_110,B_112] :
      ( k8_mcart_1(A_113,B_112,C_111,D_109,E_110) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_110)))
      | ~ m1_subset_1(E_110,k4_zfmisc_1(A_113,B_112,C_111,D_109))
      | k1_xboole_0 = D_109
      | k1_xboole_0 = C_111
      | k1_xboole_0 = B_112
      | k1_xboole_0 = A_113 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_259,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_255])).

tff(c_262,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_236,c_248,c_259])).

tff(c_263,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_271,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_2])).

tff(c_273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_271])).

tff(c_274,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_75,plain,(
    ! [A_62,B_63,C_64,D_65] : k2_zfmisc_1(k3_zfmisc_1(A_62,B_63,C_64),D_65) = k4_zfmisc_1(A_62,B_63,C_64,D_65) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( r2_hidden(k1_mcart_1(A_11),B_12)
      | ~ r2_hidden(A_11,k2_zfmisc_1(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_162,plain,(
    ! [C_89,B_92,A_91,D_93,A_90] :
      ( r2_hidden(k1_mcart_1(A_91),k3_zfmisc_1(A_90,B_92,C_89))
      | ~ r2_hidden(A_91,k4_zfmisc_1(A_90,B_92,C_89,D_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_12])).

tff(c_165,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_24,c_162])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_zfmisc_1(k2_zfmisc_1(A_4,B_5),C_6) = k3_zfmisc_1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [A_55,B_56,C_57] :
      ( r2_hidden(k1_mcart_1(A_55),B_56)
      | ~ r2_hidden(A_55,k2_zfmisc_1(B_56,C_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_71,plain,(
    ! [A_55,A_4,B_5,C_6] :
      ( r2_hidden(k1_mcart_1(A_55),k2_zfmisc_1(A_4,B_5))
      | ~ r2_hidden(A_55,k3_zfmisc_1(A_4,B_5,C_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_69])).

tff(c_170,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_165,c_71])).

tff(c_183,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))),'#skF_5') ),
    inference(resolution,[status(thm)],[c_170,c_12])).

tff(c_276,plain,(
    r2_hidden(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_183])).

tff(c_278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_276])).

tff(c_279,plain,(
    ! [A_54] : ~ r2_hidden(A_54,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_283,plain,(
    ! [A_119,B_120,C_121,D_122] : k2_zfmisc_1(k3_zfmisc_1(A_119,B_120,C_121),D_122) = k4_zfmisc_1(A_119,B_120,C_121,D_122) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_299,plain,(
    ! [A_124,D_126,C_127,A_125,B_123] :
      ( r2_hidden(k2_mcart_1(A_125),D_126)
      | ~ r2_hidden(A_125,k4_zfmisc_1(A_124,B_123,C_127,D_126)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_10])).

tff(c_301,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_24,c_299])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_301])).

tff(c_306,plain,(
    ! [A_54] : ~ r2_hidden(A_54,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_308,plain,(
    ! [A_128,B_129,C_130,D_131] : k2_zfmisc_1(k3_zfmisc_1(A_128,B_129,C_130),D_131) = k4_zfmisc_1(A_128,B_129,C_130,D_131) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_391,plain,(
    ! [C_161,A_160,A_164,D_163,B_162] :
      ( r2_hidden(k1_mcart_1(A_164),k3_zfmisc_1(A_160,B_162,C_161))
      | ~ r2_hidden(A_164,k4_zfmisc_1(A_160,B_162,C_161,D_163)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_12])).

tff(c_394,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_24,c_391])).

tff(c_399,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_394,c_71])).

tff(c_404,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))),'#skF_6') ),
    inference(resolution,[status(thm)],[c_399,c_10])).

tff(c_409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_404])).

tff(c_410,plain,(
    ! [A_54] : ~ r2_hidden(A_54,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_418,plain,(
    ! [A_169,B_170,C_171,D_172] : k2_zfmisc_1(k3_zfmisc_1(A_169,B_170,C_171),D_172) = k4_zfmisc_1(A_169,B_170,C_171,D_172) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_470,plain,(
    ! [A_195,D_196,C_199,A_198,B_197] :
      ( r2_hidden(k1_mcart_1(A_198),k3_zfmisc_1(A_195,B_197,C_199))
      | ~ r2_hidden(A_198,k4_zfmisc_1(A_195,B_197,C_199,D_196)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_12])).

tff(c_473,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_24,c_470])).

tff(c_414,plain,(
    ! [A_166,B_167,C_168] :
      ( r2_hidden(k1_mcart_1(A_166),B_167)
      | ~ r2_hidden(A_166,k2_zfmisc_1(B_167,C_168)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_416,plain,(
    ! [A_166,A_4,B_5,C_6] :
      ( r2_hidden(k1_mcart_1(A_166),k2_zfmisc_1(A_4,B_5))
      | ~ r2_hidden(A_166,k3_zfmisc_1(A_4,B_5,C_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_414])).

tff(c_478,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_473,c_416])).

tff(c_489,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))),'#skF_5') ),
    inference(resolution,[status(thm)],[c_478,c_12])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_410,c_489])).

tff(c_496,plain,(
    ! [A_54] : ~ r2_hidden(A_54,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_506,plain,(
    ! [A_208,B_209,C_210,D_211] : k2_zfmisc_1(k3_zfmisc_1(A_208,B_209,C_210),D_211) = k4_zfmisc_1(A_208,B_209,C_210,D_211) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_593,plain,(
    ! [A_235,D_239,B_238,C_236,A_237] :
      ( r2_hidden(k1_mcart_1(A_237),k3_zfmisc_1(A_235,B_238,C_236))
      | ~ r2_hidden(A_237,k4_zfmisc_1(A_235,B_238,C_236,D_239)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_12])).

tff(c_596,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_24,c_593])).

tff(c_36,plain,(
    ! [A_49,B_50,C_51] : k2_zfmisc_1(k2_zfmisc_1(A_49,B_50),C_51) = k3_zfmisc_1(A_49,B_50,C_51) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    ! [A_11,C_51,A_49,B_50] :
      ( r2_hidden(k2_mcart_1(A_11),C_51)
      | ~ r2_hidden(A_11,k3_zfmisc_1(A_49,B_50,C_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_10])).

tff(c_607,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_596,c_44])).

tff(c_612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_496,c_607])).

tff(c_613,plain,
    ( ~ r2_hidden(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_6')
    | ~ r2_hidden(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_7')
    | ~ r2_hidden(k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_618,plain,(
    ~ r2_hidden(k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_613])).

tff(c_775,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_618])).

tff(c_778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_775])).

tff(c_779,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_772])).

tff(c_781,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_779])).

tff(c_794,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_2])).

tff(c_796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_650,c_794])).

tff(c_797,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_779])).

tff(c_799,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_797])).

tff(c_806,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_2])).

tff(c_808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_651,c_806])).

tff(c_809,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_816,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_809,c_2])).

tff(c_818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_632,c_816])).

tff(c_819,plain,(
    ! [A_250] : ~ r2_hidden(A_250,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_629])).

tff(c_828,plain,(
    ! [A_314,B_312,D_315,C_313,A_316] :
      ( r2_hidden(k2_mcart_1(A_314),D_315)
      | ~ r2_hidden(A_314,k4_zfmisc_1(A_316,B_312,C_313,D_315)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_10])).

tff(c_830,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_24,c_828])).

tff(c_834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_819,c_830])).

tff(c_835,plain,(
    ! [A_250] : ~ r2_hidden(A_250,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_630])).

tff(c_882,plain,(
    ! [A_342,D_343,C_341,A_344,B_340] :
      ( r2_hidden(k1_mcart_1(A_342),k3_zfmisc_1(A_344,B_340,C_341))
      | ~ r2_hidden(A_342,k4_zfmisc_1(A_344,B_340,C_341,D_343)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_12])).

tff(c_885,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_24,c_882])).

tff(c_615,plain,(
    ! [A_245,B_246,C_247] :
      ( r2_hidden(k1_mcart_1(A_245),B_246)
      | ~ r2_hidden(A_245,k2_zfmisc_1(B_246,C_247)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_617,plain,(
    ! [A_245,A_4,B_5,C_6] :
      ( r2_hidden(k1_mcart_1(A_245),k2_zfmisc_1(A_4,B_5))
      | ~ r2_hidden(A_245,k3_zfmisc_1(A_4,B_5,C_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_615])).

tff(c_890,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_885,c_617])).

tff(c_902,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))),'#skF_6') ),
    inference(resolution,[status(thm)],[c_890,c_10])).

tff(c_907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_835,c_902])).

tff(c_908,plain,(
    ! [A_250] : ~ r2_hidden(A_250,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_631])).

tff(c_614,plain,(
    r2_hidden(k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_908,c_614])).

tff(c_912,plain,(
    ! [A_250] : ~ r2_hidden(A_250,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_628])).

tff(c_917,plain,(
    ! [A_351,B_352,C_353,D_354] : k2_zfmisc_1(k3_zfmisc_1(A_351,B_352,C_353),D_354) = k4_zfmisc_1(A_351,B_352,C_353,D_354) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1004,plain,(
    ! [D_387,A_390,A_389,B_391,C_388] :
      ( r2_hidden(k1_mcart_1(A_389),k3_zfmisc_1(A_390,B_391,C_388))
      | ~ r2_hidden(A_389,k4_zfmisc_1(A_390,B_391,C_388,D_387)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_917,c_12])).

tff(c_1007,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_24,c_1004])).

tff(c_1011,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1007,c_44])).

tff(c_1016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_912,c_1011])).

tff(c_1017,plain,
    ( ~ r2_hidden(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_7')
    | ~ r2_hidden(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_1082,plain,(
    ~ r2_hidden(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1017])).

tff(c_1031,plain,(
    ! [A_394] :
      ( ~ v1_xboole_0('#skF_1')
      | ~ r2_hidden(A_394,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_1019])).

tff(c_1033,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1031])).

tff(c_1113,plain,(
    ! [C_423,D_421,B_424,A_425,E_422] :
      ( k11_mcart_1(A_425,B_424,C_423,D_421,E_422) = k2_mcart_1(E_422)
      | ~ m1_subset_1(E_422,k4_zfmisc_1(A_425,B_424,C_423,D_421))
      | k1_xboole_0 = D_421
      | k1_xboole_0 = C_423
      | k1_xboole_0 = B_424
      | k1_xboole_0 = A_425 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1117,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_1113])).

tff(c_1167,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1117])).

tff(c_1170,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1167,c_2])).

tff(c_1172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1033,c_1170])).

tff(c_1174,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1117])).

tff(c_1030,plain,(
    ! [A_394] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_394,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_1019])).

tff(c_1051,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1030])).

tff(c_1183,plain,(
    ! [D_441,C_443,E_442,B_444,A_445] :
      ( k8_mcart_1(A_445,B_444,C_443,D_441,E_442) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_442)))
      | ~ m1_subset_1(E_442,k4_zfmisc_1(A_445,B_444,C_443,D_441))
      | k1_xboole_0 = D_441
      | k1_xboole_0 = C_443
      | k1_xboole_0 = B_444
      | k1_xboole_0 = A_445 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1187,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_1183])).

tff(c_1190,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1174,c_1187])).

tff(c_1191,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1190])).

tff(c_1196,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1191,c_2])).

tff(c_1198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1051,c_1196])).

tff(c_1200,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1190])).

tff(c_1134,plain,(
    ! [D_431,E_432,B_434,C_433,A_435] :
      ( k2_mcart_1(k1_mcart_1(E_432)) = k10_mcart_1(A_435,B_434,C_433,D_431,E_432)
      | ~ m1_subset_1(E_432,k4_zfmisc_1(A_435,B_434,C_433,D_431))
      | k1_xboole_0 = D_431
      | k1_xboole_0 = C_433
      | k1_xboole_0 = B_434
      | k1_xboole_0 = A_435 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1138,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_1134])).

tff(c_1201,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1174,c_1200,c_1138])).

tff(c_1202,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1201])).

tff(c_1208,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1202,c_2])).

tff(c_1210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1032,c_1208])).

tff(c_1212,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1201])).

tff(c_1219,plain,(
    ! [B_449,E_447,A_450,C_448,D_446] :
      ( k9_mcart_1(A_450,B_449,C_448,D_446,E_447) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_447)))
      | ~ m1_subset_1(E_447,k4_zfmisc_1(A_450,B_449,C_448,D_446))
      | k1_xboole_0 = D_446
      | k1_xboole_0 = C_448
      | k1_xboole_0 = B_449
      | k1_xboole_0 = A_450 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1223,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_1219])).

tff(c_1226,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1174,c_1200,c_1212,c_1223])).

tff(c_1227,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1226])).

tff(c_1235,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1227,c_2])).

tff(c_1237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1050,c_1235])).

tff(c_1238,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(splitRight,[status(thm)],[c_1226])).

tff(c_1034,plain,(
    ! [A_395,B_396,C_397,D_398] : k2_zfmisc_1(k3_zfmisc_1(A_395,B_396,C_397),D_398) = k4_zfmisc_1(A_395,B_396,C_397,D_398) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1118,plain,(
    ! [A_427,A_426,B_429,C_428,D_430] :
      ( r2_hidden(k1_mcart_1(A_427),k3_zfmisc_1(A_426,B_429,C_428))
      | ~ r2_hidden(A_427,k4_zfmisc_1(A_426,B_429,C_428,D_430)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1034,c_12])).

tff(c_1121,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_24,c_1118])).

tff(c_1126,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1121,c_617])).

tff(c_1133,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1126,c_10])).

tff(c_1240,plain,(
    r2_hidden(k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1238,c_1133])).

tff(c_1242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1082,c_1240])).

tff(c_1243,plain,(
    ~ r2_hidden(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1017])).

tff(c_1279,plain,(
    ! [B_464,A_465,C_463,E_462,D_461] :
      ( k11_mcart_1(A_465,B_464,C_463,D_461,E_462) = k2_mcart_1(E_462)
      | ~ m1_subset_1(E_462,k4_zfmisc_1(A_465,B_464,C_463,D_461))
      | k1_xboole_0 = D_461
      | k1_xboole_0 = C_463
      | k1_xboole_0 = B_464
      | k1_xboole_0 = A_465 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1283,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_1279])).

tff(c_1296,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1283])).

tff(c_1298,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1296,c_2])).

tff(c_1300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1033,c_1298])).

tff(c_1302,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1283])).

tff(c_1304,plain,(
    ! [A_470,D_466,C_468,B_469,E_467] :
      ( k2_mcart_1(k1_mcart_1(E_467)) = k10_mcart_1(A_470,B_469,C_468,D_466,E_467)
      | ~ m1_subset_1(E_467,k4_zfmisc_1(A_470,B_469,C_468,D_466))
      | k1_xboole_0 = D_466
      | k1_xboole_0 = C_468
      | k1_xboole_0 = B_469
      | k1_xboole_0 = A_470 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1307,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_1304])).

tff(c_1310,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1302,c_1307])).

tff(c_1345,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1310])).

tff(c_1349,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1345,c_2])).

tff(c_1351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1051,c_1349])).

tff(c_1352,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(splitRight,[status(thm)],[c_1310])).

tff(c_1354,plain,(
    k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1352])).

tff(c_1275,plain,(
    ! [D_460,C_458,A_456,B_459,A_457] :
      ( r2_hidden(k1_mcart_1(A_457),k3_zfmisc_1(A_456,B_459,C_458))
      | ~ r2_hidden(A_457,k4_zfmisc_1(A_456,B_459,C_458,D_460)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1034,c_12])).

tff(c_1278,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_24,c_1275])).

tff(c_1289,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1278,c_44])).

tff(c_1355,plain,(
    r2_hidden(k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1354,c_1289])).

tff(c_1357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1243,c_1355])).

tff(c_1358,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1352])).

tff(c_1360,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1358])).

tff(c_1374,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_2])).

tff(c_1376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1032,c_1374])).

tff(c_1377,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1358])).

tff(c_1384,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1377,c_2])).

tff(c_1386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1050,c_1384])).

tff(c_1387,plain,(
    ! [A_394] : ~ r2_hidden(A_394,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1030])).

tff(c_1421,plain,(
    ! [D_503,C_501,A_500,A_499,B_502] :
      ( r2_hidden(k1_mcart_1(A_500),k3_zfmisc_1(A_499,B_502,C_501))
      | ~ r2_hidden(A_500,k4_zfmisc_1(A_499,B_502,C_501,D_503)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1034,c_12])).

tff(c_1424,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_24,c_1421])).

tff(c_1429,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1424,c_617])).

tff(c_1434,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1429,c_10])).

tff(c_1439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1387,c_1434])).

tff(c_1440,plain,(
    ! [A_394] : ~ r2_hidden(A_394,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_1029])).

tff(c_1018,plain,(
    r2_hidden(k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_1443,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1440,c_1018])).

tff(c_1444,plain,(
    ! [A_394] : ~ r2_hidden(A_394,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1031])).

tff(c_1463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1444,c_614])).

tff(c_1464,plain,(
    ! [A_394] : ~ r2_hidden(A_394,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1028])).

tff(c_1470,plain,(
    ! [A_509,B_510,C_511,D_512] : k2_zfmisc_1(k3_zfmisc_1(A_509,B_510,C_511),D_512) = k4_zfmisc_1(A_509,B_510,C_511,D_512) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1517,plain,(
    ! [C_532,A_533,A_530,B_534,D_531] :
      ( r2_hidden(k1_mcart_1(A_533),k3_zfmisc_1(A_530,B_534,C_532))
      | ~ r2_hidden(A_533,k4_zfmisc_1(A_530,B_534,C_532,D_531)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1470,c_12])).

tff(c_1520,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_24,c_1517])).

tff(c_1524,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1520,c_44])).

tff(c_1529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1464,c_1524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:03:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/1.72  
% 4.03/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/1.72  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 4.03/1.72  
% 4.03/1.72  %Foreground sorts:
% 4.03/1.72  
% 4.03/1.72  
% 4.03/1.72  %Background operators:
% 4.03/1.72  
% 4.03/1.72  
% 4.03/1.72  %Foreground operators:
% 4.03/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.03/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.03/1.72  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.03/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.03/1.72  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 4.03/1.72  tff('#skF_7', type, '#skF_7': $i).
% 4.03/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.03/1.72  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.03/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.03/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.03/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.03/1.72  tff('#skF_1', type, '#skF_1': $i).
% 4.03/1.72  tff('#skF_9', type, '#skF_9': $i).
% 4.03/1.72  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.03/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.03/1.72  tff('#skF_8', type, '#skF_8': $i).
% 4.03/1.72  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.03/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.03/1.72  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.03/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.03/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.03/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.03/1.72  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.03/1.72  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.03/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.03/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.03/1.72  
% 4.03/1.76  tff(f_93, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(A)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(B)) => (![G]: (m1_subset_1(G, k1_zfmisc_1(C)) => (![H]: (m1_subset_1(H, k1_zfmisc_1(D)) => (![I]: (m1_subset_1(I, k4_zfmisc_1(A, B, C, D)) => (r2_hidden(I, k4_zfmisc_1(E, F, G, H)) => (((r2_hidden(k8_mcart_1(A, B, C, D, I), E) & r2_hidden(k9_mcart_1(A, B, C, D, I), F)) & r2_hidden(k10_mcart_1(A, B, C, D, I), G)) & r2_hidden(k11_mcart_1(A, B, C, D, I), H))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_mcart_1)).
% 4.03/1.76  tff(f_33, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.03/1.76  tff(f_37, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 4.03/1.76  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.03/1.76  tff(f_68, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 4.03/1.76  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.03/1.76  tff(f_35, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.03/1.76  tff(c_28, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.03/1.76  tff(c_1019, plain, (![C_392, B_393, A_394]: (~v1_xboole_0(C_392) | ~m1_subset_1(B_393, k1_zfmisc_1(C_392)) | ~r2_hidden(A_394, B_393))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.03/1.76  tff(c_1029, plain, (![A_394]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_394, '#skF_8'))), inference(resolution, [status(thm)], [c_28, c_1019])).
% 4.03/1.76  tff(c_1050, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1029])).
% 4.03/1.76  tff(c_30, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.03/1.76  tff(c_1028, plain, (![A_394]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_394, '#skF_7'))), inference(resolution, [status(thm)], [c_30, c_1019])).
% 4.03/1.76  tff(c_1032, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1028])).
% 4.03/1.76  tff(c_619, plain, (![C_248, B_249, A_250]: (~v1_xboole_0(C_248) | ~m1_subset_1(B_249, k1_zfmisc_1(C_248)) | ~r2_hidden(A_250, B_249))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.03/1.76  tff(c_628, plain, (![A_250]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_250, '#skF_7'))), inference(resolution, [status(thm)], [c_30, c_619])).
% 4.03/1.76  tff(c_632, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_628])).
% 4.03/1.76  tff(c_629, plain, (![A_250]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_250, '#skF_8'))), inference(resolution, [status(thm)], [c_28, c_619])).
% 4.03/1.76  tff(c_651, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_629])).
% 4.03/1.76  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.03/1.76  tff(c_630, plain, (![A_250]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_250, '#skF_6'))), inference(resolution, [status(thm)], [c_32, c_619])).
% 4.03/1.76  tff(c_650, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_630])).
% 4.03/1.76  tff(c_24, plain, (r2_hidden('#skF_9', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.03/1.76  tff(c_634, plain, (![A_251, B_252, C_253, D_254]: (k2_zfmisc_1(k3_zfmisc_1(A_251, B_252, C_253), D_254)=k4_zfmisc_1(A_251, B_252, C_253, D_254))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.03/1.76  tff(c_10, plain, (![A_11, C_13, B_12]: (r2_hidden(k2_mcart_1(A_11), C_13) | ~r2_hidden(A_11, k2_zfmisc_1(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.03/1.76  tff(c_653, plain, (![A_263, B_259, A_261, C_260, D_262]: (r2_hidden(k2_mcart_1(A_261), D_262) | ~r2_hidden(A_261, k4_zfmisc_1(A_263, B_259, C_260, D_262)))), inference(superposition, [status(thm), theory('equality')], [c_634, c_10])).
% 4.03/1.76  tff(c_656, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_24, c_653])).
% 4.03/1.76  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.03/1.76  tff(c_631, plain, (![A_250]: (~v1_xboole_0('#skF_1') | ~r2_hidden(A_250, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_619])).
% 4.03/1.76  tff(c_633, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_631])).
% 4.03/1.76  tff(c_26, plain, (m1_subset_1('#skF_9', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.03/1.76  tff(c_678, plain, (![D_268, A_272, C_270, E_269, B_271]: (k11_mcart_1(A_272, B_271, C_270, D_268, E_269)=k2_mcart_1(E_269) | ~m1_subset_1(E_269, k4_zfmisc_1(A_272, B_271, C_270, D_268)) | k1_xboole_0=D_268 | k1_xboole_0=C_270 | k1_xboole_0=B_271 | k1_xboole_0=A_272)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.03/1.76  tff(c_682, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_678])).
% 4.03/1.76  tff(c_766, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_682])).
% 4.03/1.76  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.03/1.76  tff(c_769, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_766, c_2])).
% 4.03/1.76  tff(c_771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_633, c_769])).
% 4.03/1.76  tff(c_772, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitRight, [status(thm)], [c_682])).
% 4.03/1.76  tff(c_774, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitLeft, [status(thm)], [c_772])).
% 4.03/1.76  tff(c_22, plain, (~r2_hidden(k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_8') | ~r2_hidden(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_7') | ~r2_hidden(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_6') | ~r2_hidden(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.03/1.76  tff(c_53, plain, (~r2_hidden(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_5')), inference(splitLeft, [status(thm)], [c_22])).
% 4.03/1.76  tff(c_54, plain, (![C_52, B_53, A_54]: (~v1_xboole_0(C_52) | ~m1_subset_1(B_53, k1_zfmisc_1(C_52)) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.03/1.76  tff(c_64, plain, (![A_54]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_54, '#skF_8'))), inference(resolution, [status(thm)], [c_28, c_54])).
% 4.03/1.76  tff(c_73, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_64])).
% 4.03/1.76  tff(c_66, plain, (![A_54]: (~v1_xboole_0('#skF_1') | ~r2_hidden(A_54, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_54])).
% 4.03/1.76  tff(c_68, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_66])).
% 4.03/1.76  tff(c_95, plain, (![E_72, C_73, B_74, D_71, A_75]: (k11_mcart_1(A_75, B_74, C_73, D_71, E_72)=k2_mcart_1(E_72) | ~m1_subset_1(E_72, k4_zfmisc_1(A_75, B_74, C_73, D_71)) | k1_xboole_0=D_71 | k1_xboole_0=C_73 | k1_xboole_0=B_74 | k1_xboole_0=A_75)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.03/1.76  tff(c_99, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_95])).
% 4.03/1.76  tff(c_126, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_99])).
% 4.03/1.76  tff(c_128, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_2])).
% 4.03/1.76  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_128])).
% 4.03/1.76  tff(c_132, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_99])).
% 4.03/1.76  tff(c_65, plain, (![A_54]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_54, '#skF_6'))), inference(resolution, [status(thm)], [c_32, c_54])).
% 4.03/1.76  tff(c_72, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_65])).
% 4.03/1.76  tff(c_172, plain, (![A_98, C_96, E_95, D_94, B_97]: (k2_mcart_1(k1_mcart_1(E_95))=k10_mcart_1(A_98, B_97, C_96, D_94, E_95) | ~m1_subset_1(E_95, k4_zfmisc_1(A_98, B_97, C_96, D_94)) | k1_xboole_0=D_94 | k1_xboole_0=C_96 | k1_xboole_0=B_97 | k1_xboole_0=A_98)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.03/1.76  tff(c_175, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_172])).
% 4.03/1.76  tff(c_178, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_132, c_175])).
% 4.03/1.76  tff(c_227, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_178])).
% 4.03/1.76  tff(c_232, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_2])).
% 4.03/1.76  tff(c_234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_232])).
% 4.03/1.76  tff(c_236, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_178])).
% 4.03/1.76  tff(c_63, plain, (![A_54]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_54, '#skF_7'))), inference(resolution, [status(thm)], [c_30, c_54])).
% 4.03/1.76  tff(c_67, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_63])).
% 4.03/1.76  tff(c_219, plain, (![A_108, D_104, B_107, E_105, C_106]: (k9_mcart_1(A_108, B_107, C_106, D_104, E_105)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_105))) | ~m1_subset_1(E_105, k4_zfmisc_1(A_108, B_107, C_106, D_104)) | k1_xboole_0=D_104 | k1_xboole_0=C_106 | k1_xboole_0=B_107 | k1_xboole_0=A_108)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.03/1.76  tff(c_223, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_219])).
% 4.03/1.76  tff(c_226, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_132, c_223])).
% 4.03/1.76  tff(c_237, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_236, c_226])).
% 4.03/1.76  tff(c_238, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_237])).
% 4.03/1.76  tff(c_244, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_238, c_2])).
% 4.03/1.76  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_244])).
% 4.03/1.76  tff(c_248, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_237])).
% 4.03/1.76  tff(c_255, plain, (![A_113, D_109, C_111, E_110, B_112]: (k8_mcart_1(A_113, B_112, C_111, D_109, E_110)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_110))) | ~m1_subset_1(E_110, k4_zfmisc_1(A_113, B_112, C_111, D_109)) | k1_xboole_0=D_109 | k1_xboole_0=C_111 | k1_xboole_0=B_112 | k1_xboole_0=A_113)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.03/1.76  tff(c_259, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_255])).
% 4.03/1.76  tff(c_262, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_132, c_236, c_248, c_259])).
% 4.03/1.76  tff(c_263, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_262])).
% 4.03/1.76  tff(c_271, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_2])).
% 4.03/1.76  tff(c_273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_271])).
% 4.03/1.76  tff(c_274, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(splitRight, [status(thm)], [c_262])).
% 4.03/1.76  tff(c_75, plain, (![A_62, B_63, C_64, D_65]: (k2_zfmisc_1(k3_zfmisc_1(A_62, B_63, C_64), D_65)=k4_zfmisc_1(A_62, B_63, C_64, D_65))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.03/1.76  tff(c_12, plain, (![A_11, B_12, C_13]: (r2_hidden(k1_mcart_1(A_11), B_12) | ~r2_hidden(A_11, k2_zfmisc_1(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.03/1.76  tff(c_162, plain, (![C_89, B_92, A_91, D_93, A_90]: (r2_hidden(k1_mcart_1(A_91), k3_zfmisc_1(A_90, B_92, C_89)) | ~r2_hidden(A_91, k4_zfmisc_1(A_90, B_92, C_89, D_93)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_12])).
% 4.03/1.76  tff(c_165, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_24, c_162])).
% 4.03/1.76  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_zfmisc_1(k2_zfmisc_1(A_4, B_5), C_6)=k3_zfmisc_1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.03/1.76  tff(c_69, plain, (![A_55, B_56, C_57]: (r2_hidden(k1_mcart_1(A_55), B_56) | ~r2_hidden(A_55, k2_zfmisc_1(B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.03/1.76  tff(c_71, plain, (![A_55, A_4, B_5, C_6]: (r2_hidden(k1_mcart_1(A_55), k2_zfmisc_1(A_4, B_5)) | ~r2_hidden(A_55, k3_zfmisc_1(A_4, B_5, C_6)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_69])).
% 4.03/1.76  tff(c_170, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_165, c_71])).
% 4.03/1.76  tff(c_183, plain, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))), '#skF_5')), inference(resolution, [status(thm)], [c_170, c_12])).
% 4.03/1.76  tff(c_276, plain, (r2_hidden(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_183])).
% 4.03/1.76  tff(c_278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_276])).
% 4.03/1.76  tff(c_279, plain, (![A_54]: (~r2_hidden(A_54, '#skF_8'))), inference(splitRight, [status(thm)], [c_64])).
% 4.03/1.76  tff(c_283, plain, (![A_119, B_120, C_121, D_122]: (k2_zfmisc_1(k3_zfmisc_1(A_119, B_120, C_121), D_122)=k4_zfmisc_1(A_119, B_120, C_121, D_122))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.03/1.76  tff(c_299, plain, (![A_124, D_126, C_127, A_125, B_123]: (r2_hidden(k2_mcart_1(A_125), D_126) | ~r2_hidden(A_125, k4_zfmisc_1(A_124, B_123, C_127, D_126)))), inference(superposition, [status(thm), theory('equality')], [c_283, c_10])).
% 4.03/1.76  tff(c_301, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_24, c_299])).
% 4.03/1.76  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_279, c_301])).
% 4.03/1.76  tff(c_306, plain, (![A_54]: (~r2_hidden(A_54, '#skF_6'))), inference(splitRight, [status(thm)], [c_65])).
% 4.03/1.76  tff(c_308, plain, (![A_128, B_129, C_130, D_131]: (k2_zfmisc_1(k3_zfmisc_1(A_128, B_129, C_130), D_131)=k4_zfmisc_1(A_128, B_129, C_130, D_131))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.03/1.76  tff(c_391, plain, (![C_161, A_160, A_164, D_163, B_162]: (r2_hidden(k1_mcart_1(A_164), k3_zfmisc_1(A_160, B_162, C_161)) | ~r2_hidden(A_164, k4_zfmisc_1(A_160, B_162, C_161, D_163)))), inference(superposition, [status(thm), theory('equality')], [c_308, c_12])).
% 4.03/1.76  tff(c_394, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_24, c_391])).
% 4.03/1.76  tff(c_399, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_394, c_71])).
% 4.03/1.76  tff(c_404, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))), '#skF_6')), inference(resolution, [status(thm)], [c_399, c_10])).
% 4.03/1.76  tff(c_409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_306, c_404])).
% 4.03/1.76  tff(c_410, plain, (![A_54]: (~r2_hidden(A_54, '#skF_5'))), inference(splitRight, [status(thm)], [c_66])).
% 4.03/1.76  tff(c_418, plain, (![A_169, B_170, C_171, D_172]: (k2_zfmisc_1(k3_zfmisc_1(A_169, B_170, C_171), D_172)=k4_zfmisc_1(A_169, B_170, C_171, D_172))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.03/1.76  tff(c_470, plain, (![A_195, D_196, C_199, A_198, B_197]: (r2_hidden(k1_mcart_1(A_198), k3_zfmisc_1(A_195, B_197, C_199)) | ~r2_hidden(A_198, k4_zfmisc_1(A_195, B_197, C_199, D_196)))), inference(superposition, [status(thm), theory('equality')], [c_418, c_12])).
% 4.03/1.76  tff(c_473, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_24, c_470])).
% 4.03/1.76  tff(c_414, plain, (![A_166, B_167, C_168]: (r2_hidden(k1_mcart_1(A_166), B_167) | ~r2_hidden(A_166, k2_zfmisc_1(B_167, C_168)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.03/1.76  tff(c_416, plain, (![A_166, A_4, B_5, C_6]: (r2_hidden(k1_mcart_1(A_166), k2_zfmisc_1(A_4, B_5)) | ~r2_hidden(A_166, k3_zfmisc_1(A_4, B_5, C_6)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_414])).
% 4.03/1.76  tff(c_478, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_473, c_416])).
% 4.03/1.76  tff(c_489, plain, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))), '#skF_5')), inference(resolution, [status(thm)], [c_478, c_12])).
% 4.03/1.76  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_410, c_489])).
% 4.03/1.76  tff(c_496, plain, (![A_54]: (~r2_hidden(A_54, '#skF_7'))), inference(splitRight, [status(thm)], [c_63])).
% 4.03/1.76  tff(c_506, plain, (![A_208, B_209, C_210, D_211]: (k2_zfmisc_1(k3_zfmisc_1(A_208, B_209, C_210), D_211)=k4_zfmisc_1(A_208, B_209, C_210, D_211))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.03/1.76  tff(c_593, plain, (![A_235, D_239, B_238, C_236, A_237]: (r2_hidden(k1_mcart_1(A_237), k3_zfmisc_1(A_235, B_238, C_236)) | ~r2_hidden(A_237, k4_zfmisc_1(A_235, B_238, C_236, D_239)))), inference(superposition, [status(thm), theory('equality')], [c_506, c_12])).
% 4.03/1.76  tff(c_596, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_24, c_593])).
% 4.03/1.76  tff(c_36, plain, (![A_49, B_50, C_51]: (k2_zfmisc_1(k2_zfmisc_1(A_49, B_50), C_51)=k3_zfmisc_1(A_49, B_50, C_51))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.03/1.76  tff(c_44, plain, (![A_11, C_51, A_49, B_50]: (r2_hidden(k2_mcart_1(A_11), C_51) | ~r2_hidden(A_11, k3_zfmisc_1(A_49, B_50, C_51)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_10])).
% 4.03/1.76  tff(c_607, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_596, c_44])).
% 4.03/1.76  tff(c_612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_496, c_607])).
% 4.03/1.76  tff(c_613, plain, (~r2_hidden(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_6') | ~r2_hidden(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_7') | ~r2_hidden(k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_22])).
% 4.03/1.76  tff(c_618, plain, (~r2_hidden(k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_613])).
% 4.03/1.76  tff(c_775, plain, (~r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_774, c_618])).
% 4.03/1.76  tff(c_778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_656, c_775])).
% 4.03/1.76  tff(c_779, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_772])).
% 4.03/1.76  tff(c_781, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_779])).
% 4.03/1.76  tff(c_794, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_781, c_2])).
% 4.03/1.76  tff(c_796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_650, c_794])).
% 4.03/1.76  tff(c_797, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_779])).
% 4.03/1.76  tff(c_799, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_797])).
% 4.03/1.76  tff(c_806, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_799, c_2])).
% 4.03/1.76  tff(c_808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_651, c_806])).
% 4.03/1.76  tff(c_809, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_797])).
% 4.03/1.76  tff(c_816, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_809, c_2])).
% 4.03/1.76  tff(c_818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_632, c_816])).
% 4.03/1.76  tff(c_819, plain, (![A_250]: (~r2_hidden(A_250, '#skF_8'))), inference(splitRight, [status(thm)], [c_629])).
% 4.03/1.76  tff(c_828, plain, (![A_314, B_312, D_315, C_313, A_316]: (r2_hidden(k2_mcart_1(A_314), D_315) | ~r2_hidden(A_314, k4_zfmisc_1(A_316, B_312, C_313, D_315)))), inference(superposition, [status(thm), theory('equality')], [c_634, c_10])).
% 4.03/1.76  tff(c_830, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_24, c_828])).
% 4.03/1.76  tff(c_834, plain, $false, inference(negUnitSimplification, [status(thm)], [c_819, c_830])).
% 4.03/1.76  tff(c_835, plain, (![A_250]: (~r2_hidden(A_250, '#skF_6'))), inference(splitRight, [status(thm)], [c_630])).
% 4.03/1.76  tff(c_882, plain, (![A_342, D_343, C_341, A_344, B_340]: (r2_hidden(k1_mcart_1(A_342), k3_zfmisc_1(A_344, B_340, C_341)) | ~r2_hidden(A_342, k4_zfmisc_1(A_344, B_340, C_341, D_343)))), inference(superposition, [status(thm), theory('equality')], [c_634, c_12])).
% 4.03/1.76  tff(c_885, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_24, c_882])).
% 4.03/1.76  tff(c_615, plain, (![A_245, B_246, C_247]: (r2_hidden(k1_mcart_1(A_245), B_246) | ~r2_hidden(A_245, k2_zfmisc_1(B_246, C_247)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.03/1.76  tff(c_617, plain, (![A_245, A_4, B_5, C_6]: (r2_hidden(k1_mcart_1(A_245), k2_zfmisc_1(A_4, B_5)) | ~r2_hidden(A_245, k3_zfmisc_1(A_4, B_5, C_6)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_615])).
% 4.03/1.76  tff(c_890, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_885, c_617])).
% 4.03/1.76  tff(c_902, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))), '#skF_6')), inference(resolution, [status(thm)], [c_890, c_10])).
% 4.03/1.76  tff(c_907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_835, c_902])).
% 4.03/1.76  tff(c_908, plain, (![A_250]: (~r2_hidden(A_250, '#skF_5'))), inference(splitRight, [status(thm)], [c_631])).
% 4.03/1.76  tff(c_614, plain, (r2_hidden(k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_5')), inference(splitRight, [status(thm)], [c_22])).
% 4.03/1.76  tff(c_911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_908, c_614])).
% 4.03/1.76  tff(c_912, plain, (![A_250]: (~r2_hidden(A_250, '#skF_7'))), inference(splitRight, [status(thm)], [c_628])).
% 4.03/1.76  tff(c_917, plain, (![A_351, B_352, C_353, D_354]: (k2_zfmisc_1(k3_zfmisc_1(A_351, B_352, C_353), D_354)=k4_zfmisc_1(A_351, B_352, C_353, D_354))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.03/1.76  tff(c_1004, plain, (![D_387, A_390, A_389, B_391, C_388]: (r2_hidden(k1_mcart_1(A_389), k3_zfmisc_1(A_390, B_391, C_388)) | ~r2_hidden(A_389, k4_zfmisc_1(A_390, B_391, C_388, D_387)))), inference(superposition, [status(thm), theory('equality')], [c_917, c_12])).
% 4.03/1.76  tff(c_1007, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_24, c_1004])).
% 4.03/1.76  tff(c_1011, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_1007, c_44])).
% 4.03/1.76  tff(c_1016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_912, c_1011])).
% 4.03/1.76  tff(c_1017, plain, (~r2_hidden(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_7') | ~r2_hidden(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_613])).
% 4.03/1.76  tff(c_1082, plain, (~r2_hidden(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_6')), inference(splitLeft, [status(thm)], [c_1017])).
% 4.03/1.76  tff(c_1031, plain, (![A_394]: (~v1_xboole_0('#skF_1') | ~r2_hidden(A_394, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_1019])).
% 4.03/1.76  tff(c_1033, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_1031])).
% 4.03/1.76  tff(c_1113, plain, (![C_423, D_421, B_424, A_425, E_422]: (k11_mcart_1(A_425, B_424, C_423, D_421, E_422)=k2_mcart_1(E_422) | ~m1_subset_1(E_422, k4_zfmisc_1(A_425, B_424, C_423, D_421)) | k1_xboole_0=D_421 | k1_xboole_0=C_423 | k1_xboole_0=B_424 | k1_xboole_0=A_425)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.03/1.76  tff(c_1117, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_1113])).
% 4.03/1.76  tff(c_1167, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1117])).
% 4.03/1.76  tff(c_1170, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1167, c_2])).
% 4.03/1.76  tff(c_1172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1033, c_1170])).
% 4.03/1.76  tff(c_1174, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_1117])).
% 4.03/1.76  tff(c_1030, plain, (![A_394]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_394, '#skF_6'))), inference(resolution, [status(thm)], [c_32, c_1019])).
% 4.03/1.76  tff(c_1051, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1030])).
% 4.03/1.76  tff(c_1183, plain, (![D_441, C_443, E_442, B_444, A_445]: (k8_mcart_1(A_445, B_444, C_443, D_441, E_442)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_442))) | ~m1_subset_1(E_442, k4_zfmisc_1(A_445, B_444, C_443, D_441)) | k1_xboole_0=D_441 | k1_xboole_0=C_443 | k1_xboole_0=B_444 | k1_xboole_0=A_445)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.03/1.76  tff(c_1187, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_1183])).
% 4.03/1.76  tff(c_1190, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1174, c_1187])).
% 4.03/1.76  tff(c_1191, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1190])).
% 4.03/1.76  tff(c_1196, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1191, c_2])).
% 4.03/1.76  tff(c_1198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1051, c_1196])).
% 4.03/1.76  tff(c_1200, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1190])).
% 4.03/1.76  tff(c_1134, plain, (![D_431, E_432, B_434, C_433, A_435]: (k2_mcart_1(k1_mcart_1(E_432))=k10_mcart_1(A_435, B_434, C_433, D_431, E_432) | ~m1_subset_1(E_432, k4_zfmisc_1(A_435, B_434, C_433, D_431)) | k1_xboole_0=D_431 | k1_xboole_0=C_433 | k1_xboole_0=B_434 | k1_xboole_0=A_435)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.03/1.76  tff(c_1138, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_1134])).
% 4.03/1.76  tff(c_1201, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1174, c_1200, c_1138])).
% 4.03/1.76  tff(c_1202, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1201])).
% 4.03/1.76  tff(c_1208, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1202, c_2])).
% 4.03/1.76  tff(c_1210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1032, c_1208])).
% 4.03/1.76  tff(c_1212, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1201])).
% 4.03/1.76  tff(c_1219, plain, (![B_449, E_447, A_450, C_448, D_446]: (k9_mcart_1(A_450, B_449, C_448, D_446, E_447)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_447))) | ~m1_subset_1(E_447, k4_zfmisc_1(A_450, B_449, C_448, D_446)) | k1_xboole_0=D_446 | k1_xboole_0=C_448 | k1_xboole_0=B_449 | k1_xboole_0=A_450)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.03/1.76  tff(c_1223, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_1219])).
% 4.03/1.76  tff(c_1226, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1174, c_1200, c_1212, c_1223])).
% 4.03/1.76  tff(c_1227, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1226])).
% 4.03/1.76  tff(c_1235, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1227, c_2])).
% 4.03/1.76  tff(c_1237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1050, c_1235])).
% 4.03/1.76  tff(c_1238, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(splitRight, [status(thm)], [c_1226])).
% 4.03/1.76  tff(c_1034, plain, (![A_395, B_396, C_397, D_398]: (k2_zfmisc_1(k3_zfmisc_1(A_395, B_396, C_397), D_398)=k4_zfmisc_1(A_395, B_396, C_397, D_398))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.03/1.76  tff(c_1118, plain, (![A_427, A_426, B_429, C_428, D_430]: (r2_hidden(k1_mcart_1(A_427), k3_zfmisc_1(A_426, B_429, C_428)) | ~r2_hidden(A_427, k4_zfmisc_1(A_426, B_429, C_428, D_430)))), inference(superposition, [status(thm), theory('equality')], [c_1034, c_12])).
% 4.03/1.76  tff(c_1121, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_24, c_1118])).
% 4.03/1.76  tff(c_1126, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1121, c_617])).
% 4.03/1.76  tff(c_1133, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))), '#skF_6')), inference(resolution, [status(thm)], [c_1126, c_10])).
% 4.03/1.76  tff(c_1240, plain, (r2_hidden(k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1238, c_1133])).
% 4.03/1.76  tff(c_1242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1082, c_1240])).
% 4.03/1.76  tff(c_1243, plain, (~r2_hidden(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_7')), inference(splitRight, [status(thm)], [c_1017])).
% 4.03/1.76  tff(c_1279, plain, (![B_464, A_465, C_463, E_462, D_461]: (k11_mcart_1(A_465, B_464, C_463, D_461, E_462)=k2_mcart_1(E_462) | ~m1_subset_1(E_462, k4_zfmisc_1(A_465, B_464, C_463, D_461)) | k1_xboole_0=D_461 | k1_xboole_0=C_463 | k1_xboole_0=B_464 | k1_xboole_0=A_465)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.03/1.76  tff(c_1283, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_1279])).
% 4.03/1.76  tff(c_1296, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_1283])).
% 4.03/1.76  tff(c_1298, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1296, c_2])).
% 4.03/1.76  tff(c_1300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1033, c_1298])).
% 4.03/1.76  tff(c_1302, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_1283])).
% 4.03/1.76  tff(c_1304, plain, (![A_470, D_466, C_468, B_469, E_467]: (k2_mcart_1(k1_mcart_1(E_467))=k10_mcart_1(A_470, B_469, C_468, D_466, E_467) | ~m1_subset_1(E_467, k4_zfmisc_1(A_470, B_469, C_468, D_466)) | k1_xboole_0=D_466 | k1_xboole_0=C_468 | k1_xboole_0=B_469 | k1_xboole_0=A_470)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.03/1.76  tff(c_1307, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_26, c_1304])).
% 4.03/1.76  tff(c_1310, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1302, c_1307])).
% 4.03/1.76  tff(c_1345, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1310])).
% 4.03/1.76  tff(c_1349, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1345, c_2])).
% 4.03/1.76  tff(c_1351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1051, c_1349])).
% 4.03/1.76  tff(c_1352, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(splitRight, [status(thm)], [c_1310])).
% 4.03/1.76  tff(c_1354, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(splitLeft, [status(thm)], [c_1352])).
% 4.03/1.76  tff(c_1275, plain, (![D_460, C_458, A_456, B_459, A_457]: (r2_hidden(k1_mcart_1(A_457), k3_zfmisc_1(A_456, B_459, C_458)) | ~r2_hidden(A_457, k4_zfmisc_1(A_456, B_459, C_458, D_460)))), inference(superposition, [status(thm), theory('equality')], [c_1034, c_12])).
% 4.03/1.76  tff(c_1278, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_24, c_1275])).
% 4.03/1.76  tff(c_1289, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_1278, c_44])).
% 4.03/1.76  tff(c_1355, plain, (r2_hidden(k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1354, c_1289])).
% 4.03/1.76  tff(c_1357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1243, c_1355])).
% 4.03/1.76  tff(c_1358, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1352])).
% 4.03/1.76  tff(c_1360, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1358])).
% 4.03/1.76  tff(c_1374, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_2])).
% 4.03/1.76  tff(c_1376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1032, c_1374])).
% 4.03/1.76  tff(c_1377, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1358])).
% 4.03/1.76  tff(c_1384, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1377, c_2])).
% 4.03/1.76  tff(c_1386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1050, c_1384])).
% 4.03/1.76  tff(c_1387, plain, (![A_394]: (~r2_hidden(A_394, '#skF_6'))), inference(splitRight, [status(thm)], [c_1030])).
% 4.03/1.76  tff(c_1421, plain, (![D_503, C_501, A_500, A_499, B_502]: (r2_hidden(k1_mcart_1(A_500), k3_zfmisc_1(A_499, B_502, C_501)) | ~r2_hidden(A_500, k4_zfmisc_1(A_499, B_502, C_501, D_503)))), inference(superposition, [status(thm), theory('equality')], [c_1034, c_12])).
% 4.03/1.76  tff(c_1424, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_24, c_1421])).
% 4.03/1.76  tff(c_1429, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1424, c_617])).
% 4.03/1.76  tff(c_1434, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))), '#skF_6')), inference(resolution, [status(thm)], [c_1429, c_10])).
% 4.03/1.76  tff(c_1439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1387, c_1434])).
% 4.03/1.76  tff(c_1440, plain, (![A_394]: (~r2_hidden(A_394, '#skF_8'))), inference(splitRight, [status(thm)], [c_1029])).
% 4.03/1.76  tff(c_1018, plain, (r2_hidden(k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_613])).
% 4.03/1.76  tff(c_1443, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1440, c_1018])).
% 4.03/1.76  tff(c_1444, plain, (![A_394]: (~r2_hidden(A_394, '#skF_5'))), inference(splitRight, [status(thm)], [c_1031])).
% 4.03/1.76  tff(c_1463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1444, c_614])).
% 4.03/1.76  tff(c_1464, plain, (![A_394]: (~r2_hidden(A_394, '#skF_7'))), inference(splitRight, [status(thm)], [c_1028])).
% 4.03/1.76  tff(c_1470, plain, (![A_509, B_510, C_511, D_512]: (k2_zfmisc_1(k3_zfmisc_1(A_509, B_510, C_511), D_512)=k4_zfmisc_1(A_509, B_510, C_511, D_512))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.03/1.76  tff(c_1517, plain, (![C_532, A_533, A_530, B_534, D_531]: (r2_hidden(k1_mcart_1(A_533), k3_zfmisc_1(A_530, B_534, C_532)) | ~r2_hidden(A_533, k4_zfmisc_1(A_530, B_534, C_532, D_531)))), inference(superposition, [status(thm), theory('equality')], [c_1470, c_12])).
% 4.03/1.76  tff(c_1520, plain, (r2_hidden(k1_mcart_1('#skF_9'), k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_24, c_1517])).
% 4.03/1.76  tff(c_1524, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_1520, c_44])).
% 4.03/1.76  tff(c_1529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1464, c_1524])).
% 4.03/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.03/1.76  
% 4.03/1.76  Inference rules
% 4.03/1.76  ----------------------
% 4.03/1.76  #Ref     : 0
% 4.03/1.76  #Sup     : 331
% 4.03/1.76  #Fact    : 0
% 4.03/1.76  #Define  : 0
% 4.03/1.76  #Split   : 53
% 4.03/1.76  #Chain   : 0
% 4.03/1.76  #Close   : 0
% 4.03/1.76  
% 4.03/1.76  Ordering : KBO
% 4.03/1.76  
% 4.03/1.76  Simplification rules
% 4.03/1.76  ----------------------
% 4.03/1.76  #Subsume      : 40
% 4.03/1.76  #Demod        : 316
% 4.03/1.76  #Tautology    : 93
% 4.03/1.76  #SimpNegUnit  : 46
% 4.03/1.76  #BackRed      : 97
% 4.03/1.76  
% 4.03/1.76  #Partial instantiations: 0
% 4.03/1.76  #Strategies tried      : 1
% 4.03/1.76  
% 4.03/1.76  Timing (in seconds)
% 4.03/1.76  ----------------------
% 4.03/1.76  Preprocessing        : 0.34
% 4.03/1.76  Parsing              : 0.18
% 4.03/1.76  CNF conversion       : 0.03
% 4.03/1.76  Main loop            : 0.60
% 4.03/1.76  Inferencing          : 0.23
% 4.03/1.76  Reduction            : 0.19
% 4.03/1.76  Demodulation         : 0.13
% 4.03/1.76  BG Simplification    : 0.04
% 4.03/1.76  Subsumption          : 0.07
% 4.03/1.76  Abstraction          : 0.04
% 4.03/1.76  MUC search           : 0.00
% 4.03/1.76  Cooper               : 0.00
% 4.03/1.76  Total                : 1.02
% 4.03/1.76  Index Insertion      : 0.00
% 4.03/1.76  Index Deletion       : 0.00
% 4.03/1.76  Index Matching       : 0.00
% 4.03/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
