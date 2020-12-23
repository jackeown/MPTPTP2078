%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:24 EST 2020

% Result     : Theorem 7.02s
% Output     : CNFRefutation 7.39s
% Verified   : 
% Statistics : Number of formulae       :  277 (1212 expanded)
%              Number of leaves         :   38 ( 397 expanded)
%              Depth                    :   12
%              Number of atoms          :  480 (4203 expanded)
%              Number of equality atoms :  208 (1712 expanded)
%              Maximal formula depth    :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_103,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

tff(f_78,axiom,(
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

tff(f_47,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_57,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_70,plain,(
    r1_tarski('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_57])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2965,plain,(
    ! [C_537,B_538,A_539] :
      ( r2_hidden(C_537,B_538)
      | ~ r2_hidden(C_537,A_539)
      | ~ r1_tarski(A_539,B_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3005,plain,(
    ! [A_547,B_548] :
      ( r2_hidden('#skF_1'(A_547),B_548)
      | ~ r1_tarski(A_547,B_548)
      | v1_xboole_0(A_547) ) ),
    inference(resolution,[status(thm)],[c_4,c_2965])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3021,plain,(
    ! [B_549,A_550] :
      ( ~ v1_xboole_0(B_549)
      | ~ r1_tarski(A_550,B_549)
      | v1_xboole_0(A_550) ) ),
    inference(resolution,[status(thm)],[c_3005,c_2])).

tff(c_3047,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_3021])).

tff(c_3061,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3047])).

tff(c_40,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_71,plain,(
    r1_tarski('#skF_10','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_3042,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_71,c_3021])).

tff(c_3060,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3042])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_72,plain,(
    r1_tarski('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_57])).

tff(c_3046,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_3021])).

tff(c_3062,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3046])).

tff(c_34,plain,
    ( ~ r2_hidden(k11_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_10')
    | ~ r2_hidden(k10_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_9')
    | ~ r2_hidden(k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_8')
    | ~ r2_hidden(k8_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_91,plain,(
    ~ r2_hidden(k8_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_102,plain,(
    ! [C_71,B_72,A_73] :
      ( r2_hidden(C_71,B_72)
      | ~ r2_hidden(C_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_140,plain,(
    ! [A_80,B_81] :
      ( r2_hidden('#skF_1'(A_80),B_81)
      | ~ r1_tarski(A_80,B_81)
      | v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_156,plain,(
    ! [B_82,A_83] :
      ( ~ v1_xboole_0(B_82)
      | ~ r1_tarski(A_83,B_82)
      | v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_177,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_71,c_156])).

tff(c_181,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_179,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_156])).

tff(c_212,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_73,plain,(
    r1_tarski('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_57])).

tff(c_178,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_73,c_156])).

tff(c_194,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_38,plain,(
    m1_subset_1('#skF_11',k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_226,plain,(
    ! [E_94,D_96,C_95,B_97,A_93] :
      ( k11_mcart_1(A_93,B_97,C_95,D_96,E_94) = k2_mcart_1(E_94)
      | ~ m1_subset_1(E_94,k4_zfmisc_1(A_93,B_97,C_95,D_96))
      | k1_xboole_0 = D_96
      | k1_xboole_0 = C_95
      | k1_xboole_0 = B_97
      | k1_xboole_0 = A_93 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_230,plain,
    ( k11_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11') = k2_mcart_1('#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_226])).

tff(c_337,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_340,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_12])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_194,c_340])).

tff(c_344,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_293,plain,(
    ! [D_108,A_105,E_106,B_109,C_107] :
      ( k2_mcart_1(k1_mcart_1(E_106)) = k10_mcart_1(A_105,B_109,C_107,D_108,E_106)
      | ~ m1_subset_1(E_106,k4_zfmisc_1(A_105,B_109,C_107,D_108))
      | k1_xboole_0 = D_108
      | k1_xboole_0 = C_107
      | k1_xboole_0 = B_109
      | k1_xboole_0 = A_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_297,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_11')) = k10_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_293])).

tff(c_369,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_11')) = k10_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_297])).

tff(c_370,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_375,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_12])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_375])).

tff(c_379,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_180,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_156])).

tff(c_195,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_419,plain,(
    ! [C_125,D_126,A_123,E_124,B_127] :
      ( k9_mcart_1(A_123,B_127,C_125,D_126,E_124) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_124)))
      | ~ m1_subset_1(E_124,k4_zfmisc_1(A_123,B_127,C_125,D_126))
      | k1_xboole_0 = D_126
      | k1_xboole_0 = C_125
      | k1_xboole_0 = B_127
      | k1_xboole_0 = A_123 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_421,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_419])).

tff(c_424,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_379,c_421])).

tff(c_667,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_424])).

tff(c_674,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_667,c_12])).

tff(c_676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_674])).

tff(c_678,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_357,plain,(
    ! [A_116,D_119,E_117,B_120,C_118] :
      ( k8_mcart_1(A_116,B_120,C_118,D_119,E_117) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_117)))
      | ~ m1_subset_1(E_117,k4_zfmisc_1(A_116,B_120,C_118,D_119))
      | k1_xboole_0 = D_119
      | k1_xboole_0 = C_118
      | k1_xboole_0 = B_120
      | k1_xboole_0 = A_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_359,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k8_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_357])).

tff(c_362,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k8_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_359])).

tff(c_725,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k8_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_379,c_678,c_362])).

tff(c_726,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_725])).

tff(c_734,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_726,c_12])).

tff(c_736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_734])).

tff(c_737,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k8_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11') ),
    inference(splitRight,[status(thm)],[c_725])).

tff(c_36,plain,(
    r2_hidden('#skF_11',k4_zfmisc_1('#skF_7','#skF_8','#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_196,plain,(
    ! [A_85,B_86,C_87,D_88] : k2_zfmisc_1(k3_zfmisc_1(A_85,B_86,C_87),D_88) = k4_zfmisc_1(A_85,B_86,C_87,D_88) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_hidden(k1_mcart_1(A_19),B_20)
      | ~ r2_hidden(A_19,k2_zfmisc_1(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1259,plain,(
    ! [B_250,A_251,A_253,C_254,D_252] :
      ( r2_hidden(k1_mcart_1(A_251),k3_zfmisc_1(A_253,B_250,C_254))
      | ~ r2_hidden(A_251,k4_zfmisc_1(A_253,B_250,C_254,D_252)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_24])).

tff(c_1313,plain,(
    r2_hidden(k1_mcart_1('#skF_11'),k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_36,c_1259])).

tff(c_121,plain,(
    ! [A_77,B_78,C_79] : k2_zfmisc_1(k2_zfmisc_1(A_77,B_78),C_79) = k3_zfmisc_1(A_77,B_78,C_79) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_131,plain,(
    ! [A_19,A_77,B_78,C_79] :
      ( r2_hidden(k1_mcart_1(A_19),k2_zfmisc_1(A_77,B_78))
      | ~ r2_hidden(A_19,k3_zfmisc_1(A_77,B_78,C_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_24])).

tff(c_1324,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_11')),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_1313,c_131])).

tff(c_1334,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1324,c_24])).

tff(c_1342,plain,(
    r2_hidden(k8_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_1334])).

tff(c_1344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_1342])).

tff(c_1345,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_112,plain,(
    ! [A_74,C_75,B_76] :
      ( r2_hidden(k2_mcart_1(A_74),C_75)
      | ~ r2_hidden(A_74,k2_zfmisc_1(B_76,C_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1607,plain,(
    ! [B_300,C_301] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_300,C_301))),C_301)
      | v1_xboole_0(k2_zfmisc_1(B_300,C_301)) ) ),
    inference(resolution,[status(thm)],[c_4,c_112])).

tff(c_1636,plain,(
    ! [C_301,B_300] :
      ( ~ v1_xboole_0(C_301)
      | v1_xboole_0(k2_zfmisc_1(B_300,C_301)) ) ),
    inference(resolution,[status(thm)],[c_1607,c_2])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14] : k2_zfmisc_1(k2_zfmisc_1(A_12,B_13),C_14) = k3_zfmisc_1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_93,plain,(
    ! [A_68,B_69,C_70] :
      ( r2_hidden(k1_mcart_1(A_68),B_69)
      | ~ r2_hidden(A_68,k2_zfmisc_1(B_69,C_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1664,plain,(
    ! [B_311,C_312] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_311,C_312))),B_311)
      | v1_xboole_0(k2_zfmisc_1(B_311,C_312)) ) ),
    inference(resolution,[status(thm)],[c_4,c_93])).

tff(c_1699,plain,(
    ! [B_313,C_314] :
      ( ~ v1_xboole_0(B_313)
      | v1_xboole_0(k2_zfmisc_1(B_313,C_314)) ) ),
    inference(resolution,[status(thm)],[c_1664,c_2])).

tff(c_1705,plain,(
    ! [A_12,B_13,C_14] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_12,B_13))
      | v1_xboole_0(k3_zfmisc_1(A_12,B_13,C_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1699])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17,D_18] : k2_zfmisc_1(k3_zfmisc_1(A_15,B_16,C_17),D_18) = k4_zfmisc_1(A_15,B_16,C_17,D_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1775,plain,(
    ! [A_325,B_326,C_327,D_328] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_325,B_326,C_327))
      | v1_xboole_0(k4_zfmisc_1(A_325,B_326,C_327,D_328)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1699])).

tff(c_56,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_7','#skF_8','#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_1779,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_1775,c_56])).

tff(c_1786,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_1705,c_1779])).

tff(c_1793,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1636,c_1786])).

tff(c_1798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1345,c_1793])).

tff(c_1799,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_1836,plain,(
    ! [B_342,C_343] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_342,C_343))),C_343)
      | v1_xboole_0(k2_zfmisc_1(B_342,C_343)) ) ),
    inference(resolution,[status(thm)],[c_4,c_112])).

tff(c_1864,plain,(
    ! [C_344,B_345] :
      ( ~ v1_xboole_0(C_344)
      | v1_xboole_0(k2_zfmisc_1(B_345,C_344)) ) ),
    inference(resolution,[status(thm)],[c_1836,c_2])).

tff(c_1870,plain,(
    ! [C_14,A_12,B_13] :
      ( ~ v1_xboole_0(C_14)
      | v1_xboole_0(k3_zfmisc_1(A_12,B_13,C_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1864])).

tff(c_2099,plain,(
    ! [B_387,C_388] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_387,C_388))),B_387)
      | v1_xboole_0(k2_zfmisc_1(B_387,C_388)) ) ),
    inference(resolution,[status(thm)],[c_4,c_93])).

tff(c_2134,plain,(
    ! [B_389,C_390] :
      ( ~ v1_xboole_0(B_389)
      | v1_xboole_0(k2_zfmisc_1(B_389,C_390)) ) ),
    inference(resolution,[status(thm)],[c_2099,c_2])).

tff(c_2244,plain,(
    ! [A_403,B_404,C_405,D_406] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_403,B_404,C_405))
      | v1_xboole_0(k4_zfmisc_1(A_403,B_404,C_405,D_406)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2134])).

tff(c_2248,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_2244,c_56])).

tff(c_2254,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_1870,c_2248])).

tff(c_2259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1799,c_2254])).

tff(c_2260,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_2293,plain,(
    ! [B_415,C_416] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_415,C_416))),B_415)
      | v1_xboole_0(k2_zfmisc_1(B_415,C_416)) ) ),
    inference(resolution,[status(thm)],[c_4,c_93])).

tff(c_2321,plain,(
    ! [B_415,C_416] :
      ( ~ v1_xboole_0(B_415)
      | v1_xboole_0(k2_zfmisc_1(B_415,C_416)) ) ),
    inference(resolution,[status(thm)],[c_2293,c_2])).

tff(c_2329,plain,(
    ! [B_422,C_423] :
      ( ~ v1_xboole_0(B_422)
      | v1_xboole_0(k2_zfmisc_1(B_422,C_423)) ) ),
    inference(resolution,[status(thm)],[c_2293,c_2])).

tff(c_2335,plain,(
    ! [A_12,B_13,C_14] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_12,B_13))
      | v1_xboole_0(k3_zfmisc_1(A_12,B_13,C_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2329])).

tff(c_2690,plain,(
    ! [A_484,B_485,C_486,D_487] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_484,B_485,C_486))
      | v1_xboole_0(k4_zfmisc_1(A_484,B_485,C_486,D_487)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2329])).

tff(c_2694,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_2690,c_56])).

tff(c_2702,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_2335,c_2694])).

tff(c_2738,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2321,c_2702])).

tff(c_2743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2260,c_2738])).

tff(c_2744,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_2761,plain,(
    ! [A_493,B_494,C_495,D_496] : k2_zfmisc_1(k3_zfmisc_1(A_493,B_494,C_495),D_496) = k4_zfmisc_1(A_493,B_494,C_495,D_496) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_19,C_21,B_20] :
      ( r2_hidden(k2_mcart_1(A_19),C_21)
      | ~ r2_hidden(A_19,k2_zfmisc_1(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2896,plain,(
    ! [A_528,D_525,A_527,C_526,B_529] :
      ( r2_hidden(k2_mcart_1(A_527),D_525)
      | ~ r2_hidden(A_527,k4_zfmisc_1(A_528,B_529,C_526,D_525)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2761,c_22])).

tff(c_2918,plain,(
    r2_hidden(k2_mcart_1('#skF_11'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_36,c_2896])).

tff(c_2924,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_2918,c_2])).

tff(c_2931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2744,c_2924])).

tff(c_2933,plain,(
    r2_hidden(k8_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_2938,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2933,c_2])).

tff(c_3033,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_73,c_3021])).

tff(c_3045,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2938,c_3033])).

tff(c_3063,plain,(
    ! [D_555,E_553,A_552,C_554,B_556] :
      ( k11_mcart_1(A_552,B_556,C_554,D_555,E_553) = k2_mcart_1(E_553)
      | ~ m1_subset_1(E_553,k4_zfmisc_1(A_552,B_556,C_554,D_555))
      | k1_xboole_0 = D_555
      | k1_xboole_0 = C_554
      | k1_xboole_0 = B_556
      | k1_xboole_0 = A_552 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3067,plain,
    ( k11_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11') = k2_mcart_1('#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_3063])).

tff(c_3109,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3067])).

tff(c_3111,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3109,c_12])).

tff(c_3113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3045,c_3111])).

tff(c_3114,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6'
    | k11_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11') = k2_mcart_1('#skF_11') ),
    inference(splitRight,[status(thm)],[c_3067])).

tff(c_3150,plain,(
    k11_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11') = k2_mcart_1('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_3114])).

tff(c_2932,plain,
    ( ~ r2_hidden(k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_8')
    | ~ r2_hidden(k10_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_9')
    | ~ r2_hidden(k11_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_3129,plain,(
    ~ r2_hidden(k11_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2932])).

tff(c_3166,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_11'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3150,c_3129])).

tff(c_2989,plain,(
    ! [A_543,B_544,C_545,D_546] : k2_zfmisc_1(k3_zfmisc_1(A_543,B_544,C_545),D_546) = k4_zfmisc_1(A_543,B_544,C_545,D_546) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3222,plain,(
    ! [B_585,A_586,D_588,A_587,C_589] :
      ( r2_hidden(k2_mcart_1(A_586),D_588)
      | ~ r2_hidden(A_586,k4_zfmisc_1(A_587,B_585,C_589,D_588)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2989,c_22])).

tff(c_3239,plain,(
    r2_hidden(k2_mcart_1('#skF_11'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_36,c_3222])).

tff(c_3251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3166,c_3239])).

tff(c_3252,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3114])).

tff(c_3269,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3252])).

tff(c_3272,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3269,c_12])).

tff(c_3274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3062,c_3272])).

tff(c_3275,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3252])).

tff(c_3277,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3275])).

tff(c_3281,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3277,c_12])).

tff(c_3283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3060,c_3281])).

tff(c_3284,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3275])).

tff(c_3298,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3284,c_12])).

tff(c_3300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3061,c_3298])).

tff(c_3301,plain,
    ( ~ r2_hidden(k10_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_9')
    | ~ r2_hidden(k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_2932])).

tff(c_3415,plain,(
    ~ r2_hidden(k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3301])).

tff(c_3115,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3067])).

tff(c_3474,plain,(
    ! [A_611,C_613,B_615,D_614,E_612] :
      ( k2_mcart_1(k1_mcart_1(E_612)) = k10_mcart_1(A_611,B_615,C_613,D_614,E_612)
      | ~ m1_subset_1(E_612,k4_zfmisc_1(A_611,B_615,C_613,D_614))
      | k1_xboole_0 = D_614
      | k1_xboole_0 = C_613
      | k1_xboole_0 = B_615
      | k1_xboole_0 = A_611 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3477,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_11')) = k10_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_3474])).

tff(c_3480,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_11')) = k10_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3115,c_3477])).

tff(c_3487,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3480])).

tff(c_3491,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3487,c_12])).

tff(c_3493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3062,c_3491])).

tff(c_3495,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3480])).

tff(c_3535,plain,(
    ! [D_621,E_619,B_622,A_618,C_620] :
      ( k8_mcart_1(A_618,B_622,C_620,D_621,E_619) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_619)))
      | ~ m1_subset_1(E_619,k4_zfmisc_1(A_618,B_622,C_620,D_621))
      | k1_xboole_0 = D_621
      | k1_xboole_0 = C_620
      | k1_xboole_0 = B_622
      | k1_xboole_0 = A_618 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3537,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k8_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_3535])).

tff(c_3540,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k8_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_3115,c_3495,c_3537])).

tff(c_3683,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3540])).

tff(c_3690,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3683,c_12])).

tff(c_3692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3061,c_3690])).

tff(c_3694,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3540])).

tff(c_3594,plain,(
    ! [A_629,B_633,E_630,D_632,C_631] :
      ( k9_mcart_1(A_629,B_633,C_631,D_632,E_630) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_630)))
      | ~ m1_subset_1(E_630,k4_zfmisc_1(A_629,B_633,C_631,D_632))
      | k1_xboole_0 = D_632
      | k1_xboole_0 = C_631
      | k1_xboole_0 = B_633
      | k1_xboole_0 = A_629 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3596,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_3594])).

tff(c_3599,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_3115,c_3495,c_3596])).

tff(c_3745,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_3694,c_3599])).

tff(c_3746,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3745])).

tff(c_3754,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3746,c_12])).

tff(c_3756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3060,c_3754])).

tff(c_3757,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11') ),
    inference(splitRight,[status(thm)],[c_3745])).

tff(c_4284,plain,(
    ! [A_741,B_740,C_744,A_742,D_743] :
      ( r2_hidden(k1_mcart_1(A_741),k3_zfmisc_1(A_742,B_740,C_744))
      | ~ r2_hidden(A_741,k4_zfmisc_1(A_742,B_740,C_744,D_743)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2989,c_24])).

tff(c_4330,plain,(
    r2_hidden(k1_mcart_1('#skF_11'),k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_36,c_4284])).

tff(c_2978,plain,(
    ! [A_540,B_541,C_542] :
      ( r2_hidden(k1_mcart_1(A_540),B_541)
      | ~ r2_hidden(A_540,k2_zfmisc_1(B_541,C_542)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2980,plain,(
    ! [A_540,A_12,B_13,C_14] :
      ( r2_hidden(k1_mcart_1(A_540),k2_zfmisc_1(A_12,B_13))
      | ~ r2_hidden(A_540,k3_zfmisc_1(A_12,B_13,C_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2978])).

tff(c_4341,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_11')),k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_4330,c_2980])).

tff(c_4351,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))),'#skF_8') ),
    inference(resolution,[status(thm)],[c_4341,c_22])).

tff(c_4359,plain,(
    r2_hidden(k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3757,c_4351])).

tff(c_4361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3415,c_4359])).

tff(c_4362,plain,(
    ~ r2_hidden(k10_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_3301])).

tff(c_4408,plain,(
    ! [E_750,C_751,D_752,A_749,B_753] :
      ( k2_mcart_1(k1_mcart_1(E_750)) = k10_mcart_1(A_749,B_753,C_751,D_752,E_750)
      | ~ m1_subset_1(E_750,k4_zfmisc_1(A_749,B_753,C_751,D_752))
      | k1_xboole_0 = D_752
      | k1_xboole_0 = C_751
      | k1_xboole_0 = B_753
      | k1_xboole_0 = A_749 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4411,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_11')) = k10_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_4408])).

tff(c_4414,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_11')) = k10_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3115,c_4411])).

tff(c_4594,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4414])).

tff(c_4600,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4594,c_12])).

tff(c_4602,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3062,c_4600])).

tff(c_4604,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4414])).

tff(c_4472,plain,(
    ! [A_756,D_759,E_757,B_760,C_758] :
      ( k8_mcart_1(A_756,B_760,C_758,D_759,E_757) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_757)))
      | ~ m1_subset_1(E_757,k4_zfmisc_1(A_756,B_760,C_758,D_759))
      | k1_xboole_0 = D_759
      | k1_xboole_0 = C_758
      | k1_xboole_0 = B_760
      | k1_xboole_0 = A_756 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4474,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k8_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_4472])).

tff(c_4477,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k8_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3115,c_4474])).

tff(c_4797,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k8_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_4604,c_4477])).

tff(c_4798,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4797])).

tff(c_4805,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4798,c_12])).

tff(c_4807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3061,c_4805])).

tff(c_4809,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4797])).

tff(c_4531,plain,(
    ! [E_768,A_767,D_770,B_771,C_769] :
      ( k9_mcart_1(A_767,B_771,C_769,D_770,E_768) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_768)))
      | ~ m1_subset_1(E_768,k4_zfmisc_1(A_767,B_771,C_769,D_770))
      | k1_xboole_0 = D_770
      | k1_xboole_0 = C_769
      | k1_xboole_0 = B_771
      | k1_xboole_0 = A_767 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4533,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_4531])).

tff(c_4536,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3115,c_4533])).

tff(c_4915,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))) = k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11')
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_4604,c_4809,c_4536])).

tff(c_4916,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4915])).

tff(c_4924,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4916,c_12])).

tff(c_4926,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3060,c_4924])).

tff(c_4928,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4915])).

tff(c_4603,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_6'
    | k2_mcart_1(k1_mcart_1('#skF_11')) = k10_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11') ),
    inference(splitRight,[status(thm)],[c_4414])).

tff(c_5087,plain,(
    k2_mcart_1(k1_mcart_1('#skF_11')) = k10_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_4928,c_4809,c_4603])).

tff(c_5367,plain,(
    ! [A_894,B_892,C_896,D_895,A_893] :
      ( r2_hidden(k1_mcart_1(A_893),k3_zfmisc_1(A_894,B_892,C_896))
      | ~ r2_hidden(A_893,k4_zfmisc_1(A_894,B_892,C_896,D_895)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2989,c_24])).

tff(c_5421,plain,(
    r2_hidden(k1_mcart_1('#skF_11'),k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_36,c_5367])).

tff(c_2948,plain,(
    ! [A_534,B_535,C_536] : k2_zfmisc_1(k2_zfmisc_1(A_534,B_535),C_536) = k3_zfmisc_1(A_534,B_535,C_536) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2956,plain,(
    ! [A_19,C_536,A_534,B_535] :
      ( r2_hidden(k2_mcart_1(A_19),C_536)
      | ~ r2_hidden(A_19,k3_zfmisc_1(A_534,B_535,C_536)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2948,c_22])).

tff(c_5426,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_11')),'#skF_9') ),
    inference(resolution,[status(thm)],[c_5421,c_2956])).

tff(c_5434,plain,(
    r2_hidden(k10_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_11'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5087,c_5426])).

tff(c_5436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4362,c_5434])).

tff(c_5437,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_3046])).

tff(c_2939,plain,(
    ! [A_531,C_532,B_533] :
      ( r2_hidden(k2_mcart_1(A_531),C_532)
      | ~ r2_hidden(A_531,k2_zfmisc_1(B_533,C_532)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5850,plain,(
    ! [B_957,C_958] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_957,C_958))),C_958)
      | v1_xboole_0(k2_zfmisc_1(B_957,C_958)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2939])).

tff(c_5879,plain,(
    ! [C_958,B_957] :
      ( ~ v1_xboole_0(C_958)
      | v1_xboole_0(k2_zfmisc_1(B_957,C_958)) ) ),
    inference(resolution,[status(thm)],[c_5850,c_2])).

tff(c_5550,plain,(
    ! [B_915,C_916] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_915,C_916))),B_915)
      | v1_xboole_0(k2_zfmisc_1(B_915,C_916)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2978])).

tff(c_5588,plain,(
    ! [B_917,C_918] :
      ( ~ v1_xboole_0(B_917)
      | v1_xboole_0(k2_zfmisc_1(B_917,C_918)) ) ),
    inference(resolution,[status(thm)],[c_5550,c_2])).

tff(c_5594,plain,(
    ! [A_12,B_13,C_14] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_12,B_13))
      | v1_xboole_0(k3_zfmisc_1(A_12,B_13,C_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_5588])).

tff(c_5956,plain,(
    ! [A_974,B_975,C_976,D_977] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_974,B_975,C_976))
      | v1_xboole_0(k4_zfmisc_1(A_974,B_975,C_976,D_977)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_5588])).

tff(c_5960,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_5956,c_56])).

tff(c_5968,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_5594,c_5960])).

tff(c_5971,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_5879,c_5968])).

tff(c_5978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5437,c_5971])).

tff(c_5979,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_3047])).

tff(c_6438,plain,(
    ! [B_1039,C_1040] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1039,C_1040))),C_1040)
      | v1_xboole_0(k2_zfmisc_1(B_1039,C_1040)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2939])).

tff(c_6470,plain,(
    ! [C_1041,B_1042] :
      ( ~ v1_xboole_0(C_1041)
      | v1_xboole_0(k2_zfmisc_1(B_1042,C_1041)) ) ),
    inference(resolution,[status(thm)],[c_6438,c_2])).

tff(c_6476,plain,(
    ! [C_14,A_12,B_13] :
      ( ~ v1_xboole_0(C_14)
      | v1_xboole_0(k3_zfmisc_1(A_12,B_13,C_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_6470])).

tff(c_6326,plain,(
    ! [B_1025,C_1026] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1025,C_1026))),B_1025)
      | v1_xboole_0(k2_zfmisc_1(B_1025,C_1026)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2978])).

tff(c_6363,plain,(
    ! [B_1027,C_1028] :
      ( ~ v1_xboole_0(B_1027)
      | v1_xboole_0(k2_zfmisc_1(B_1027,C_1028)) ) ),
    inference(resolution,[status(thm)],[c_6326,c_2])).

tff(c_6485,plain,(
    ! [A_1050,B_1051,C_1052,D_1053] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_1050,B_1051,C_1052))
      | v1_xboole_0(k4_zfmisc_1(A_1050,B_1051,C_1052,D_1053)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_6363])).

tff(c_6489,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_6485,c_56])).

tff(c_6492,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_6476,c_6489])).

tff(c_6499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5979,c_6492])).

tff(c_6500,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_3042])).

tff(c_6529,plain,(
    ! [A_1064,A_1065,D_1066,B_1063,C_1067] :
      ( r2_hidden(k2_mcart_1(A_1064),D_1066)
      | ~ r2_hidden(A_1064,k4_zfmisc_1(A_1065,B_1063,C_1067,D_1066)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2989,c_22])).

tff(c_6543,plain,(
    r2_hidden(k2_mcart_1('#skF_11'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_36,c_6529])).

tff(c_6549,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_6543,c_2])).

tff(c_6554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6500,c_6549])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:22:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.02/2.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.02/2.47  
% 7.02/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.02/2.47  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 7.02/2.47  
% 7.02/2.47  %Foreground sorts:
% 7.02/2.47  
% 7.02/2.47  
% 7.02/2.47  %Background operators:
% 7.02/2.47  
% 7.02/2.47  
% 7.02/2.47  %Foreground operators:
% 7.02/2.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.02/2.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.02/2.47  tff('#skF_11', type, '#skF_11': $i).
% 7.02/2.47  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 7.02/2.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.02/2.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.02/2.47  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 7.02/2.47  tff('#skF_7', type, '#skF_7': $i).
% 7.02/2.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.02/2.47  tff('#skF_10', type, '#skF_10': $i).
% 7.02/2.47  tff('#skF_5', type, '#skF_5': $i).
% 7.02/2.47  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 7.02/2.47  tff('#skF_6', type, '#skF_6': $i).
% 7.02/2.47  tff('#skF_3', type, '#skF_3': $i).
% 7.02/2.47  tff('#skF_9', type, '#skF_9': $i).
% 7.02/2.47  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 7.02/2.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.02/2.47  tff('#skF_8', type, '#skF_8': $i).
% 7.02/2.47  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 7.02/2.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.02/2.47  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 7.02/2.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.02/2.47  tff('#skF_4', type, '#skF_4': $i).
% 7.02/2.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.02/2.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.02/2.47  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 7.02/2.47  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 7.02/2.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.02/2.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.02/2.47  
% 7.39/2.50  tff(f_103, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(A)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(B)) => (![G]: (m1_subset_1(G, k1_zfmisc_1(C)) => (![H]: (m1_subset_1(H, k1_zfmisc_1(D)) => (![I]: (m1_subset_1(I, k4_zfmisc_1(A, B, C, D)) => (r2_hidden(I, k4_zfmisc_1(E, F, G, H)) => (((r2_hidden(k8_mcart_1(A, B, C, D, I), E) & r2_hidden(k9_mcart_1(A, B, C, D, I), F)) & r2_hidden(k10_mcart_1(A, B, C, D, I), G)) & r2_hidden(k11_mcart_1(A, B, C, D, I), H))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_mcart_1)).
% 7.39/2.50  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.39/2.50  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.39/2.50  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.39/2.50  tff(f_78, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 7.39/2.50  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.39/2.50  tff(f_47, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 7.39/2.50  tff(f_53, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 7.39/2.50  tff(f_45, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 7.39/2.50  tff(c_42, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.39/2.50  tff(c_57, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.39/2.50  tff(c_70, plain, (r1_tarski('#skF_9', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_57])).
% 7.39/2.50  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.39/2.50  tff(c_2965, plain, (![C_537, B_538, A_539]: (r2_hidden(C_537, B_538) | ~r2_hidden(C_537, A_539) | ~r1_tarski(A_539, B_538))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.39/2.50  tff(c_3005, plain, (![A_547, B_548]: (r2_hidden('#skF_1'(A_547), B_548) | ~r1_tarski(A_547, B_548) | v1_xboole_0(A_547))), inference(resolution, [status(thm)], [c_4, c_2965])).
% 7.39/2.50  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.39/2.50  tff(c_3021, plain, (![B_549, A_550]: (~v1_xboole_0(B_549) | ~r1_tarski(A_550, B_549) | v1_xboole_0(A_550))), inference(resolution, [status(thm)], [c_3005, c_2])).
% 7.39/2.50  tff(c_3047, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_70, c_3021])).
% 7.39/2.50  tff(c_3061, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_3047])).
% 7.39/2.50  tff(c_40, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.39/2.50  tff(c_71, plain, (r1_tarski('#skF_10', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_57])).
% 7.39/2.50  tff(c_3042, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_71, c_3021])).
% 7.39/2.50  tff(c_3060, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_3042])).
% 7.39/2.50  tff(c_44, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.39/2.50  tff(c_72, plain, (r1_tarski('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_57])).
% 7.39/2.50  tff(c_3046, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_72, c_3021])).
% 7.39/2.50  tff(c_3062, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_3046])).
% 7.39/2.50  tff(c_34, plain, (~r2_hidden(k11_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_10') | ~r2_hidden(k10_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_9') | ~r2_hidden(k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_8') | ~r2_hidden(k8_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.39/2.50  tff(c_91, plain, (~r2_hidden(k8_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_7')), inference(splitLeft, [status(thm)], [c_34])).
% 7.39/2.50  tff(c_102, plain, (![C_71, B_72, A_73]: (r2_hidden(C_71, B_72) | ~r2_hidden(C_71, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.39/2.50  tff(c_140, plain, (![A_80, B_81]: (r2_hidden('#skF_1'(A_80), B_81) | ~r1_tarski(A_80, B_81) | v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_4, c_102])).
% 7.39/2.50  tff(c_156, plain, (![B_82, A_83]: (~v1_xboole_0(B_82) | ~r1_tarski(A_83, B_82) | v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_140, c_2])).
% 7.39/2.50  tff(c_177, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_71, c_156])).
% 7.39/2.50  tff(c_181, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_177])).
% 7.39/2.50  tff(c_179, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_72, c_156])).
% 7.39/2.50  tff(c_212, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_179])).
% 7.39/2.50  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.39/2.50  tff(c_73, plain, (r1_tarski('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_57])).
% 7.39/2.50  tff(c_178, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_73, c_156])).
% 7.39/2.50  tff(c_194, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_178])).
% 7.39/2.50  tff(c_38, plain, (m1_subset_1('#skF_11', k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.39/2.50  tff(c_226, plain, (![E_94, D_96, C_95, B_97, A_93]: (k11_mcart_1(A_93, B_97, C_95, D_96, E_94)=k2_mcart_1(E_94) | ~m1_subset_1(E_94, k4_zfmisc_1(A_93, B_97, C_95, D_96)) | k1_xboole_0=D_96 | k1_xboole_0=C_95 | k1_xboole_0=B_97 | k1_xboole_0=A_93)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.39/2.50  tff(c_230, plain, (k11_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11')=k2_mcart_1('#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_226])).
% 7.39/2.50  tff(c_337, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_230])).
% 7.39/2.50  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.39/2.50  tff(c_340, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_12])).
% 7.39/2.50  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_194, c_340])).
% 7.39/2.50  tff(c_344, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_230])).
% 7.39/2.50  tff(c_293, plain, (![D_108, A_105, E_106, B_109, C_107]: (k2_mcart_1(k1_mcart_1(E_106))=k10_mcart_1(A_105, B_109, C_107, D_108, E_106) | ~m1_subset_1(E_106, k4_zfmisc_1(A_105, B_109, C_107, D_108)) | k1_xboole_0=D_108 | k1_xboole_0=C_107 | k1_xboole_0=B_109 | k1_xboole_0=A_105)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.39/2.50  tff(c_297, plain, (k2_mcart_1(k1_mcart_1('#skF_11'))=k10_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_293])).
% 7.39/2.50  tff(c_369, plain, (k2_mcart_1(k1_mcart_1('#skF_11'))=k10_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_344, c_297])).
% 7.39/2.50  tff(c_370, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_369])).
% 7.39/2.50  tff(c_375, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_370, c_12])).
% 7.39/2.50  tff(c_377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_375])).
% 7.39/2.50  tff(c_379, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_369])).
% 7.39/2.50  tff(c_180, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_70, c_156])).
% 7.39/2.50  tff(c_195, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_180])).
% 7.39/2.50  tff(c_419, plain, (![C_125, D_126, A_123, E_124, B_127]: (k9_mcart_1(A_123, B_127, C_125, D_126, E_124)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_124))) | ~m1_subset_1(E_124, k4_zfmisc_1(A_123, B_127, C_125, D_126)) | k1_xboole_0=D_126 | k1_xboole_0=C_125 | k1_xboole_0=B_127 | k1_xboole_0=A_123)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.39/2.50  tff(c_421, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_419])).
% 7.39/2.50  tff(c_424, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_344, c_379, c_421])).
% 7.39/2.50  tff(c_667, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_424])).
% 7.39/2.50  tff(c_674, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_667, c_12])).
% 7.39/2.50  tff(c_676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_674])).
% 7.39/2.50  tff(c_678, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_424])).
% 7.39/2.50  tff(c_357, plain, (![A_116, D_119, E_117, B_120, C_118]: (k8_mcart_1(A_116, B_120, C_118, D_119, E_117)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_117))) | ~m1_subset_1(E_117, k4_zfmisc_1(A_116, B_120, C_118, D_119)) | k1_xboole_0=D_119 | k1_xboole_0=C_118 | k1_xboole_0=B_120 | k1_xboole_0=A_116)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.39/2.50  tff(c_359, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k8_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_357])).
% 7.39/2.50  tff(c_362, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k8_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_344, c_359])).
% 7.39/2.50  tff(c_725, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k8_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_379, c_678, c_362])).
% 7.39/2.50  tff(c_726, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_725])).
% 7.39/2.50  tff(c_734, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_726, c_12])).
% 7.39/2.50  tff(c_736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_181, c_734])).
% 7.39/2.50  tff(c_737, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k8_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11')), inference(splitRight, [status(thm)], [c_725])).
% 7.39/2.50  tff(c_36, plain, (r2_hidden('#skF_11', k4_zfmisc_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.39/2.50  tff(c_196, plain, (![A_85, B_86, C_87, D_88]: (k2_zfmisc_1(k3_zfmisc_1(A_85, B_86, C_87), D_88)=k4_zfmisc_1(A_85, B_86, C_87, D_88))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.39/2.50  tff(c_24, plain, (![A_19, B_20, C_21]: (r2_hidden(k1_mcart_1(A_19), B_20) | ~r2_hidden(A_19, k2_zfmisc_1(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.39/2.50  tff(c_1259, plain, (![B_250, A_251, A_253, C_254, D_252]: (r2_hidden(k1_mcart_1(A_251), k3_zfmisc_1(A_253, B_250, C_254)) | ~r2_hidden(A_251, k4_zfmisc_1(A_253, B_250, C_254, D_252)))), inference(superposition, [status(thm), theory('equality')], [c_196, c_24])).
% 7.39/2.50  tff(c_1313, plain, (r2_hidden(k1_mcart_1('#skF_11'), k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_36, c_1259])).
% 7.39/2.50  tff(c_121, plain, (![A_77, B_78, C_79]: (k2_zfmisc_1(k2_zfmisc_1(A_77, B_78), C_79)=k3_zfmisc_1(A_77, B_78, C_79))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.39/2.50  tff(c_131, plain, (![A_19, A_77, B_78, C_79]: (r2_hidden(k1_mcart_1(A_19), k2_zfmisc_1(A_77, B_78)) | ~r2_hidden(A_19, k3_zfmisc_1(A_77, B_78, C_79)))), inference(superposition, [status(thm), theory('equality')], [c_121, c_24])).
% 7.39/2.50  tff(c_1324, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_11')), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_1313, c_131])).
% 7.39/2.50  tff(c_1334, plain, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))), '#skF_7')), inference(resolution, [status(thm)], [c_1324, c_24])).
% 7.39/2.50  tff(c_1342, plain, (r2_hidden(k8_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_1334])).
% 7.39/2.50  tff(c_1344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_1342])).
% 7.39/2.50  tff(c_1345, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_179])).
% 7.39/2.50  tff(c_112, plain, (![A_74, C_75, B_76]: (r2_hidden(k2_mcart_1(A_74), C_75) | ~r2_hidden(A_74, k2_zfmisc_1(B_76, C_75)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.39/2.50  tff(c_1607, plain, (![B_300, C_301]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_300, C_301))), C_301) | v1_xboole_0(k2_zfmisc_1(B_300, C_301)))), inference(resolution, [status(thm)], [c_4, c_112])).
% 7.39/2.50  tff(c_1636, plain, (![C_301, B_300]: (~v1_xboole_0(C_301) | v1_xboole_0(k2_zfmisc_1(B_300, C_301)))), inference(resolution, [status(thm)], [c_1607, c_2])).
% 7.39/2.50  tff(c_18, plain, (![A_12, B_13, C_14]: (k2_zfmisc_1(k2_zfmisc_1(A_12, B_13), C_14)=k3_zfmisc_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.39/2.50  tff(c_93, plain, (![A_68, B_69, C_70]: (r2_hidden(k1_mcart_1(A_68), B_69) | ~r2_hidden(A_68, k2_zfmisc_1(B_69, C_70)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.39/2.50  tff(c_1664, plain, (![B_311, C_312]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_311, C_312))), B_311) | v1_xboole_0(k2_zfmisc_1(B_311, C_312)))), inference(resolution, [status(thm)], [c_4, c_93])).
% 7.39/2.50  tff(c_1699, plain, (![B_313, C_314]: (~v1_xboole_0(B_313) | v1_xboole_0(k2_zfmisc_1(B_313, C_314)))), inference(resolution, [status(thm)], [c_1664, c_2])).
% 7.39/2.50  tff(c_1705, plain, (![A_12, B_13, C_14]: (~v1_xboole_0(k2_zfmisc_1(A_12, B_13)) | v1_xboole_0(k3_zfmisc_1(A_12, B_13, C_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1699])).
% 7.39/2.50  tff(c_20, plain, (![A_15, B_16, C_17, D_18]: (k2_zfmisc_1(k3_zfmisc_1(A_15, B_16, C_17), D_18)=k4_zfmisc_1(A_15, B_16, C_17, D_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.39/2.50  tff(c_1775, plain, (![A_325, B_326, C_327, D_328]: (~v1_xboole_0(k3_zfmisc_1(A_325, B_326, C_327)) | v1_xboole_0(k4_zfmisc_1(A_325, B_326, C_327, D_328)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1699])).
% 7.39/2.50  tff(c_56, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_7', '#skF_8', '#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_36, c_2])).
% 7.39/2.50  tff(c_1779, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_1775, c_56])).
% 7.39/2.50  tff(c_1786, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_1705, c_1779])).
% 7.39/2.50  tff(c_1793, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_1636, c_1786])).
% 7.39/2.50  tff(c_1798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1345, c_1793])).
% 7.39/2.50  tff(c_1799, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_180])).
% 7.39/2.50  tff(c_1836, plain, (![B_342, C_343]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_342, C_343))), C_343) | v1_xboole_0(k2_zfmisc_1(B_342, C_343)))), inference(resolution, [status(thm)], [c_4, c_112])).
% 7.39/2.50  tff(c_1864, plain, (![C_344, B_345]: (~v1_xboole_0(C_344) | v1_xboole_0(k2_zfmisc_1(B_345, C_344)))), inference(resolution, [status(thm)], [c_1836, c_2])).
% 7.39/2.50  tff(c_1870, plain, (![C_14, A_12, B_13]: (~v1_xboole_0(C_14) | v1_xboole_0(k3_zfmisc_1(A_12, B_13, C_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1864])).
% 7.39/2.50  tff(c_2099, plain, (![B_387, C_388]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_387, C_388))), B_387) | v1_xboole_0(k2_zfmisc_1(B_387, C_388)))), inference(resolution, [status(thm)], [c_4, c_93])).
% 7.39/2.50  tff(c_2134, plain, (![B_389, C_390]: (~v1_xboole_0(B_389) | v1_xboole_0(k2_zfmisc_1(B_389, C_390)))), inference(resolution, [status(thm)], [c_2099, c_2])).
% 7.39/2.50  tff(c_2244, plain, (![A_403, B_404, C_405, D_406]: (~v1_xboole_0(k3_zfmisc_1(A_403, B_404, C_405)) | v1_xboole_0(k4_zfmisc_1(A_403, B_404, C_405, D_406)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2134])).
% 7.39/2.50  tff(c_2248, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_2244, c_56])).
% 7.39/2.50  tff(c_2254, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_1870, c_2248])).
% 7.39/2.50  tff(c_2259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1799, c_2254])).
% 7.39/2.50  tff(c_2260, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_178])).
% 7.39/2.50  tff(c_2293, plain, (![B_415, C_416]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_415, C_416))), B_415) | v1_xboole_0(k2_zfmisc_1(B_415, C_416)))), inference(resolution, [status(thm)], [c_4, c_93])).
% 7.39/2.50  tff(c_2321, plain, (![B_415, C_416]: (~v1_xboole_0(B_415) | v1_xboole_0(k2_zfmisc_1(B_415, C_416)))), inference(resolution, [status(thm)], [c_2293, c_2])).
% 7.39/2.50  tff(c_2329, plain, (![B_422, C_423]: (~v1_xboole_0(B_422) | v1_xboole_0(k2_zfmisc_1(B_422, C_423)))), inference(resolution, [status(thm)], [c_2293, c_2])).
% 7.39/2.50  tff(c_2335, plain, (![A_12, B_13, C_14]: (~v1_xboole_0(k2_zfmisc_1(A_12, B_13)) | v1_xboole_0(k3_zfmisc_1(A_12, B_13, C_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2329])).
% 7.39/2.50  tff(c_2690, plain, (![A_484, B_485, C_486, D_487]: (~v1_xboole_0(k3_zfmisc_1(A_484, B_485, C_486)) | v1_xboole_0(k4_zfmisc_1(A_484, B_485, C_486, D_487)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2329])).
% 7.39/2.50  tff(c_2694, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_2690, c_56])).
% 7.39/2.50  tff(c_2702, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_2335, c_2694])).
% 7.39/2.50  tff(c_2738, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_2321, c_2702])).
% 7.39/2.50  tff(c_2743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2260, c_2738])).
% 7.39/2.50  tff(c_2744, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_177])).
% 7.39/2.50  tff(c_2761, plain, (![A_493, B_494, C_495, D_496]: (k2_zfmisc_1(k3_zfmisc_1(A_493, B_494, C_495), D_496)=k4_zfmisc_1(A_493, B_494, C_495, D_496))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.39/2.50  tff(c_22, plain, (![A_19, C_21, B_20]: (r2_hidden(k2_mcart_1(A_19), C_21) | ~r2_hidden(A_19, k2_zfmisc_1(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.39/2.50  tff(c_2896, plain, (![A_528, D_525, A_527, C_526, B_529]: (r2_hidden(k2_mcart_1(A_527), D_525) | ~r2_hidden(A_527, k4_zfmisc_1(A_528, B_529, C_526, D_525)))), inference(superposition, [status(thm), theory('equality')], [c_2761, c_22])).
% 7.39/2.50  tff(c_2918, plain, (r2_hidden(k2_mcart_1('#skF_11'), '#skF_10')), inference(resolution, [status(thm)], [c_36, c_2896])).
% 7.39/2.50  tff(c_2924, plain, (~v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_2918, c_2])).
% 7.39/2.50  tff(c_2931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2744, c_2924])).
% 7.39/2.50  tff(c_2933, plain, (r2_hidden(k8_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_7')), inference(splitRight, [status(thm)], [c_34])).
% 7.39/2.50  tff(c_2938, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_2933, c_2])).
% 7.39/2.50  tff(c_3033, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_73, c_3021])).
% 7.39/2.50  tff(c_3045, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2938, c_3033])).
% 7.39/2.50  tff(c_3063, plain, (![D_555, E_553, A_552, C_554, B_556]: (k11_mcart_1(A_552, B_556, C_554, D_555, E_553)=k2_mcart_1(E_553) | ~m1_subset_1(E_553, k4_zfmisc_1(A_552, B_556, C_554, D_555)) | k1_xboole_0=D_555 | k1_xboole_0=C_554 | k1_xboole_0=B_556 | k1_xboole_0=A_552)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.39/2.50  tff(c_3067, plain, (k11_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11')=k2_mcart_1('#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_3063])).
% 7.39/2.50  tff(c_3109, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3067])).
% 7.39/2.50  tff(c_3111, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3109, c_12])).
% 7.39/2.50  tff(c_3113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3045, c_3111])).
% 7.39/2.50  tff(c_3114, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6' | k11_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11')=k2_mcart_1('#skF_11')), inference(splitRight, [status(thm)], [c_3067])).
% 7.39/2.50  tff(c_3150, plain, (k11_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11')=k2_mcart_1('#skF_11')), inference(splitLeft, [status(thm)], [c_3114])).
% 7.39/2.50  tff(c_2932, plain, (~r2_hidden(k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_8') | ~r2_hidden(k10_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_9') | ~r2_hidden(k11_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_10')), inference(splitRight, [status(thm)], [c_34])).
% 7.39/2.50  tff(c_3129, plain, (~r2_hidden(k11_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_10')), inference(splitLeft, [status(thm)], [c_2932])).
% 7.39/2.50  tff(c_3166, plain, (~r2_hidden(k2_mcart_1('#skF_11'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_3150, c_3129])).
% 7.39/2.50  tff(c_2989, plain, (![A_543, B_544, C_545, D_546]: (k2_zfmisc_1(k3_zfmisc_1(A_543, B_544, C_545), D_546)=k4_zfmisc_1(A_543, B_544, C_545, D_546))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.39/2.50  tff(c_3222, plain, (![B_585, A_586, D_588, A_587, C_589]: (r2_hidden(k2_mcart_1(A_586), D_588) | ~r2_hidden(A_586, k4_zfmisc_1(A_587, B_585, C_589, D_588)))), inference(superposition, [status(thm), theory('equality')], [c_2989, c_22])).
% 7.39/2.50  tff(c_3239, plain, (r2_hidden(k2_mcart_1('#skF_11'), '#skF_10')), inference(resolution, [status(thm)], [c_36, c_3222])).
% 7.39/2.50  tff(c_3251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3166, c_3239])).
% 7.39/2.50  tff(c_3252, plain, (k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3114])).
% 7.39/2.50  tff(c_3269, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_3252])).
% 7.39/2.50  tff(c_3272, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3269, c_12])).
% 7.39/2.50  tff(c_3274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3062, c_3272])).
% 7.39/2.50  tff(c_3275, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_3252])).
% 7.39/2.50  tff(c_3277, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_3275])).
% 7.39/2.50  tff(c_3281, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3277, c_12])).
% 7.39/2.50  tff(c_3283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3060, c_3281])).
% 7.39/2.50  tff(c_3284, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3275])).
% 7.39/2.50  tff(c_3298, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3284, c_12])).
% 7.39/2.50  tff(c_3300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3061, c_3298])).
% 7.39/2.50  tff(c_3301, plain, (~r2_hidden(k10_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_9') | ~r2_hidden(k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_8')), inference(splitRight, [status(thm)], [c_2932])).
% 7.39/2.50  tff(c_3415, plain, (~r2_hidden(k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_8')), inference(splitLeft, [status(thm)], [c_3301])).
% 7.39/2.50  tff(c_3115, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_3067])).
% 7.39/2.50  tff(c_3474, plain, (![A_611, C_613, B_615, D_614, E_612]: (k2_mcart_1(k1_mcart_1(E_612))=k10_mcart_1(A_611, B_615, C_613, D_614, E_612) | ~m1_subset_1(E_612, k4_zfmisc_1(A_611, B_615, C_613, D_614)) | k1_xboole_0=D_614 | k1_xboole_0=C_613 | k1_xboole_0=B_615 | k1_xboole_0=A_611)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.39/2.50  tff(c_3477, plain, (k2_mcart_1(k1_mcart_1('#skF_11'))=k10_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_3474])).
% 7.39/2.50  tff(c_3480, plain, (k2_mcart_1(k1_mcart_1('#skF_11'))=k10_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3115, c_3477])).
% 7.39/2.50  tff(c_3487, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_3480])).
% 7.39/2.50  tff(c_3491, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3487, c_12])).
% 7.39/2.50  tff(c_3493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3062, c_3491])).
% 7.39/2.50  tff(c_3495, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_3480])).
% 7.39/2.50  tff(c_3535, plain, (![D_621, E_619, B_622, A_618, C_620]: (k8_mcart_1(A_618, B_622, C_620, D_621, E_619)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_619))) | ~m1_subset_1(E_619, k4_zfmisc_1(A_618, B_622, C_620, D_621)) | k1_xboole_0=D_621 | k1_xboole_0=C_620 | k1_xboole_0=B_622 | k1_xboole_0=A_618)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.39/2.50  tff(c_3537, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k8_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_3535])).
% 7.39/2.50  tff(c_3540, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k8_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_3115, c_3495, c_3537])).
% 7.39/2.50  tff(c_3683, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_3540])).
% 7.39/2.50  tff(c_3690, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3683, c_12])).
% 7.39/2.50  tff(c_3692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3061, c_3690])).
% 7.39/2.50  tff(c_3694, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_3540])).
% 7.39/2.50  tff(c_3594, plain, (![A_629, B_633, E_630, D_632, C_631]: (k9_mcart_1(A_629, B_633, C_631, D_632, E_630)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_630))) | ~m1_subset_1(E_630, k4_zfmisc_1(A_629, B_633, C_631, D_632)) | k1_xboole_0=D_632 | k1_xboole_0=C_631 | k1_xboole_0=B_633 | k1_xboole_0=A_629)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.39/2.50  tff(c_3596, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_3594])).
% 7.39/2.50  tff(c_3599, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_3115, c_3495, c_3596])).
% 7.39/2.50  tff(c_3745, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_3694, c_3599])).
% 7.39/2.50  tff(c_3746, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_3745])).
% 7.39/2.50  tff(c_3754, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3746, c_12])).
% 7.39/2.50  tff(c_3756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3060, c_3754])).
% 7.39/2.50  tff(c_3757, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11')), inference(splitRight, [status(thm)], [c_3745])).
% 7.39/2.50  tff(c_4284, plain, (![A_741, B_740, C_744, A_742, D_743]: (r2_hidden(k1_mcart_1(A_741), k3_zfmisc_1(A_742, B_740, C_744)) | ~r2_hidden(A_741, k4_zfmisc_1(A_742, B_740, C_744, D_743)))), inference(superposition, [status(thm), theory('equality')], [c_2989, c_24])).
% 7.39/2.50  tff(c_4330, plain, (r2_hidden(k1_mcart_1('#skF_11'), k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_36, c_4284])).
% 7.39/2.50  tff(c_2978, plain, (![A_540, B_541, C_542]: (r2_hidden(k1_mcart_1(A_540), B_541) | ~r2_hidden(A_540, k2_zfmisc_1(B_541, C_542)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.39/2.50  tff(c_2980, plain, (![A_540, A_12, B_13, C_14]: (r2_hidden(k1_mcart_1(A_540), k2_zfmisc_1(A_12, B_13)) | ~r2_hidden(A_540, k3_zfmisc_1(A_12, B_13, C_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2978])).
% 7.39/2.50  tff(c_4341, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_11')), k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_4330, c_2980])).
% 7.39/2.50  tff(c_4351, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11'))), '#skF_8')), inference(resolution, [status(thm)], [c_4341, c_22])).
% 7.39/2.50  tff(c_4359, plain, (r2_hidden(k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3757, c_4351])).
% 7.39/2.50  tff(c_4361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3415, c_4359])).
% 7.39/2.50  tff(c_4362, plain, (~r2_hidden(k10_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_9')), inference(splitRight, [status(thm)], [c_3301])).
% 7.39/2.50  tff(c_4408, plain, (![E_750, C_751, D_752, A_749, B_753]: (k2_mcart_1(k1_mcart_1(E_750))=k10_mcart_1(A_749, B_753, C_751, D_752, E_750) | ~m1_subset_1(E_750, k4_zfmisc_1(A_749, B_753, C_751, D_752)) | k1_xboole_0=D_752 | k1_xboole_0=C_751 | k1_xboole_0=B_753 | k1_xboole_0=A_749)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.39/2.50  tff(c_4411, plain, (k2_mcart_1(k1_mcart_1('#skF_11'))=k10_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_4408])).
% 7.39/2.50  tff(c_4414, plain, (k2_mcart_1(k1_mcart_1('#skF_11'))=k10_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3115, c_4411])).
% 7.39/2.50  tff(c_4594, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_4414])).
% 7.39/2.50  tff(c_4600, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4594, c_12])).
% 7.39/2.50  tff(c_4602, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3062, c_4600])).
% 7.39/2.50  tff(c_4604, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_4414])).
% 7.39/2.50  tff(c_4472, plain, (![A_756, D_759, E_757, B_760, C_758]: (k8_mcart_1(A_756, B_760, C_758, D_759, E_757)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_757))) | ~m1_subset_1(E_757, k4_zfmisc_1(A_756, B_760, C_758, D_759)) | k1_xboole_0=D_759 | k1_xboole_0=C_758 | k1_xboole_0=B_760 | k1_xboole_0=A_756)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.39/2.50  tff(c_4474, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k8_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_4472])).
% 7.39/2.50  tff(c_4477, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k8_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3115, c_4474])).
% 7.39/2.50  tff(c_4797, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k8_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_4604, c_4477])).
% 7.39/2.50  tff(c_4798, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_4797])).
% 7.39/2.50  tff(c_4805, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4798, c_12])).
% 7.39/2.50  tff(c_4807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3061, c_4805])).
% 7.39/2.50  tff(c_4809, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_4797])).
% 7.39/2.50  tff(c_4531, plain, (![E_768, A_767, D_770, B_771, C_769]: (k9_mcart_1(A_767, B_771, C_769, D_770, E_768)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_768))) | ~m1_subset_1(E_768, k4_zfmisc_1(A_767, B_771, C_769, D_770)) | k1_xboole_0=D_770 | k1_xboole_0=C_769 | k1_xboole_0=B_771 | k1_xboole_0=A_767)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.39/2.50  tff(c_4533, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_38, c_4531])).
% 7.39/2.50  tff(c_4536, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3115, c_4533])).
% 7.39/2.50  tff(c_4915, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_11')))=k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11') | k1_xboole_0='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_4604, c_4809, c_4536])).
% 7.39/2.50  tff(c_4916, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_4915])).
% 7.39/2.50  tff(c_4924, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4916, c_12])).
% 7.39/2.50  tff(c_4926, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3060, c_4924])).
% 7.39/2.50  tff(c_4928, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_4915])).
% 7.39/2.50  tff(c_4603, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_6' | k2_mcart_1(k1_mcart_1('#skF_11'))=k10_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11')), inference(splitRight, [status(thm)], [c_4414])).
% 7.39/2.50  tff(c_5087, plain, (k2_mcart_1(k1_mcart_1('#skF_11'))=k10_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_4928, c_4809, c_4603])).
% 7.39/2.50  tff(c_5367, plain, (![A_894, B_892, C_896, D_895, A_893]: (r2_hidden(k1_mcart_1(A_893), k3_zfmisc_1(A_894, B_892, C_896)) | ~r2_hidden(A_893, k4_zfmisc_1(A_894, B_892, C_896, D_895)))), inference(superposition, [status(thm), theory('equality')], [c_2989, c_24])).
% 7.39/2.50  tff(c_5421, plain, (r2_hidden(k1_mcart_1('#skF_11'), k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_36, c_5367])).
% 7.39/2.50  tff(c_2948, plain, (![A_534, B_535, C_536]: (k2_zfmisc_1(k2_zfmisc_1(A_534, B_535), C_536)=k3_zfmisc_1(A_534, B_535, C_536))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.39/2.50  tff(c_2956, plain, (![A_19, C_536, A_534, B_535]: (r2_hidden(k2_mcart_1(A_19), C_536) | ~r2_hidden(A_19, k3_zfmisc_1(A_534, B_535, C_536)))), inference(superposition, [status(thm), theory('equality')], [c_2948, c_22])).
% 7.39/2.50  tff(c_5426, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_11')), '#skF_9')), inference(resolution, [status(thm)], [c_5421, c_2956])).
% 7.39/2.50  tff(c_5434, plain, (r2_hidden(k10_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_11'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_5087, c_5426])).
% 7.39/2.50  tff(c_5436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4362, c_5434])).
% 7.39/2.50  tff(c_5437, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_3046])).
% 7.39/2.50  tff(c_2939, plain, (![A_531, C_532, B_533]: (r2_hidden(k2_mcart_1(A_531), C_532) | ~r2_hidden(A_531, k2_zfmisc_1(B_533, C_532)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.39/2.50  tff(c_5850, plain, (![B_957, C_958]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_957, C_958))), C_958) | v1_xboole_0(k2_zfmisc_1(B_957, C_958)))), inference(resolution, [status(thm)], [c_4, c_2939])).
% 7.39/2.50  tff(c_5879, plain, (![C_958, B_957]: (~v1_xboole_0(C_958) | v1_xboole_0(k2_zfmisc_1(B_957, C_958)))), inference(resolution, [status(thm)], [c_5850, c_2])).
% 7.39/2.50  tff(c_5550, plain, (![B_915, C_916]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_915, C_916))), B_915) | v1_xboole_0(k2_zfmisc_1(B_915, C_916)))), inference(resolution, [status(thm)], [c_4, c_2978])).
% 7.39/2.50  tff(c_5588, plain, (![B_917, C_918]: (~v1_xboole_0(B_917) | v1_xboole_0(k2_zfmisc_1(B_917, C_918)))), inference(resolution, [status(thm)], [c_5550, c_2])).
% 7.39/2.50  tff(c_5594, plain, (![A_12, B_13, C_14]: (~v1_xboole_0(k2_zfmisc_1(A_12, B_13)) | v1_xboole_0(k3_zfmisc_1(A_12, B_13, C_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_5588])).
% 7.39/2.50  tff(c_5956, plain, (![A_974, B_975, C_976, D_977]: (~v1_xboole_0(k3_zfmisc_1(A_974, B_975, C_976)) | v1_xboole_0(k4_zfmisc_1(A_974, B_975, C_976, D_977)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_5588])).
% 7.39/2.50  tff(c_5960, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_5956, c_56])).
% 7.39/2.50  tff(c_5968, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_5594, c_5960])).
% 7.39/2.50  tff(c_5971, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_5879, c_5968])).
% 7.39/2.50  tff(c_5978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5437, c_5971])).
% 7.39/2.50  tff(c_5979, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_3047])).
% 7.39/2.50  tff(c_6438, plain, (![B_1039, C_1040]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_1039, C_1040))), C_1040) | v1_xboole_0(k2_zfmisc_1(B_1039, C_1040)))), inference(resolution, [status(thm)], [c_4, c_2939])).
% 7.39/2.50  tff(c_6470, plain, (![C_1041, B_1042]: (~v1_xboole_0(C_1041) | v1_xboole_0(k2_zfmisc_1(B_1042, C_1041)))), inference(resolution, [status(thm)], [c_6438, c_2])).
% 7.39/2.50  tff(c_6476, plain, (![C_14, A_12, B_13]: (~v1_xboole_0(C_14) | v1_xboole_0(k3_zfmisc_1(A_12, B_13, C_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_6470])).
% 7.39/2.50  tff(c_6326, plain, (![B_1025, C_1026]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_1025, C_1026))), B_1025) | v1_xboole_0(k2_zfmisc_1(B_1025, C_1026)))), inference(resolution, [status(thm)], [c_4, c_2978])).
% 7.39/2.50  tff(c_6363, plain, (![B_1027, C_1028]: (~v1_xboole_0(B_1027) | v1_xboole_0(k2_zfmisc_1(B_1027, C_1028)))), inference(resolution, [status(thm)], [c_6326, c_2])).
% 7.39/2.50  tff(c_6485, plain, (![A_1050, B_1051, C_1052, D_1053]: (~v1_xboole_0(k3_zfmisc_1(A_1050, B_1051, C_1052)) | v1_xboole_0(k4_zfmisc_1(A_1050, B_1051, C_1052, D_1053)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_6363])).
% 7.39/2.50  tff(c_6489, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_6485, c_56])).
% 7.39/2.50  tff(c_6492, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_6476, c_6489])).
% 7.39/2.50  tff(c_6499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5979, c_6492])).
% 7.39/2.50  tff(c_6500, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_3042])).
% 7.39/2.50  tff(c_6529, plain, (![A_1064, A_1065, D_1066, B_1063, C_1067]: (r2_hidden(k2_mcart_1(A_1064), D_1066) | ~r2_hidden(A_1064, k4_zfmisc_1(A_1065, B_1063, C_1067, D_1066)))), inference(superposition, [status(thm), theory('equality')], [c_2989, c_22])).
% 7.39/2.50  tff(c_6543, plain, (r2_hidden(k2_mcart_1('#skF_11'), '#skF_10')), inference(resolution, [status(thm)], [c_36, c_6529])).
% 7.39/2.50  tff(c_6549, plain, (~v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_6543, c_2])).
% 7.39/2.50  tff(c_6554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6500, c_6549])).
% 7.39/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.39/2.50  
% 7.39/2.50  Inference rules
% 7.39/2.50  ----------------------
% 7.39/2.50  #Ref     : 0
% 7.39/2.50  #Sup     : 1571
% 7.39/2.50  #Fact    : 0
% 7.39/2.50  #Define  : 0
% 7.39/2.50  #Split   : 117
% 7.39/2.50  #Chain   : 0
% 7.39/2.50  #Close   : 0
% 7.39/2.50  
% 7.39/2.50  Ordering : KBO
% 7.39/2.50  
% 7.39/2.50  Simplification rules
% 7.39/2.50  ----------------------
% 7.39/2.50  #Subsume      : 444
% 7.39/2.50  #Demod        : 613
% 7.39/2.50  #Tautology    : 135
% 7.39/2.50  #SimpNegUnit  : 63
% 7.39/2.50  #BackRed      : 132
% 7.39/2.50  
% 7.39/2.50  #Partial instantiations: 0
% 7.39/2.50  #Strategies tried      : 1
% 7.39/2.50  
% 7.39/2.50  Timing (in seconds)
% 7.39/2.50  ----------------------
% 7.39/2.51  Preprocessing        : 0.36
% 7.39/2.51  Parsing              : 0.18
% 7.39/2.51  CNF conversion       : 0.03
% 7.39/2.51  Main loop            : 1.34
% 7.39/2.51  Inferencing          : 0.47
% 7.39/2.51  Reduction            : 0.42
% 7.39/2.51  Demodulation         : 0.27
% 7.39/2.51  BG Simplification    : 0.05
% 7.39/2.51  Subsumption          : 0.28
% 7.39/2.51  Abstraction          : 0.06
% 7.39/2.51  MUC search           : 0.00
% 7.39/2.51  Cooper               : 0.00
% 7.39/2.51  Total                : 1.78
% 7.39/2.51  Index Insertion      : 0.00
% 7.39/2.51  Index Deletion       : 0.00
% 7.39/2.51  Index Matching       : 0.00
% 7.39/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
