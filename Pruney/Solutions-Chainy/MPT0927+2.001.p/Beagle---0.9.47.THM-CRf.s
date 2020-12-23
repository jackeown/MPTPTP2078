%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:23 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.53s
% Verified   : 
% Statistics : Number of formulae       :  235 ( 849 expanded)
%              Number of leaves         :   35 ( 277 expanded)
%              Depth                    :   12
%              Number of atoms          :  412 (3134 expanded)
%              Number of equality atoms :  199 (1401 expanded)
%              Maximal formula depth    :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff(f_99,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_mcart_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_74,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_32,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_49,plain,(
    ! [B_53,A_54] :
      ( v1_xboole_0(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_49])).

tff(c_83,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_34,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_62,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_64,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_28,plain,(
    r2_hidden('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_511,plain,(
    ! [A_150,B_151,C_152,D_153] : k2_zfmisc_1(k3_zfmisc_1(A_150,B_151,C_152),D_153) = k4_zfmisc_1(A_150,B_151,C_152,D_153) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_15,C_17,B_16] :
      ( r2_hidden(k2_mcart_1(A_15),C_17)
      | ~ r2_hidden(A_15,k2_zfmisc_1(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_577,plain,(
    ! [A_174,D_170,B_171,C_172,A_173] :
      ( r2_hidden(k2_mcart_1(A_173),D_170)
      | ~ r2_hidden(A_173,k4_zfmisc_1(A_174,B_171,C_172,D_170)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_14])).

tff(c_587,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_28,c_577])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_65,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_49])).

tff(c_67,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_30,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_552,plain,(
    ! [C_158,E_156,D_159,A_157,B_160] :
      ( k11_mcart_1(A_157,B_160,C_158,D_159,E_156) = k2_mcart_1(E_156)
      | ~ m1_subset_1(E_156,k4_zfmisc_1(A_157,B_160,C_158,D_159))
      | k1_xboole_0 = D_159
      | k1_xboole_0 = C_158
      | k1_xboole_0 = B_160
      | k1_xboole_0 = A_157 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_556,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_552])).

tff(c_570,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_556])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_572,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_6])).

tff(c_574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_572])).

tff(c_575,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_556])).

tff(c_640,plain,(
    k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_575])).

tff(c_26,plain,
    ( ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9')
    | ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7')
    | ~ r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_85,plain,(
    ~ r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_154,plain,(
    ! [C_81,B_83,E_79,A_80,D_82] :
      ( k11_mcart_1(A_80,B_83,C_81,D_82,E_79) = k2_mcart_1(E_79)
      | ~ m1_subset_1(E_79,k4_zfmisc_1(A_80,B_83,C_81,D_82))
      | k1_xboole_0 = D_82
      | k1_xboole_0 = C_81
      | k1_xboole_0 = B_83
      | k1_xboole_0 = A_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_158,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_154])).

tff(c_230,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_233,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_6])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_233])).

tff(c_237,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_212,plain,(
    ! [A_96,E_95,B_99,C_97,D_98] :
      ( k2_mcart_1(k1_mcart_1(E_95)) = k10_mcart_1(A_96,B_99,C_97,D_98,E_95)
      | ~ m1_subset_1(E_95,k4_zfmisc_1(A_96,B_99,C_97,D_98))
      | k1_xboole_0 = D_98
      | k1_xboole_0 = C_97
      | k1_xboole_0 = B_99
      | k1_xboole_0 = A_96 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_216,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_212])).

tff(c_288,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_216])).

tff(c_289,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_294,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_6])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_294])).

tff(c_298,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_318,plain,(
    ! [B_126,E_122,A_123,D_125,C_124] :
      ( k9_mcart_1(A_123,B_126,C_124,D_125,E_122) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_122)))
      | ~ m1_subset_1(E_122,k4_zfmisc_1(A_123,B_126,C_124,D_125))
      | k1_xboole_0 = D_125
      | k1_xboole_0 = C_124
      | k1_xboole_0 = B_126
      | k1_xboole_0 = A_123 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_320,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_318])).

tff(c_323,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_298,c_320])).

tff(c_444,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_323])).

tff(c_451,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_6])).

tff(c_453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_451])).

tff(c_455,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_323])).

tff(c_254,plain,(
    ! [A_110,D_112,C_111,B_113,E_109] :
      ( k8_mcart_1(A_110,B_113,C_111,D_112,E_109) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_109)))
      | ~ m1_subset_1(E_109,k4_zfmisc_1(A_110,B_113,C_111,D_112))
      | k1_xboole_0 = D_112
      | k1_xboole_0 = C_111
      | k1_xboole_0 = B_113
      | k1_xboole_0 = A_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_256,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_254])).

tff(c_259,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_256])).

tff(c_460,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_298,c_455,c_259])).

tff(c_461,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_460])).

tff(c_469,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_6])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_469])).

tff(c_472,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_460])).

tff(c_105,plain,(
    ! [A_68,B_69,C_70,D_71] : k2_zfmisc_1(k3_zfmisc_1(A_68,B_69,C_70),D_71) = k4_zfmisc_1(A_68,B_69,C_70,D_71) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] :
      ( r2_hidden(k1_mcart_1(A_15),B_16)
      | ~ r2_hidden(A_15,k2_zfmisc_1(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_403,plain,(
    ! [B_137,C_136,A_138,A_139,D_135] :
      ( r2_hidden(k1_mcart_1(A_138),k3_zfmisc_1(A_139,B_137,C_136))
      | ~ r2_hidden(A_138,k4_zfmisc_1(A_139,B_137,C_136,D_135)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_16])).

tff(c_421,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_28,c_403])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10) = k3_zfmisc_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_93,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden(k1_mcart_1(A_61),B_62)
      | ~ r2_hidden(A_61,k2_zfmisc_1(B_62,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_95,plain,(
    ! [A_61,A_8,B_9,C_10] :
      ( r2_hidden(k1_mcart_1(A_61),k2_zfmisc_1(A_8,B_9))
      | ~ r2_hidden(A_61,k3_zfmisc_1(A_8,B_9,C_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_93])).

tff(c_430,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_421,c_95])).

tff(c_441,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))),'#skF_6') ),
    inference(resolution,[status(thm)],[c_430,c_16])).

tff(c_482,plain,(
    r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_441])).

tff(c_484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_482])).

tff(c_485,plain,
    ( ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7')
    | ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_498,plain,(
    ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_485])).

tff(c_641,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_498])).

tff(c_644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_641])).

tff(c_645,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_575])).

tff(c_647,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_645])).

tff(c_651,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_6])).

tff(c_653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_651])).

tff(c_654,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_656,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_654])).

tff(c_668,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_656,c_6])).

tff(c_670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_668])).

tff(c_671,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_654])).

tff(c_678,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_671,c_6])).

tff(c_680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_678])).

tff(c_681,plain,
    ( ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_485])).

tff(c_740,plain,(
    ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_681])).

tff(c_749,plain,(
    ! [B_214,E_210,C_212,A_211,D_213] :
      ( k11_mcart_1(A_211,B_214,C_212,D_213,E_210) = k2_mcart_1(E_210)
      | ~ m1_subset_1(E_210,k4_zfmisc_1(A_211,B_214,C_212,D_213))
      | k1_xboole_0 = D_213
      | k1_xboole_0 = C_212
      | k1_xboole_0 = B_214
      | k1_xboole_0 = A_211 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_753,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_749])).

tff(c_833,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_753])).

tff(c_836,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_6])).

tff(c_838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_836])).

tff(c_840,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_753])).

tff(c_814,plain,(
    ! [D_231,C_230,A_229,E_228,B_232] :
      ( k2_mcart_1(k1_mcart_1(E_228)) = k10_mcart_1(A_229,B_232,C_230,D_231,E_228)
      | ~ m1_subset_1(E_228,k4_zfmisc_1(A_229,B_232,C_230,D_231))
      | k1_xboole_0 = D_231
      | k1_xboole_0 = C_230
      | k1_xboole_0 = B_232
      | k1_xboole_0 = A_229 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_818,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_814])).

tff(c_901,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_840,c_818])).

tff(c_902,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_901])).

tff(c_907,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_902,c_6])).

tff(c_909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_907])).

tff(c_911,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_901])).

tff(c_946,plain,(
    ! [E_256,A_257,D_259,C_258,B_260] :
      ( k9_mcart_1(A_257,B_260,C_258,D_259,E_256) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_256)))
      | ~ m1_subset_1(E_256,k4_zfmisc_1(A_257,B_260,C_258,D_259))
      | k1_xboole_0 = D_259
      | k1_xboole_0 = C_258
      | k1_xboole_0 = B_260
      | k1_xboole_0 = A_257 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_948,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_946])).

tff(c_951,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_840,c_911,c_948])).

tff(c_1053,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_951])).

tff(c_1060,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_6])).

tff(c_1062,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1060])).

tff(c_1064,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_951])).

tff(c_849,plain,(
    ! [A_241,D_243,B_244,C_242,E_240] :
      ( k8_mcart_1(A_241,B_244,C_242,D_243,E_240) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_240)))
      | ~ m1_subset_1(E_240,k4_zfmisc_1(A_241,B_244,C_242,D_243))
      | k1_xboole_0 = D_243
      | k1_xboole_0 = C_242
      | k1_xboole_0 = B_244
      | k1_xboole_0 = A_241 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_851,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_849])).

tff(c_854,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_840,c_851])).

tff(c_1065,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_911,c_1064,c_854])).

tff(c_1066,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1065])).

tff(c_1074,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_6])).

tff(c_1076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_1074])).

tff(c_1078,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1065])).

tff(c_1063,plain,
    ( k1_xboole_0 = '#skF_5'
    | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_951])).

tff(c_1085,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_1078,c_1063])).

tff(c_699,plain,(
    ! [A_199,B_200,C_201,D_202] : k2_zfmisc_1(k3_zfmisc_1(A_199,B_200,C_201),D_202) = k4_zfmisc_1(A_199,B_200,C_201,D_202) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_992,plain,(
    ! [A_268,A_269,D_267,B_266,C_270] :
      ( r2_hidden(k1_mcart_1(A_269),k3_zfmisc_1(A_268,B_266,C_270))
      | ~ r2_hidden(A_269,k4_zfmisc_1(A_268,B_266,C_270,D_267)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_699,c_16])).

tff(c_1010,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_28,c_992])).

tff(c_687,plain,(
    ! [A_192,B_193,C_194] :
      ( r2_hidden(k1_mcart_1(A_192),B_193)
      | ~ r2_hidden(A_192,k2_zfmisc_1(B_193,C_194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_689,plain,(
    ! [A_192,A_8,B_9,C_10] :
      ( r2_hidden(k1_mcart_1(A_192),k2_zfmisc_1(A_8,B_9))
      | ~ r2_hidden(A_192,k3_zfmisc_1(A_8,B_9,C_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_687])).

tff(c_1019,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1010,c_689])).

tff(c_1031,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1019,c_14])).

tff(c_1086,plain,(
    r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_1031])).

tff(c_1088,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_740,c_1086])).

tff(c_1089,plain,(
    ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_681])).

tff(c_1103,plain,(
    ! [A_277,B_280,C_278,E_276,D_279] :
      ( k11_mcart_1(A_277,B_280,C_278,D_279,E_276) = k2_mcart_1(E_276)
      | ~ m1_subset_1(E_276,k4_zfmisc_1(A_277,B_280,C_278,D_279))
      | k1_xboole_0 = D_279
      | k1_xboole_0 = C_278
      | k1_xboole_0 = B_280
      | k1_xboole_0 = A_277 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1107,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_1103])).

tff(c_1187,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1107])).

tff(c_1190,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1187,c_6])).

tff(c_1192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_1190])).

tff(c_1194,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1107])).

tff(c_1165,plain,(
    ! [B_301,C_299,E_297,D_300,A_298] :
      ( k2_mcart_1(k1_mcart_1(E_297)) = k10_mcart_1(A_298,B_301,C_299,D_300,E_297)
      | ~ m1_subset_1(E_297,k4_zfmisc_1(A_298,B_301,C_299,D_300))
      | k1_xboole_0 = D_300
      | k1_xboole_0 = C_299
      | k1_xboole_0 = B_301
      | k1_xboole_0 = A_298 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1169,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_1165])).

tff(c_1284,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1194,c_1169])).

tff(c_1285,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1284])).

tff(c_1290,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1285,c_6])).

tff(c_1292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1290])).

tff(c_1293,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_1284])).

tff(c_1295,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1293])).

tff(c_1346,plain,(
    ! [D_333,B_332,A_334,C_336,A_335] :
      ( r2_hidden(k1_mcart_1(A_335),k3_zfmisc_1(A_334,B_332,C_336))
      | ~ r2_hidden(A_335,k4_zfmisc_1(A_334,B_332,C_336,D_333)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_699,c_16])).

tff(c_1364,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_28,c_1346])).

tff(c_491,plain,(
    ! [A_140,C_141,B_142] :
      ( r2_hidden(k2_mcart_1(A_140),C_141)
      | ~ r2_hidden(A_140,k2_zfmisc_1(B_142,C_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_493,plain,(
    ! [A_140,C_10,A_8,B_9] :
      ( r2_hidden(k2_mcart_1(A_140),C_10)
      | ~ r2_hidden(A_140,k3_zfmisc_1(A_8,B_9,C_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_491])).

tff(c_1369,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_1364,c_493])).

tff(c_1375,plain,(
    r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1295,c_1369])).

tff(c_1377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1089,c_1375])).

tff(c_1378,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1293])).

tff(c_1382,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1378])).

tff(c_1388,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1382,c_6])).

tff(c_1390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1388])).

tff(c_1391,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1378])).

tff(c_1399,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1391,c_6])).

tff(c_1401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_1399])).

tff(c_1402,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1404,plain,(
    ! [A_337,C_338,B_339] :
      ( r2_hidden(k2_mcart_1(A_337),C_338)
      | ~ r2_hidden(A_337,k2_zfmisc_1(B_339,C_338)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1481,plain,(
    ! [B_363,C_364] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_363,C_364))),C_364)
      | v1_xboole_0(k2_zfmisc_1(B_363,C_364)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1404])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1503,plain,(
    ! [C_364,B_363] :
      ( ~ v1_xboole_0(C_364)
      | v1_xboole_0(k2_zfmisc_1(B_363,C_364)) ) ),
    inference(resolution,[status(thm)],[c_1481,c_2])).

tff(c_1411,plain,(
    ! [A_340,B_341,C_342] :
      ( r2_hidden(k1_mcart_1(A_340),B_341)
      | ~ r2_hidden(A_340,k2_zfmisc_1(B_341,C_342)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1440,plain,(
    ! [B_351,C_352] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_351,C_352))),B_351)
      | v1_xboole_0(k2_zfmisc_1(B_351,C_352)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1411])).

tff(c_1468,plain,(
    ! [B_353,C_354] :
      ( ~ v1_xboole_0(B_353)
      | v1_xboole_0(k2_zfmisc_1(B_353,C_354)) ) ),
    inference(resolution,[status(thm)],[c_1440,c_2])).

tff(c_1474,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | v1_xboole_0(k3_zfmisc_1(A_8,B_9,C_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1468])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13,D_14] : k2_zfmisc_1(k3_zfmisc_1(A_11,B_12,C_13),D_14) = k4_zfmisc_1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1553,plain,(
    ! [A_384,B_385,C_386,D_387] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_384,B_385,C_386))
      | v1_xboole_0(k4_zfmisc_1(A_384,B_385,C_386,D_387)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1468])).

tff(c_48,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_28,c_2])).

tff(c_1557,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_1553,c_48])).

tff(c_1565,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1474,c_1557])).

tff(c_1569,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1503,c_1565])).

tff(c_1576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_1569])).

tff(c_1577,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_1580,plain,(
    ! [A_388,C_389,B_390] :
      ( r2_hidden(k2_mcart_1(A_388),C_389)
      | ~ r2_hidden(A_388,k2_zfmisc_1(B_390,C_389)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1657,plain,(
    ! [B_414,C_415] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_414,C_415))),C_415)
      | v1_xboole_0(k2_zfmisc_1(B_414,C_415)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1580])).

tff(c_1682,plain,(
    ! [C_416,B_417] :
      ( ~ v1_xboole_0(C_416)
      | v1_xboole_0(k2_zfmisc_1(B_417,C_416)) ) ),
    inference(resolution,[status(thm)],[c_1657,c_2])).

tff(c_1697,plain,(
    ! [D_421,A_422,B_423,C_424] :
      ( ~ v1_xboole_0(D_421)
      | v1_xboole_0(k4_zfmisc_1(A_422,B_423,C_424,D_421)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1682])).

tff(c_1700,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_1697,c_48])).

tff(c_1704,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1577,c_1700])).

tff(c_1705,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_1732,plain,(
    ! [A_431,B_432,C_433] :
      ( r2_hidden(k1_mcart_1(A_431),B_432)
      | ~ r2_hidden(A_431,k2_zfmisc_1(B_432,C_433)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1819,plain,(
    ! [B_463,C_464] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_463,C_464))),B_463)
      | v1_xboole_0(k2_zfmisc_1(B_463,C_464)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1732])).

tff(c_1848,plain,(
    ! [B_463,C_464] :
      ( ~ v1_xboole_0(B_463)
      | v1_xboole_0(k2_zfmisc_1(B_463,C_464)) ) ),
    inference(resolution,[status(thm)],[c_1819,c_2])).

tff(c_1856,plain,(
    ! [B_470,C_471] :
      ( ~ v1_xboole_0(B_470)
      | v1_xboole_0(k2_zfmisc_1(B_470,C_471)) ) ),
    inference(resolution,[status(thm)],[c_1819,c_2])).

tff(c_1862,plain,(
    ! [A_8,B_9,C_10] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_8,B_9))
      | v1_xboole_0(k3_zfmisc_1(A_8,B_9,C_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1856])).

tff(c_1864,plain,(
    ! [A_475,B_476,C_477,D_478] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_475,B_476,C_477))
      | v1_xboole_0(k4_zfmisc_1(A_475,B_476,C_477,D_478)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1856])).

tff(c_1868,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_1864,c_48])).

tff(c_1884,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1862,c_1868])).

tff(c_1888,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1848,c_1884])).

tff(c_1895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1705,c_1888])).

tff(c_1896,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1917,plain,(
    ! [A_482,C_483,B_484] :
      ( r2_hidden(k2_mcart_1(A_482),C_483)
      | ~ r2_hidden(A_482,k2_zfmisc_1(B_484,C_483)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2014,plain,(
    ! [B_518,C_519] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_518,C_519))),C_519)
      | v1_xboole_0(k2_zfmisc_1(B_518,C_519)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1917])).

tff(c_2043,plain,(
    ! [C_520,B_521] :
      ( ~ v1_xboole_0(C_520)
      | v1_xboole_0(k2_zfmisc_1(B_521,C_520)) ) ),
    inference(resolution,[status(thm)],[c_2014,c_2])).

tff(c_2049,plain,(
    ! [C_10,A_8,B_9] :
      ( ~ v1_xboole_0(C_10)
      | v1_xboole_0(k3_zfmisc_1(A_8,B_9,C_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2043])).

tff(c_1924,plain,(
    ! [A_485,B_486,C_487] :
      ( r2_hidden(k1_mcart_1(A_485),B_486)
      | ~ r2_hidden(A_485,k2_zfmisc_1(B_486,C_487)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1957,plain,(
    ! [B_501,C_502] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_501,C_502))),B_501)
      | v1_xboole_0(k2_zfmisc_1(B_501,C_502)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1924])).

tff(c_1985,plain,(
    ! [B_503,C_504] :
      ( ~ v1_xboole_0(B_503)
      | v1_xboole_0(k2_zfmisc_1(B_503,C_504)) ) ),
    inference(resolution,[status(thm)],[c_1957,c_2])).

tff(c_2064,plain,(
    ! [A_529,B_530,C_531,D_532] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_529,B_530,C_531))
      | v1_xboole_0(k4_zfmisc_1(A_529,B_530,C_531,D_532)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1985])).

tff(c_2068,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_2064,c_48])).

tff(c_2077,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2049,c_2068])).

tff(c_2084,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1896,c_2077])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.75  
% 4.13/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.75  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4
% 4.13/1.75  
% 4.13/1.75  %Foreground sorts:
% 4.13/1.75  
% 4.13/1.75  
% 4.13/1.75  %Background operators:
% 4.13/1.75  
% 4.13/1.75  
% 4.13/1.75  %Foreground operators:
% 4.13/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.75  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.13/1.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.13/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.13/1.75  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 4.13/1.75  tff('#skF_7', type, '#skF_7': $i).
% 4.13/1.75  tff('#skF_10', type, '#skF_10': $i).
% 4.13/1.75  tff('#skF_5', type, '#skF_5': $i).
% 4.13/1.75  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.13/1.75  tff('#skF_6', type, '#skF_6': $i).
% 4.13/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.13/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.13/1.75  tff('#skF_9', type, '#skF_9': $i).
% 4.13/1.75  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.13/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.13/1.75  tff('#skF_8', type, '#skF_8': $i).
% 4.13/1.75  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.13/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.75  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.13/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.13/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.13/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.75  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.13/1.75  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.13/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.13/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.13/1.75  
% 4.13/1.78  tff(f_99, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(A)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(B)) => (![G]: (m1_subset_1(G, k1_zfmisc_1(C)) => (![H]: (m1_subset_1(H, k1_zfmisc_1(D)) => (![I]: (m1_subset_1(I, k4_zfmisc_1(A, B, C, D)) => (r2_hidden(I, k4_zfmisc_1(E, F, G, H)) => (((r2_hidden(k8_mcart_1(A, B, C, D, I), E) & r2_hidden(k9_mcart_1(A, B, C, D, I), F)) & r2_hidden(k10_mcart_1(A, B, C, D, I), G)) & r2_hidden(k11_mcart_1(A, B, C, D, I), H))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_mcart_1)).
% 4.13/1.78  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.13/1.78  tff(f_43, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 4.13/1.78  tff(f_49, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.13/1.78  tff(f_74, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 4.13/1.78  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.13/1.78  tff(f_41, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.13/1.78  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.13/1.78  tff(c_32, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.13/1.78  tff(c_49, plain, (![B_53, A_54]: (v1_xboole_0(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.13/1.78  tff(c_63, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_32, c_49])).
% 4.13/1.78  tff(c_83, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_63])).
% 4.13/1.78  tff(c_34, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.13/1.78  tff(c_62, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_49])).
% 4.13/1.78  tff(c_66, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 4.13/1.78  tff(c_36, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.13/1.78  tff(c_64, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_49])).
% 4.13/1.78  tff(c_84, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_64])).
% 4.13/1.78  tff(c_28, plain, (r2_hidden('#skF_10', k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.13/1.78  tff(c_511, plain, (![A_150, B_151, C_152, D_153]: (k2_zfmisc_1(k3_zfmisc_1(A_150, B_151, C_152), D_153)=k4_zfmisc_1(A_150, B_151, C_152, D_153))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.13/1.78  tff(c_14, plain, (![A_15, C_17, B_16]: (r2_hidden(k2_mcart_1(A_15), C_17) | ~r2_hidden(A_15, k2_zfmisc_1(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.13/1.78  tff(c_577, plain, (![A_174, D_170, B_171, C_172, A_173]: (r2_hidden(k2_mcart_1(A_173), D_170) | ~r2_hidden(A_173, k4_zfmisc_1(A_174, B_171, C_172, D_170)))), inference(superposition, [status(thm), theory('equality')], [c_511, c_14])).
% 4.13/1.78  tff(c_587, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_28, c_577])).
% 4.13/1.78  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.13/1.78  tff(c_65, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_49])).
% 4.13/1.78  tff(c_67, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_65])).
% 4.13/1.78  tff(c_30, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.13/1.78  tff(c_552, plain, (![C_158, E_156, D_159, A_157, B_160]: (k11_mcart_1(A_157, B_160, C_158, D_159, E_156)=k2_mcart_1(E_156) | ~m1_subset_1(E_156, k4_zfmisc_1(A_157, B_160, C_158, D_159)) | k1_xboole_0=D_159 | k1_xboole_0=C_158 | k1_xboole_0=B_160 | k1_xboole_0=A_157)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.13/1.78  tff(c_556, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_552])).
% 4.13/1.78  tff(c_570, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_556])).
% 4.13/1.78  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.13/1.78  tff(c_572, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_570, c_6])).
% 4.13/1.78  tff(c_574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_572])).
% 4.13/1.78  tff(c_575, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_556])).
% 4.13/1.78  tff(c_640, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_575])).
% 4.13/1.78  tff(c_26, plain, (~r2_hidden(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9') | ~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8') | ~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7') | ~r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.13/1.78  tff(c_85, plain, (~r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(splitLeft, [status(thm)], [c_26])).
% 4.13/1.78  tff(c_154, plain, (![C_81, B_83, E_79, A_80, D_82]: (k11_mcart_1(A_80, B_83, C_81, D_82, E_79)=k2_mcart_1(E_79) | ~m1_subset_1(E_79, k4_zfmisc_1(A_80, B_83, C_81, D_82)) | k1_xboole_0=D_82 | k1_xboole_0=C_81 | k1_xboole_0=B_83 | k1_xboole_0=A_80)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.13/1.78  tff(c_158, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_154])).
% 4.13/1.78  tff(c_230, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_158])).
% 4.13/1.78  tff(c_233, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_230, c_6])).
% 4.13/1.78  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_233])).
% 4.13/1.78  tff(c_237, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_158])).
% 4.13/1.78  tff(c_212, plain, (![A_96, E_95, B_99, C_97, D_98]: (k2_mcart_1(k1_mcart_1(E_95))=k10_mcart_1(A_96, B_99, C_97, D_98, E_95) | ~m1_subset_1(E_95, k4_zfmisc_1(A_96, B_99, C_97, D_98)) | k1_xboole_0=D_98 | k1_xboole_0=C_97 | k1_xboole_0=B_99 | k1_xboole_0=A_96)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.13/1.78  tff(c_216, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_212])).
% 4.13/1.78  tff(c_288, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_237, c_216])).
% 4.13/1.78  tff(c_289, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_288])).
% 4.13/1.78  tff(c_294, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_289, c_6])).
% 4.13/1.78  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_294])).
% 4.13/1.78  tff(c_298, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_288])).
% 4.13/1.78  tff(c_318, plain, (![B_126, E_122, A_123, D_125, C_124]: (k9_mcart_1(A_123, B_126, C_124, D_125, E_122)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_122))) | ~m1_subset_1(E_122, k4_zfmisc_1(A_123, B_126, C_124, D_125)) | k1_xboole_0=D_125 | k1_xboole_0=C_124 | k1_xboole_0=B_126 | k1_xboole_0=A_123)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.13/1.78  tff(c_320, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_318])).
% 4.13/1.78  tff(c_323, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_237, c_298, c_320])).
% 4.13/1.78  tff(c_444, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_323])).
% 4.13/1.78  tff(c_451, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_444, c_6])).
% 4.13/1.78  tff(c_453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_451])).
% 4.13/1.78  tff(c_455, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_323])).
% 4.13/1.78  tff(c_254, plain, (![A_110, D_112, C_111, B_113, E_109]: (k8_mcart_1(A_110, B_113, C_111, D_112, E_109)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_109))) | ~m1_subset_1(E_109, k4_zfmisc_1(A_110, B_113, C_111, D_112)) | k1_xboole_0=D_112 | k1_xboole_0=C_111 | k1_xboole_0=B_113 | k1_xboole_0=A_110)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.13/1.78  tff(c_256, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_254])).
% 4.13/1.78  tff(c_259, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_237, c_256])).
% 4.13/1.78  tff(c_460, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_298, c_455, c_259])).
% 4.13/1.78  tff(c_461, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_460])).
% 4.13/1.78  tff(c_469, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_6])).
% 4.13/1.78  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_469])).
% 4.13/1.78  tff(c_472, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_460])).
% 4.13/1.78  tff(c_105, plain, (![A_68, B_69, C_70, D_71]: (k2_zfmisc_1(k3_zfmisc_1(A_68, B_69, C_70), D_71)=k4_zfmisc_1(A_68, B_69, C_70, D_71))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.13/1.78  tff(c_16, plain, (![A_15, B_16, C_17]: (r2_hidden(k1_mcart_1(A_15), B_16) | ~r2_hidden(A_15, k2_zfmisc_1(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.13/1.78  tff(c_403, plain, (![B_137, C_136, A_138, A_139, D_135]: (r2_hidden(k1_mcart_1(A_138), k3_zfmisc_1(A_139, B_137, C_136)) | ~r2_hidden(A_138, k4_zfmisc_1(A_139, B_137, C_136, D_135)))), inference(superposition, [status(thm), theory('equality')], [c_105, c_16])).
% 4.13/1.78  tff(c_421, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_28, c_403])).
% 4.13/1.78  tff(c_10, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10)=k3_zfmisc_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.13/1.78  tff(c_93, plain, (![A_61, B_62, C_63]: (r2_hidden(k1_mcart_1(A_61), B_62) | ~r2_hidden(A_61, k2_zfmisc_1(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.13/1.78  tff(c_95, plain, (![A_61, A_8, B_9, C_10]: (r2_hidden(k1_mcart_1(A_61), k2_zfmisc_1(A_8, B_9)) | ~r2_hidden(A_61, k3_zfmisc_1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_93])).
% 4.13/1.78  tff(c_430, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_421, c_95])).
% 4.13/1.78  tff(c_441, plain, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))), '#skF_6')), inference(resolution, [status(thm)], [c_430, c_16])).
% 4.13/1.78  tff(c_482, plain, (r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_472, c_441])).
% 4.13/1.78  tff(c_484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_482])).
% 4.13/1.78  tff(c_485, plain, (~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7') | ~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8') | ~r2_hidden(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_26])).
% 4.13/1.78  tff(c_498, plain, (~r2_hidden(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_485])).
% 4.13/1.78  tff(c_641, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_640, c_498])).
% 4.13/1.78  tff(c_644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_587, c_641])).
% 4.13/1.78  tff(c_645, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_575])).
% 4.13/1.78  tff(c_647, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_645])).
% 4.13/1.78  tff(c_651, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_647, c_6])).
% 4.13/1.78  tff(c_653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_651])).
% 4.13/1.78  tff(c_654, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_645])).
% 4.13/1.78  tff(c_656, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_654])).
% 4.13/1.78  tff(c_668, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_656, c_6])).
% 4.13/1.78  tff(c_670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_668])).
% 4.13/1.78  tff(c_671, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_654])).
% 4.13/1.78  tff(c_678, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_671, c_6])).
% 4.13/1.78  tff(c_680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_678])).
% 4.13/1.78  tff(c_681, plain, (~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8') | ~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(splitRight, [status(thm)], [c_485])).
% 4.13/1.78  tff(c_740, plain, (~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(splitLeft, [status(thm)], [c_681])).
% 4.13/1.78  tff(c_749, plain, (![B_214, E_210, C_212, A_211, D_213]: (k11_mcart_1(A_211, B_214, C_212, D_213, E_210)=k2_mcart_1(E_210) | ~m1_subset_1(E_210, k4_zfmisc_1(A_211, B_214, C_212, D_213)) | k1_xboole_0=D_213 | k1_xboole_0=C_212 | k1_xboole_0=B_214 | k1_xboole_0=A_211)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.13/1.78  tff(c_753, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_749])).
% 4.13/1.78  tff(c_833, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_753])).
% 4.13/1.78  tff(c_836, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_833, c_6])).
% 4.13/1.78  tff(c_838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_836])).
% 4.13/1.78  tff(c_840, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_753])).
% 4.13/1.78  tff(c_814, plain, (![D_231, C_230, A_229, E_228, B_232]: (k2_mcart_1(k1_mcart_1(E_228))=k10_mcart_1(A_229, B_232, C_230, D_231, E_228) | ~m1_subset_1(E_228, k4_zfmisc_1(A_229, B_232, C_230, D_231)) | k1_xboole_0=D_231 | k1_xboole_0=C_230 | k1_xboole_0=B_232 | k1_xboole_0=A_229)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.13/1.78  tff(c_818, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_814])).
% 4.13/1.78  tff(c_901, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_840, c_818])).
% 4.13/1.78  tff(c_902, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_901])).
% 4.13/1.78  tff(c_907, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_902, c_6])).
% 4.13/1.78  tff(c_909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_907])).
% 4.13/1.78  tff(c_911, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_901])).
% 4.13/1.78  tff(c_946, plain, (![E_256, A_257, D_259, C_258, B_260]: (k9_mcart_1(A_257, B_260, C_258, D_259, E_256)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_256))) | ~m1_subset_1(E_256, k4_zfmisc_1(A_257, B_260, C_258, D_259)) | k1_xboole_0=D_259 | k1_xboole_0=C_258 | k1_xboole_0=B_260 | k1_xboole_0=A_257)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.13/1.78  tff(c_948, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_946])).
% 4.13/1.78  tff(c_951, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_840, c_911, c_948])).
% 4.13/1.78  tff(c_1053, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_951])).
% 4.13/1.78  tff(c_1060, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_6])).
% 4.13/1.78  tff(c_1062, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1060])).
% 4.13/1.78  tff(c_1064, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_951])).
% 4.13/1.78  tff(c_849, plain, (![A_241, D_243, B_244, C_242, E_240]: (k8_mcart_1(A_241, B_244, C_242, D_243, E_240)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_240))) | ~m1_subset_1(E_240, k4_zfmisc_1(A_241, B_244, C_242, D_243)) | k1_xboole_0=D_243 | k1_xboole_0=C_242 | k1_xboole_0=B_244 | k1_xboole_0=A_241)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.13/1.78  tff(c_851, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_849])).
% 4.13/1.78  tff(c_854, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_840, c_851])).
% 4.13/1.78  tff(c_1065, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_911, c_1064, c_854])).
% 4.13/1.78  tff(c_1066, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_1065])).
% 4.13/1.78  tff(c_1074, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_6])).
% 4.13/1.78  tff(c_1076, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_1074])).
% 4.13/1.78  tff(c_1078, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_1065])).
% 4.13/1.78  tff(c_1063, plain, (k1_xboole_0='#skF_5' | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_951])).
% 4.13/1.78  tff(c_1085, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_1078, c_1063])).
% 4.13/1.78  tff(c_699, plain, (![A_199, B_200, C_201, D_202]: (k2_zfmisc_1(k3_zfmisc_1(A_199, B_200, C_201), D_202)=k4_zfmisc_1(A_199, B_200, C_201, D_202))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.13/1.78  tff(c_992, plain, (![A_268, A_269, D_267, B_266, C_270]: (r2_hidden(k1_mcart_1(A_269), k3_zfmisc_1(A_268, B_266, C_270)) | ~r2_hidden(A_269, k4_zfmisc_1(A_268, B_266, C_270, D_267)))), inference(superposition, [status(thm), theory('equality')], [c_699, c_16])).
% 4.13/1.78  tff(c_1010, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_28, c_992])).
% 4.13/1.78  tff(c_687, plain, (![A_192, B_193, C_194]: (r2_hidden(k1_mcart_1(A_192), B_193) | ~r2_hidden(A_192, k2_zfmisc_1(B_193, C_194)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.13/1.78  tff(c_689, plain, (![A_192, A_8, B_9, C_10]: (r2_hidden(k1_mcart_1(A_192), k2_zfmisc_1(A_8, B_9)) | ~r2_hidden(A_192, k3_zfmisc_1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_687])).
% 4.13/1.78  tff(c_1019, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1010, c_689])).
% 4.13/1.78  tff(c_1031, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))), '#skF_7')), inference(resolution, [status(thm)], [c_1019, c_14])).
% 4.13/1.78  tff(c_1086, plain, (r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_1031])).
% 4.13/1.78  tff(c_1088, plain, $false, inference(negUnitSimplification, [status(thm)], [c_740, c_1086])).
% 4.13/1.78  tff(c_1089, plain, (~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_681])).
% 4.13/1.78  tff(c_1103, plain, (![A_277, B_280, C_278, E_276, D_279]: (k11_mcart_1(A_277, B_280, C_278, D_279, E_276)=k2_mcart_1(E_276) | ~m1_subset_1(E_276, k4_zfmisc_1(A_277, B_280, C_278, D_279)) | k1_xboole_0=D_279 | k1_xboole_0=C_278 | k1_xboole_0=B_280 | k1_xboole_0=A_277)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.13/1.78  tff(c_1107, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_1103])).
% 4.13/1.78  tff(c_1187, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1107])).
% 4.13/1.78  tff(c_1190, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1187, c_6])).
% 4.13/1.78  tff(c_1192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_1190])).
% 4.13/1.78  tff(c_1194, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1107])).
% 4.13/1.78  tff(c_1165, plain, (![B_301, C_299, E_297, D_300, A_298]: (k2_mcart_1(k1_mcart_1(E_297))=k10_mcart_1(A_298, B_301, C_299, D_300, E_297) | ~m1_subset_1(E_297, k4_zfmisc_1(A_298, B_301, C_299, D_300)) | k1_xboole_0=D_300 | k1_xboole_0=C_299 | k1_xboole_0=B_301 | k1_xboole_0=A_298)), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.13/1.78  tff(c_1169, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_1165])).
% 4.13/1.78  tff(c_1284, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1194, c_1169])).
% 4.53/1.78  tff(c_1285, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1284])).
% 4.53/1.78  tff(c_1290, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1285, c_6])).
% 4.53/1.78  tff(c_1292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_1290])).
% 4.53/1.78  tff(c_1293, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_1284])).
% 4.53/1.78  tff(c_1295, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitLeft, [status(thm)], [c_1293])).
% 4.53/1.78  tff(c_1346, plain, (![D_333, B_332, A_334, C_336, A_335]: (r2_hidden(k1_mcart_1(A_335), k3_zfmisc_1(A_334, B_332, C_336)) | ~r2_hidden(A_335, k4_zfmisc_1(A_334, B_332, C_336, D_333)))), inference(superposition, [status(thm), theory('equality')], [c_699, c_16])).
% 4.53/1.78  tff(c_1364, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_28, c_1346])).
% 4.53/1.78  tff(c_491, plain, (![A_140, C_141, B_142]: (r2_hidden(k2_mcart_1(A_140), C_141) | ~r2_hidden(A_140, k2_zfmisc_1(B_142, C_141)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.53/1.78  tff(c_493, plain, (![A_140, C_10, A_8, B_9]: (r2_hidden(k2_mcart_1(A_140), C_10) | ~r2_hidden(A_140, k3_zfmisc_1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_491])).
% 4.53/1.78  tff(c_1369, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_1364, c_493])).
% 4.53/1.78  tff(c_1375, plain, (r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1295, c_1369])).
% 4.53/1.78  tff(c_1377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1089, c_1375])).
% 4.53/1.78  tff(c_1378, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1293])).
% 4.53/1.78  tff(c_1382, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1378])).
% 4.53/1.78  tff(c_1388, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1382, c_6])).
% 4.53/1.78  tff(c_1390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1388])).
% 4.53/1.78  tff(c_1391, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1378])).
% 4.53/1.78  tff(c_1399, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1391, c_6])).
% 4.53/1.78  tff(c_1401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_1399])).
% 4.53/1.78  tff(c_1402, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_64])).
% 4.53/1.78  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.53/1.78  tff(c_1404, plain, (![A_337, C_338, B_339]: (r2_hidden(k2_mcart_1(A_337), C_338) | ~r2_hidden(A_337, k2_zfmisc_1(B_339, C_338)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.53/1.78  tff(c_1481, plain, (![B_363, C_364]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_363, C_364))), C_364) | v1_xboole_0(k2_zfmisc_1(B_363, C_364)))), inference(resolution, [status(thm)], [c_4, c_1404])).
% 4.53/1.78  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.53/1.78  tff(c_1503, plain, (![C_364, B_363]: (~v1_xboole_0(C_364) | v1_xboole_0(k2_zfmisc_1(B_363, C_364)))), inference(resolution, [status(thm)], [c_1481, c_2])).
% 4.53/1.78  tff(c_1411, plain, (![A_340, B_341, C_342]: (r2_hidden(k1_mcart_1(A_340), B_341) | ~r2_hidden(A_340, k2_zfmisc_1(B_341, C_342)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.53/1.78  tff(c_1440, plain, (![B_351, C_352]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_351, C_352))), B_351) | v1_xboole_0(k2_zfmisc_1(B_351, C_352)))), inference(resolution, [status(thm)], [c_4, c_1411])).
% 4.53/1.78  tff(c_1468, plain, (![B_353, C_354]: (~v1_xboole_0(B_353) | v1_xboole_0(k2_zfmisc_1(B_353, C_354)))), inference(resolution, [status(thm)], [c_1440, c_2])).
% 4.53/1.78  tff(c_1474, plain, (![A_8, B_9, C_10]: (~v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | v1_xboole_0(k3_zfmisc_1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1468])).
% 4.53/1.78  tff(c_12, plain, (![A_11, B_12, C_13, D_14]: (k2_zfmisc_1(k3_zfmisc_1(A_11, B_12, C_13), D_14)=k4_zfmisc_1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.53/1.78  tff(c_1553, plain, (![A_384, B_385, C_386, D_387]: (~v1_xboole_0(k3_zfmisc_1(A_384, B_385, C_386)) | v1_xboole_0(k4_zfmisc_1(A_384, B_385, C_386, D_387)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1468])).
% 4.53/1.78  tff(c_48, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_28, c_2])).
% 4.53/1.78  tff(c_1557, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_1553, c_48])).
% 4.53/1.78  tff(c_1565, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1474, c_1557])).
% 4.53/1.78  tff(c_1569, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_1503, c_1565])).
% 4.53/1.78  tff(c_1576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1402, c_1569])).
% 4.53/1.78  tff(c_1577, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_63])).
% 4.53/1.78  tff(c_1580, plain, (![A_388, C_389, B_390]: (r2_hidden(k2_mcart_1(A_388), C_389) | ~r2_hidden(A_388, k2_zfmisc_1(B_390, C_389)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.53/1.78  tff(c_1657, plain, (![B_414, C_415]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_414, C_415))), C_415) | v1_xboole_0(k2_zfmisc_1(B_414, C_415)))), inference(resolution, [status(thm)], [c_4, c_1580])).
% 4.53/1.78  tff(c_1682, plain, (![C_416, B_417]: (~v1_xboole_0(C_416) | v1_xboole_0(k2_zfmisc_1(B_417, C_416)))), inference(resolution, [status(thm)], [c_1657, c_2])).
% 4.53/1.78  tff(c_1697, plain, (![D_421, A_422, B_423, C_424]: (~v1_xboole_0(D_421) | v1_xboole_0(k4_zfmisc_1(A_422, B_423, C_424, D_421)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1682])).
% 4.53/1.78  tff(c_1700, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_1697, c_48])).
% 4.53/1.78  tff(c_1704, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1577, c_1700])).
% 4.53/1.78  tff(c_1705, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_65])).
% 4.53/1.78  tff(c_1732, plain, (![A_431, B_432, C_433]: (r2_hidden(k1_mcart_1(A_431), B_432) | ~r2_hidden(A_431, k2_zfmisc_1(B_432, C_433)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.53/1.78  tff(c_1819, plain, (![B_463, C_464]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_463, C_464))), B_463) | v1_xboole_0(k2_zfmisc_1(B_463, C_464)))), inference(resolution, [status(thm)], [c_4, c_1732])).
% 4.53/1.78  tff(c_1848, plain, (![B_463, C_464]: (~v1_xboole_0(B_463) | v1_xboole_0(k2_zfmisc_1(B_463, C_464)))), inference(resolution, [status(thm)], [c_1819, c_2])).
% 4.53/1.78  tff(c_1856, plain, (![B_470, C_471]: (~v1_xboole_0(B_470) | v1_xboole_0(k2_zfmisc_1(B_470, C_471)))), inference(resolution, [status(thm)], [c_1819, c_2])).
% 4.53/1.78  tff(c_1862, plain, (![A_8, B_9, C_10]: (~v1_xboole_0(k2_zfmisc_1(A_8, B_9)) | v1_xboole_0(k3_zfmisc_1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1856])).
% 4.53/1.78  tff(c_1864, plain, (![A_475, B_476, C_477, D_478]: (~v1_xboole_0(k3_zfmisc_1(A_475, B_476, C_477)) | v1_xboole_0(k4_zfmisc_1(A_475, B_476, C_477, D_478)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1856])).
% 4.53/1.78  tff(c_1868, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_1864, c_48])).
% 4.53/1.78  tff(c_1884, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1862, c_1868])).
% 4.53/1.78  tff(c_1888, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1848, c_1884])).
% 4.53/1.78  tff(c_1895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1705, c_1888])).
% 4.53/1.78  tff(c_1896, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_62])).
% 4.53/1.78  tff(c_1917, plain, (![A_482, C_483, B_484]: (r2_hidden(k2_mcart_1(A_482), C_483) | ~r2_hidden(A_482, k2_zfmisc_1(B_484, C_483)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.53/1.78  tff(c_2014, plain, (![B_518, C_519]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_518, C_519))), C_519) | v1_xboole_0(k2_zfmisc_1(B_518, C_519)))), inference(resolution, [status(thm)], [c_4, c_1917])).
% 4.53/1.78  tff(c_2043, plain, (![C_520, B_521]: (~v1_xboole_0(C_520) | v1_xboole_0(k2_zfmisc_1(B_521, C_520)))), inference(resolution, [status(thm)], [c_2014, c_2])).
% 4.53/1.78  tff(c_2049, plain, (![C_10, A_8, B_9]: (~v1_xboole_0(C_10) | v1_xboole_0(k3_zfmisc_1(A_8, B_9, C_10)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2043])).
% 4.53/1.78  tff(c_1924, plain, (![A_485, B_486, C_487]: (r2_hidden(k1_mcart_1(A_485), B_486) | ~r2_hidden(A_485, k2_zfmisc_1(B_486, C_487)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.53/1.78  tff(c_1957, plain, (![B_501, C_502]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_501, C_502))), B_501) | v1_xboole_0(k2_zfmisc_1(B_501, C_502)))), inference(resolution, [status(thm)], [c_4, c_1924])).
% 4.53/1.78  tff(c_1985, plain, (![B_503, C_504]: (~v1_xboole_0(B_503) | v1_xboole_0(k2_zfmisc_1(B_503, C_504)))), inference(resolution, [status(thm)], [c_1957, c_2])).
% 4.53/1.78  tff(c_2064, plain, (![A_529, B_530, C_531, D_532]: (~v1_xboole_0(k3_zfmisc_1(A_529, B_530, C_531)) | v1_xboole_0(k4_zfmisc_1(A_529, B_530, C_531, D_532)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1985])).
% 4.53/1.78  tff(c_2068, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_2064, c_48])).
% 4.53/1.78  tff(c_2077, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_2049, c_2068])).
% 4.53/1.78  tff(c_2084, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1896, c_2077])).
% 4.53/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.53/1.78  
% 4.53/1.78  Inference rules
% 4.53/1.78  ----------------------
% 4.53/1.78  #Ref     : 0
% 4.53/1.78  #Sup     : 445
% 4.53/1.78  #Fact    : 0
% 4.53/1.78  #Define  : 0
% 4.53/1.78  #Split   : 43
% 4.53/1.78  #Chain   : 0
% 4.53/1.78  #Close   : 0
% 4.53/1.78  
% 4.53/1.78  Ordering : KBO
% 4.53/1.78  
% 4.53/1.78  Simplification rules
% 4.53/1.78  ----------------------
% 4.53/1.78  #Subsume      : 52
% 4.53/1.78  #Demod        : 384
% 4.53/1.78  #Tautology    : 53
% 4.53/1.78  #SimpNegUnit  : 41
% 4.53/1.78  #BackRed      : 100
% 4.53/1.78  
% 4.53/1.78  #Partial instantiations: 0
% 4.53/1.78  #Strategies tried      : 1
% 4.53/1.78  
% 4.53/1.78  Timing (in seconds)
% 4.53/1.78  ----------------------
% 4.53/1.79  Preprocessing        : 0.32
% 4.53/1.79  Parsing              : 0.17
% 4.53/1.79  CNF conversion       : 0.03
% 4.53/1.79  Main loop            : 0.64
% 4.53/1.79  Inferencing          : 0.24
% 4.53/1.79  Reduction            : 0.20
% 4.53/1.79  Demodulation         : 0.14
% 4.53/1.79  BG Simplification    : 0.03
% 4.53/1.79  Subsumption          : 0.09
% 4.53/1.79  Abstraction          : 0.04
% 4.53/1.79  MUC search           : 0.00
% 4.53/1.79  Cooper               : 0.00
% 4.53/1.79  Total                : 1.05
% 4.53/1.79  Index Insertion      : 0.00
% 4.53/1.79  Index Deletion       : 0.00
% 4.53/1.79  Index Matching       : 0.00
% 4.53/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
