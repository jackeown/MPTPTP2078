%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:13 EST 2020

% Result     : Theorem 4.33s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 529 expanded)
%              Number of leaves         :   31 ( 183 expanded)
%              Depth                    :   12
%              Number of atoms          :  317 (1449 expanded)
%              Number of equality atoms :   92 ( 430 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_884,plain,(
    ! [A_173,B_174] :
      ( r2_hidden('#skF_1'(A_173,B_174),A_173)
      | r1_tarski(A_173,B_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_892,plain,(
    ! [A_173] : r1_tarski(A_173,A_173) ),
    inference(resolution,[status(thm)],[c_884,c_4])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_862,plain,(
    ! [A_169,B_170] :
      ( r1_tarski(A_169,B_170)
      | ~ m1_subset_1(A_169,k1_zfmisc_1(B_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_877,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_862])).

tff(c_30,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] : k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13) = k3_zfmisc_1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_934,plain,(
    ! [A_185,C_186,B_187] :
      ( r2_hidden(k2_mcart_1(A_185),C_186)
      | ~ r2_hidden(A_185,k2_zfmisc_1(B_187,C_186)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_964,plain,(
    ! [A_192,C_193,A_194,B_195] :
      ( r2_hidden(k2_mcart_1(A_192),C_193)
      | ~ r2_hidden(A_192,k3_zfmisc_1(A_194,B_195,C_193)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_934])).

tff(c_975,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_964])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_878,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_862])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1051,plain,(
    ! [A_201,B_202,C_203,D_204] :
      ( k7_mcart_1(A_201,B_202,C_203,D_204) = k2_mcart_1(D_204)
      | ~ m1_subset_1(D_204,k3_zfmisc_1(A_201,B_202,C_203))
      | k1_xboole_0 = C_203
      | k1_xboole_0 = B_202
      | k1_xboole_0 = A_201 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1055,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_1051])).

tff(c_1057,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1055])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_28,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_46,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    ! [A_42,B_43] :
      ( ~ r2_hidden('#skF_1'(A_42,B_43),B_43)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_47,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_47])).

tff(c_63,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_47])).

tff(c_134,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( k7_mcart_1(A_64,B_65,C_66,D_67) = k2_mcart_1(D_67)
      | ~ m1_subset_1(D_67,k3_zfmisc_1(A_64,B_65,C_66))
      | k1_xboole_0 = C_66
      | k1_xboole_0 = B_65
      | k1_xboole_0 = A_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_138,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_134])).

tff(c_166,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_168,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_8])).

tff(c_83,plain,(
    ! [C_47,B_48,A_49] :
      ( r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_294,plain,(
    ! [A_93,B_94,B_95] :
      ( r2_hidden('#skF_1'(A_93,B_94),B_95)
      | ~ r1_tarski(A_93,B_95)
      | r1_tarski(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_83])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_319,plain,(
    ! [B_96,A_97,B_98] :
      ( ~ r1_tarski(B_96,'#skF_1'(A_97,B_98))
      | ~ r1_tarski(A_97,B_96)
      | r1_tarski(A_97,B_98) ) ),
    inference(resolution,[status(thm)],[c_294,c_14])).

tff(c_330,plain,(
    ! [A_99,B_100] :
      ( ~ r1_tarski(A_99,'#skF_2')
      | r1_tarski(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_168,c_319])).

tff(c_343,plain,(
    ! [B_100] : r1_tarski('#skF_5',B_100) ),
    inference(resolution,[status(thm)],[c_63,c_330])).

tff(c_105,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden(k1_mcart_1(A_53),B_54)
      | ~ r2_hidden(A_53,k2_zfmisc_1(B_54,C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_422,plain,(
    ! [A_114,A_115,B_116,C_117] :
      ( r2_hidden(k1_mcart_1(A_114),k2_zfmisc_1(A_115,B_116))
      | ~ r2_hidden(A_114,k3_zfmisc_1(A_115,B_116,C_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_105])).

tff(c_444,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_422])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] :
      ( r2_hidden(k1_mcart_1(A_14),B_15)
      | ~ r2_hidden(A_14,k2_zfmisc_1(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_455,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_444,c_20])).

tff(c_469,plain,(
    ~ r1_tarski('#skF_5',k1_mcart_1(k1_mcart_1('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_455,c_14])).

tff(c_476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_469])).

tff(c_478,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_558,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( k5_mcart_1(A_129,B_130,C_131,D_132) = k1_mcart_1(k1_mcart_1(D_132))
      | ~ m1_subset_1(D_132,k3_zfmisc_1(A_129,B_130,C_131))
      | k1_xboole_0 = C_131
      | k1_xboole_0 = B_130
      | k1_xboole_0 = A_129 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_561,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_558])).

tff(c_564,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_561])).

tff(c_645,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_564])).

tff(c_658,plain,(
    ! [A_149] : r1_tarski('#skF_3',A_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_8])).

tff(c_598,plain,(
    ! [A_141,B_142,B_143] :
      ( r2_hidden('#skF_1'(A_141,B_142),B_143)
      | ~ r1_tarski(A_141,B_143)
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_6,c_83])).

tff(c_622,plain,(
    ! [B_143,A_141,B_142] :
      ( ~ r1_tarski(B_143,'#skF_1'(A_141,B_142))
      | ~ r1_tarski(A_141,B_143)
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_598,c_14])).

tff(c_687,plain,(
    ! [A_150,B_151] :
      ( ~ r1_tarski(A_150,'#skF_3')
      | r1_tarski(A_150,B_151) ) ),
    inference(resolution,[status(thm)],[c_658,c_622])).

tff(c_700,plain,(
    ! [B_151] : r1_tarski('#skF_6',B_151) ),
    inference(resolution,[status(thm)],[c_62,c_687])).

tff(c_752,plain,(
    ! [A_158,A_159,B_160,C_161] :
      ( r2_hidden(k1_mcart_1(A_158),k2_zfmisc_1(A_159,B_160))
      | ~ r2_hidden(A_158,k3_zfmisc_1(A_159,B_160,C_161)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_105])).

tff(c_771,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_752])).

tff(c_18,plain,(
    ! [A_14,C_16,B_15] :
      ( r2_hidden(k2_mcart_1(A_14),C_16)
      | ~ r2_hidden(A_14,k2_zfmisc_1(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_781,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_771,c_18])).

tff(c_789,plain,(
    ~ r1_tarski('#skF_6',k2_mcart_1(k1_mcart_1('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_781,c_14])).

tff(c_796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_789])).

tff(c_798,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_564])).

tff(c_515,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k6_mcart_1(A_121,B_122,C_123,D_124) = k2_mcart_1(k1_mcart_1(D_124))
      | ~ m1_subset_1(D_124,k3_zfmisc_1(A_121,B_122,C_123))
      | k1_xboole_0 = C_123
      | k1_xboole_0 = B_122
      | k1_xboole_0 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_518,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_515])).

tff(c_521,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_518])).

tff(c_799,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_798,c_521])).

tff(c_800,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_799])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_61,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_47])).

tff(c_112,plain,(
    ! [A_56,C_57,B_58] :
      ( r2_hidden(k2_mcart_1(A_56),C_57)
      | ~ r2_hidden(A_56,k2_zfmisc_1(B_58,C_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_126,plain,(
    ! [A_60,C_61,A_62,B_63] :
      ( r2_hidden(k2_mcart_1(A_60),C_61)
      | ~ r2_hidden(A_60,k3_zfmisc_1(A_62,B_63,C_61)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_112])).

tff(c_133,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_126])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_146,plain,(
    ! [B_68] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_68)
      | ~ r1_tarski('#skF_7',B_68) ) ),
    inference(resolution,[status(thm)],[c_133,c_2])).

tff(c_490,plain,(
    ! [B_119,B_120] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_119)
      | ~ r1_tarski(B_120,B_119)
      | ~ r1_tarski('#skF_7',B_120) ) ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_498,plain,
    ( r2_hidden(k2_mcart_1('#skF_8'),'#skF_4')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_61,c_490])).

tff(c_506,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_498])).

tff(c_524,plain,(
    ! [B_125] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_125)
      | ~ r1_tarski('#skF_4',B_125) ) ),
    inference(resolution,[status(thm)],[c_506,c_2])).

tff(c_544,plain,(
    ! [B_126] :
      ( ~ r1_tarski(B_126,k2_mcart_1('#skF_8'))
      | ~ r1_tarski('#skF_4',B_126) ) ),
    inference(resolution,[status(thm)],[c_524,c_14])).

tff(c_554,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_544])).

tff(c_804,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_554])).

tff(c_812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_804])).

tff(c_814,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_799])).

tff(c_797,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_564])).

tff(c_819,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_814,c_797])).

tff(c_825,plain,(
    ! [A_165,A_166,B_167,C_168] :
      ( r2_hidden(k1_mcart_1(A_165),k2_zfmisc_1(A_166,B_167))
      | ~ r2_hidden(A_165,k3_zfmisc_1(A_166,B_167,C_168)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_105])).

tff(c_844,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_825])).

tff(c_848,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_844,c_20])).

tff(c_857,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_848])).

tff(c_859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_857])).

tff(c_861,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_894,plain,(
    ! [C_175,B_176,A_177] :
      ( r2_hidden(C_175,B_176)
      | ~ r2_hidden(C_175,A_177)
      | ~ r1_tarski(A_177,B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_948,plain,(
    ! [B_191] :
      ( r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),B_191)
      | ~ r1_tarski('#skF_5',B_191) ) ),
    inference(resolution,[status(thm)],[c_861,c_894])).

tff(c_1015,plain,(
    ! [B_198] :
      ( ~ r1_tarski(B_198,k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'))
      | ~ r1_tarski('#skF_5',B_198) ) ),
    inference(resolution,[status(thm)],[c_948,c_14])).

tff(c_1025,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_1015])).

tff(c_1059,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_1025])).

tff(c_1064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_1059])).

tff(c_1065,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1055])).

tff(c_1109,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1065])).

tff(c_860,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_983,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_860])).

tff(c_1110,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1109,c_983])).

tff(c_1113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_975,c_1110])).

tff(c_1114,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1065])).

tff(c_1116,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1114])).

tff(c_1123,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_8])).

tff(c_1163,plain,(
    ! [A_218,B_219,B_220] :
      ( r2_hidden('#skF_1'(A_218,B_219),B_220)
      | ~ r1_tarski(A_218,B_220)
      | r1_tarski(A_218,B_219) ) ),
    inference(resolution,[status(thm)],[c_6,c_894])).

tff(c_1216,plain,(
    ! [B_229,A_230,B_231] :
      ( ~ r1_tarski(B_229,'#skF_1'(A_230,B_231))
      | ~ r1_tarski(A_230,B_229)
      | r1_tarski(A_230,B_231) ) ),
    inference(resolution,[status(thm)],[c_1163,c_14])).

tff(c_1245,plain,(
    ! [A_236,B_237] :
      ( ~ r1_tarski(A_236,'#skF_3')
      | r1_tarski(A_236,B_237) ) ),
    inference(resolution,[status(thm)],[c_1123,c_1216])).

tff(c_1258,plain,(
    ! [B_237] : r1_tarski('#skF_6',B_237) ),
    inference(resolution,[status(thm)],[c_877,c_1245])).

tff(c_941,plain,(
    ! [A_188,B_189,C_190] :
      ( r2_hidden(k1_mcart_1(A_188),B_189)
      | ~ r2_hidden(A_188,k2_zfmisc_1(B_189,C_190)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1320,plain,(
    ! [A_247,A_248,B_249,C_250] :
      ( r2_hidden(k1_mcart_1(A_247),k2_zfmisc_1(A_248,B_249))
      | ~ r2_hidden(A_247,k3_zfmisc_1(A_248,B_249,C_250)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_941])).

tff(c_1346,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_1320])).

tff(c_1358,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1346,c_18])).

tff(c_1372,plain,(
    ~ r1_tarski('#skF_6',k2_mcart_1(k1_mcart_1('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_1358,c_14])).

tff(c_1379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1258,c_1372])).

tff(c_1380,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1114])).

tff(c_876,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_862])).

tff(c_984,plain,(
    ! [B_196] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_196)
      | ~ r1_tarski('#skF_7',B_196) ) ),
    inference(resolution,[status(thm)],[c_975,c_2])).

tff(c_1026,plain,(
    ! [B_199,B_200] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_199)
      | ~ r1_tarski(B_200,B_199)
      | ~ r1_tarski('#skF_7',B_200) ) ),
    inference(resolution,[status(thm)],[c_984,c_2])).

tff(c_1034,plain,
    ( r2_hidden(k2_mcart_1('#skF_8'),'#skF_4')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_876,c_1026])).

tff(c_1042,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_1034])).

tff(c_1068,plain,(
    ! [B_205] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_205)
      | ~ r1_tarski('#skF_4',B_205) ) ),
    inference(resolution,[status(thm)],[c_1042,c_2])).

tff(c_1095,plain,(
    ! [B_210] :
      ( ~ r1_tarski(B_210,k2_mcart_1('#skF_8'))
      | ~ r1_tarski('#skF_4',B_210) ) ),
    inference(resolution,[status(thm)],[c_1068,c_14])).

tff(c_1105,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_1095])).

tff(c_1384,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_1105])).

tff(c_1393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_1384])).

tff(c_1394,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_860])).

tff(c_1403,plain,(
    ! [A_251,B_252,C_253,D_254] :
      ( k7_mcart_1(A_251,B_252,C_253,D_254) = k2_mcart_1(D_254)
      | ~ m1_subset_1(D_254,k3_zfmisc_1(A_251,B_252,C_253))
      | k1_xboole_0 = C_253
      | k1_xboole_0 = B_252
      | k1_xboole_0 = A_251 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1407,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_1403])).

tff(c_1439,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1407])).

tff(c_1441,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_8])).

tff(c_1486,plain,(
    ! [B_263] :
      ( ~ r1_tarski(B_263,k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'))
      | ~ r1_tarski('#skF_5',B_263) ) ),
    inference(resolution,[status(thm)],[c_948,c_14])).

tff(c_1490,plain,(
    ~ r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_1441,c_1486])).

tff(c_1498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_1490])).

tff(c_1500,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1407])).

tff(c_1524,plain,(
    ! [A_267,B_268,C_269,D_270] :
      ( k6_mcart_1(A_267,B_268,C_269,D_270) = k2_mcart_1(k1_mcart_1(D_270))
      | ~ m1_subset_1(D_270,k3_zfmisc_1(A_267,B_268,C_269))
      | k1_xboole_0 = C_269
      | k1_xboole_0 = B_268
      | k1_xboole_0 = A_267 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1527,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_1524])).

tff(c_1530,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1500,c_1527])).

tff(c_1602,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1530])).

tff(c_1610,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1602,c_8])).

tff(c_1640,plain,(
    ! [A_284,B_285,B_286] :
      ( r2_hidden('#skF_1'(A_284,B_285),B_286)
      | ~ r1_tarski(A_284,B_286)
      | r1_tarski(A_284,B_285) ) ),
    inference(resolution,[status(thm)],[c_6,c_894])).

tff(c_1706,plain,(
    ! [B_298,A_299,B_300] :
      ( ~ r1_tarski(B_298,'#skF_1'(A_299,B_300))
      | ~ r1_tarski(A_299,B_298)
      | r1_tarski(A_299,B_300) ) ),
    inference(resolution,[status(thm)],[c_1640,c_14])).

tff(c_1717,plain,(
    ! [A_301,B_302] :
      ( ~ r1_tarski(A_301,'#skF_3')
      | r1_tarski(A_301,B_302) ) ),
    inference(resolution,[status(thm)],[c_1610,c_1706])).

tff(c_1730,plain,(
    ! [B_302] : r1_tarski('#skF_6',B_302) ),
    inference(resolution,[status(thm)],[c_877,c_1717])).

tff(c_1786,plain,(
    ! [A_306,A_307,B_308,C_309] :
      ( r2_hidden(k1_mcart_1(A_306),k2_zfmisc_1(A_307,B_308))
      | ~ r2_hidden(A_306,k3_zfmisc_1(A_307,B_308,C_309)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_941])).

tff(c_1812,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_1786])).

tff(c_1823,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1812,c_18])).

tff(c_1837,plain,(
    ~ r1_tarski('#skF_6',k2_mcart_1(k1_mcart_1('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_1823,c_14])).

tff(c_1844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1730,c_1837])).

tff(c_1845,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1530])).

tff(c_1851,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1845])).

tff(c_2021,plain,(
    ! [A_338,A_339,B_340,C_341] :
      ( r2_hidden(k1_mcart_1(A_338),k2_zfmisc_1(A_339,B_340))
      | ~ r2_hidden(A_338,k3_zfmisc_1(A_339,B_340,C_341)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_941])).

tff(c_2051,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_2021])).

tff(c_2055,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2051,c_18])).

tff(c_2064,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1851,c_2055])).

tff(c_2066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1394,c_2064])).

tff(c_2067,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1845])).

tff(c_1408,plain,(
    ! [B_255] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_255)
      | ~ r1_tarski('#skF_7',B_255) ) ),
    inference(resolution,[status(thm)],[c_975,c_2])).

tff(c_1531,plain,(
    ! [B_271,B_272] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_271)
      | ~ r1_tarski(B_272,B_271)
      | ~ r1_tarski('#skF_7',B_272) ) ),
    inference(resolution,[status(thm)],[c_1408,c_2])).

tff(c_1539,plain,
    ( r2_hidden(k2_mcart_1('#skF_8'),'#skF_4')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_876,c_1531])).

tff(c_1547,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_1539])).

tff(c_1558,plain,(
    ! [B_273] :
      ( r2_hidden(k2_mcart_1('#skF_8'),B_273)
      | ~ r1_tarski('#skF_4',B_273) ) ),
    inference(resolution,[status(thm)],[c_1547,c_2])).

tff(c_1578,plain,(
    ! [B_274] :
      ( ~ r1_tarski(B_274,k2_mcart_1('#skF_8'))
      | ~ r1_tarski('#skF_4',B_274) ) ),
    inference(resolution,[status(thm)],[c_1558,c_14])).

tff(c_1588,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_1578])).

tff(c_2070,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2067,c_1588])).

tff(c_2080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_2070])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n001.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 20:57:00 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.33/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.79  
% 4.40/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.79  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 4.40/1.79  
% 4.40/1.79  %Foreground sorts:
% 4.40/1.79  
% 4.40/1.79  
% 4.40/1.79  %Background operators:
% 4.40/1.79  
% 4.40/1.79  
% 4.40/1.79  %Foreground operators:
% 4.40/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.40/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.40/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.40/1.79  tff('#skF_7', type, '#skF_7': $i).
% 4.40/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.40/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.40/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.40/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.40/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.40/1.79  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 4.40/1.79  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.40/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.40/1.79  tff('#skF_8', type, '#skF_8': $i).
% 4.40/1.79  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 4.40/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.40/1.79  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.40/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.40/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.40/1.79  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 4.40/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.40/1.79  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.40/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.40/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.40/1.79  
% 4.63/1.83  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.63/1.83  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 4.63/1.83  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.63/1.83  tff(f_45, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.63/1.83  tff(f_51, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.63/1.83  tff(f_71, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 4.63/1.83  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.63/1.83  tff(f_43, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.63/1.83  tff(c_884, plain, (![A_173, B_174]: (r2_hidden('#skF_1'(A_173, B_174), A_173) | r1_tarski(A_173, B_174))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.83  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.83  tff(c_892, plain, (![A_173]: (r1_tarski(A_173, A_173))), inference(resolution, [status(thm)], [c_884, c_4])).
% 4.63/1.83  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.83  tff(c_862, plain, (![A_169, B_170]: (r1_tarski(A_169, B_170) | ~m1_subset_1(A_169, k1_zfmisc_1(B_170)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.63/1.83  tff(c_877, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_862])).
% 4.63/1.83  tff(c_30, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.83  tff(c_16, plain, (![A_11, B_12, C_13]: (k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13)=k3_zfmisc_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.63/1.83  tff(c_934, plain, (![A_185, C_186, B_187]: (r2_hidden(k2_mcart_1(A_185), C_186) | ~r2_hidden(A_185, k2_zfmisc_1(B_187, C_186)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.63/1.83  tff(c_964, plain, (![A_192, C_193, A_194, B_195]: (r2_hidden(k2_mcart_1(A_192), C_193) | ~r2_hidden(A_192, k3_zfmisc_1(A_194, B_195, C_193)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_934])).
% 4.63/1.83  tff(c_975, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_30, c_964])).
% 4.63/1.83  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.83  tff(c_878, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_862])).
% 4.63/1.83  tff(c_32, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.83  tff(c_1051, plain, (![A_201, B_202, C_203, D_204]: (k7_mcart_1(A_201, B_202, C_203, D_204)=k2_mcart_1(D_204) | ~m1_subset_1(D_204, k3_zfmisc_1(A_201, B_202, C_203)) | k1_xboole_0=C_203 | k1_xboole_0=B_202 | k1_xboole_0=A_201)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.63/1.83  tff(c_1055, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_1051])).
% 4.63/1.83  tff(c_1057, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1055])).
% 4.63/1.83  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.63/1.83  tff(c_28, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.83  tff(c_46, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_28])).
% 4.63/1.83  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.83  tff(c_69, plain, (![A_42, B_43]: (~r2_hidden('#skF_1'(A_42, B_43), B_43) | r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.83  tff(c_74, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_69])).
% 4.63/1.83  tff(c_47, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.63/1.83  tff(c_62, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_47])).
% 4.63/1.83  tff(c_63, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_47])).
% 4.63/1.83  tff(c_134, plain, (![A_64, B_65, C_66, D_67]: (k7_mcart_1(A_64, B_65, C_66, D_67)=k2_mcart_1(D_67) | ~m1_subset_1(D_67, k3_zfmisc_1(A_64, B_65, C_66)) | k1_xboole_0=C_66 | k1_xboole_0=B_65 | k1_xboole_0=A_64)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.63/1.83  tff(c_138, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_134])).
% 4.63/1.83  tff(c_166, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_138])).
% 4.63/1.83  tff(c_168, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_8])).
% 4.63/1.83  tff(c_83, plain, (![C_47, B_48, A_49]: (r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.83  tff(c_294, plain, (![A_93, B_94, B_95]: (r2_hidden('#skF_1'(A_93, B_94), B_95) | ~r1_tarski(A_93, B_95) | r1_tarski(A_93, B_94))), inference(resolution, [status(thm)], [c_6, c_83])).
% 4.63/1.83  tff(c_14, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.63/1.83  tff(c_319, plain, (![B_96, A_97, B_98]: (~r1_tarski(B_96, '#skF_1'(A_97, B_98)) | ~r1_tarski(A_97, B_96) | r1_tarski(A_97, B_98))), inference(resolution, [status(thm)], [c_294, c_14])).
% 4.63/1.83  tff(c_330, plain, (![A_99, B_100]: (~r1_tarski(A_99, '#skF_2') | r1_tarski(A_99, B_100))), inference(resolution, [status(thm)], [c_168, c_319])).
% 4.63/1.83  tff(c_343, plain, (![B_100]: (r1_tarski('#skF_5', B_100))), inference(resolution, [status(thm)], [c_63, c_330])).
% 4.63/1.83  tff(c_105, plain, (![A_53, B_54, C_55]: (r2_hidden(k1_mcart_1(A_53), B_54) | ~r2_hidden(A_53, k2_zfmisc_1(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.63/1.83  tff(c_422, plain, (![A_114, A_115, B_116, C_117]: (r2_hidden(k1_mcart_1(A_114), k2_zfmisc_1(A_115, B_116)) | ~r2_hidden(A_114, k3_zfmisc_1(A_115, B_116, C_117)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_105])).
% 4.63/1.83  tff(c_444, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_422])).
% 4.63/1.83  tff(c_20, plain, (![A_14, B_15, C_16]: (r2_hidden(k1_mcart_1(A_14), B_15) | ~r2_hidden(A_14, k2_zfmisc_1(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.63/1.83  tff(c_455, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_444, c_20])).
% 4.63/1.83  tff(c_469, plain, (~r1_tarski('#skF_5', k1_mcart_1(k1_mcart_1('#skF_8')))), inference(resolution, [status(thm)], [c_455, c_14])).
% 4.63/1.84  tff(c_476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_343, c_469])).
% 4.63/1.84  tff(c_478, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_138])).
% 4.63/1.84  tff(c_558, plain, (![A_129, B_130, C_131, D_132]: (k5_mcart_1(A_129, B_130, C_131, D_132)=k1_mcart_1(k1_mcart_1(D_132)) | ~m1_subset_1(D_132, k3_zfmisc_1(A_129, B_130, C_131)) | k1_xboole_0=C_131 | k1_xboole_0=B_130 | k1_xboole_0=A_129)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.63/1.84  tff(c_561, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_558])).
% 4.63/1.84  tff(c_564, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_478, c_561])).
% 4.63/1.84  tff(c_645, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_564])).
% 4.63/1.84  tff(c_658, plain, (![A_149]: (r1_tarski('#skF_3', A_149))), inference(demodulation, [status(thm), theory('equality')], [c_645, c_8])).
% 4.63/1.84  tff(c_598, plain, (![A_141, B_142, B_143]: (r2_hidden('#skF_1'(A_141, B_142), B_143) | ~r1_tarski(A_141, B_143) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_6, c_83])).
% 4.63/1.84  tff(c_622, plain, (![B_143, A_141, B_142]: (~r1_tarski(B_143, '#skF_1'(A_141, B_142)) | ~r1_tarski(A_141, B_143) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_598, c_14])).
% 4.63/1.84  tff(c_687, plain, (![A_150, B_151]: (~r1_tarski(A_150, '#skF_3') | r1_tarski(A_150, B_151))), inference(resolution, [status(thm)], [c_658, c_622])).
% 4.63/1.84  tff(c_700, plain, (![B_151]: (r1_tarski('#skF_6', B_151))), inference(resolution, [status(thm)], [c_62, c_687])).
% 4.63/1.84  tff(c_752, plain, (![A_158, A_159, B_160, C_161]: (r2_hidden(k1_mcart_1(A_158), k2_zfmisc_1(A_159, B_160)) | ~r2_hidden(A_158, k3_zfmisc_1(A_159, B_160, C_161)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_105])).
% 4.63/1.84  tff(c_771, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_752])).
% 4.63/1.84  tff(c_18, plain, (![A_14, C_16, B_15]: (r2_hidden(k2_mcart_1(A_14), C_16) | ~r2_hidden(A_14, k2_zfmisc_1(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.63/1.84  tff(c_781, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_771, c_18])).
% 4.63/1.84  tff(c_789, plain, (~r1_tarski('#skF_6', k2_mcart_1(k1_mcart_1('#skF_8')))), inference(resolution, [status(thm)], [c_781, c_14])).
% 4.63/1.84  tff(c_796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_700, c_789])).
% 4.63/1.84  tff(c_798, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_564])).
% 4.63/1.84  tff(c_515, plain, (![A_121, B_122, C_123, D_124]: (k6_mcart_1(A_121, B_122, C_123, D_124)=k2_mcart_1(k1_mcart_1(D_124)) | ~m1_subset_1(D_124, k3_zfmisc_1(A_121, B_122, C_123)) | k1_xboole_0=C_123 | k1_xboole_0=B_122 | k1_xboole_0=A_121)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.63/1.84  tff(c_518, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_515])).
% 4.63/1.84  tff(c_521, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_478, c_518])).
% 4.63/1.84  tff(c_799, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_798, c_521])).
% 4.63/1.84  tff(c_800, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_799])).
% 4.63/1.84  tff(c_34, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.84  tff(c_61, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_47])).
% 4.63/1.84  tff(c_112, plain, (![A_56, C_57, B_58]: (r2_hidden(k2_mcart_1(A_56), C_57) | ~r2_hidden(A_56, k2_zfmisc_1(B_58, C_57)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.63/1.84  tff(c_126, plain, (![A_60, C_61, A_62, B_63]: (r2_hidden(k2_mcart_1(A_60), C_61) | ~r2_hidden(A_60, k3_zfmisc_1(A_62, B_63, C_61)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_112])).
% 4.63/1.84  tff(c_133, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_30, c_126])).
% 4.63/1.84  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.84  tff(c_146, plain, (![B_68]: (r2_hidden(k2_mcart_1('#skF_8'), B_68) | ~r1_tarski('#skF_7', B_68))), inference(resolution, [status(thm)], [c_133, c_2])).
% 4.63/1.84  tff(c_490, plain, (![B_119, B_120]: (r2_hidden(k2_mcart_1('#skF_8'), B_119) | ~r1_tarski(B_120, B_119) | ~r1_tarski('#skF_7', B_120))), inference(resolution, [status(thm)], [c_146, c_2])).
% 4.63/1.84  tff(c_498, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_61, c_490])).
% 4.63/1.84  tff(c_506, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_498])).
% 4.63/1.84  tff(c_524, plain, (![B_125]: (r2_hidden(k2_mcart_1('#skF_8'), B_125) | ~r1_tarski('#skF_4', B_125))), inference(resolution, [status(thm)], [c_506, c_2])).
% 4.63/1.84  tff(c_544, plain, (![B_126]: (~r1_tarski(B_126, k2_mcart_1('#skF_8')) | ~r1_tarski('#skF_4', B_126))), inference(resolution, [status(thm)], [c_524, c_14])).
% 4.63/1.84  tff(c_554, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_544])).
% 4.63/1.84  tff(c_804, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_800, c_554])).
% 4.63/1.84  tff(c_812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_804])).
% 4.63/1.84  tff(c_814, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_799])).
% 4.63/1.84  tff(c_797, plain, (k1_xboole_0='#skF_4' | k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_564])).
% 4.63/1.84  tff(c_819, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_814, c_797])).
% 4.63/1.84  tff(c_825, plain, (![A_165, A_166, B_167, C_168]: (r2_hidden(k1_mcart_1(A_165), k2_zfmisc_1(A_166, B_167)) | ~r2_hidden(A_165, k3_zfmisc_1(A_166, B_167, C_168)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_105])).
% 4.63/1.84  tff(c_844, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_825])).
% 4.63/1.84  tff(c_848, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_844, c_20])).
% 4.63/1.84  tff(c_857, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_819, c_848])).
% 4.63/1.84  tff(c_859, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_857])).
% 4.63/1.84  tff(c_861, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_28])).
% 4.63/1.84  tff(c_894, plain, (![C_175, B_176, A_177]: (r2_hidden(C_175, B_176) | ~r2_hidden(C_175, A_177) | ~r1_tarski(A_177, B_176))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.63/1.84  tff(c_948, plain, (![B_191]: (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), B_191) | ~r1_tarski('#skF_5', B_191))), inference(resolution, [status(thm)], [c_861, c_894])).
% 4.63/1.84  tff(c_1015, plain, (![B_198]: (~r1_tarski(B_198, k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')) | ~r1_tarski('#skF_5', B_198))), inference(resolution, [status(thm)], [c_948, c_14])).
% 4.63/1.84  tff(c_1025, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1015])).
% 4.63/1.84  tff(c_1059, plain, (~r1_tarski('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_1025])).
% 4.63/1.84  tff(c_1064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_878, c_1059])).
% 4.63/1.84  tff(c_1065, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_1055])).
% 4.63/1.84  tff(c_1109, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_1065])).
% 4.63/1.84  tff(c_860, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_28])).
% 4.63/1.84  tff(c_983, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_860])).
% 4.63/1.84  tff(c_1110, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1109, c_983])).
% 4.63/1.84  tff(c_1113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_975, c_1110])).
% 4.63/1.84  tff(c_1114, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1065])).
% 4.63/1.84  tff(c_1116, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1114])).
% 4.63/1.84  tff(c_1123, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1116, c_8])).
% 4.63/1.84  tff(c_1163, plain, (![A_218, B_219, B_220]: (r2_hidden('#skF_1'(A_218, B_219), B_220) | ~r1_tarski(A_218, B_220) | r1_tarski(A_218, B_219))), inference(resolution, [status(thm)], [c_6, c_894])).
% 4.63/1.84  tff(c_1216, plain, (![B_229, A_230, B_231]: (~r1_tarski(B_229, '#skF_1'(A_230, B_231)) | ~r1_tarski(A_230, B_229) | r1_tarski(A_230, B_231))), inference(resolution, [status(thm)], [c_1163, c_14])).
% 4.63/1.84  tff(c_1245, plain, (![A_236, B_237]: (~r1_tarski(A_236, '#skF_3') | r1_tarski(A_236, B_237))), inference(resolution, [status(thm)], [c_1123, c_1216])).
% 4.63/1.84  tff(c_1258, plain, (![B_237]: (r1_tarski('#skF_6', B_237))), inference(resolution, [status(thm)], [c_877, c_1245])).
% 4.63/1.84  tff(c_941, plain, (![A_188, B_189, C_190]: (r2_hidden(k1_mcart_1(A_188), B_189) | ~r2_hidden(A_188, k2_zfmisc_1(B_189, C_190)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.63/1.84  tff(c_1320, plain, (![A_247, A_248, B_249, C_250]: (r2_hidden(k1_mcart_1(A_247), k2_zfmisc_1(A_248, B_249)) | ~r2_hidden(A_247, k3_zfmisc_1(A_248, B_249, C_250)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_941])).
% 4.63/1.84  tff(c_1346, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_1320])).
% 4.63/1.84  tff(c_1358, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_1346, c_18])).
% 4.63/1.84  tff(c_1372, plain, (~r1_tarski('#skF_6', k2_mcart_1(k1_mcart_1('#skF_8')))), inference(resolution, [status(thm)], [c_1358, c_14])).
% 4.63/1.84  tff(c_1379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1258, c_1372])).
% 4.63/1.84  tff(c_1380, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1114])).
% 4.63/1.84  tff(c_876, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_862])).
% 4.63/1.84  tff(c_984, plain, (![B_196]: (r2_hidden(k2_mcart_1('#skF_8'), B_196) | ~r1_tarski('#skF_7', B_196))), inference(resolution, [status(thm)], [c_975, c_2])).
% 4.63/1.84  tff(c_1026, plain, (![B_199, B_200]: (r2_hidden(k2_mcart_1('#skF_8'), B_199) | ~r1_tarski(B_200, B_199) | ~r1_tarski('#skF_7', B_200))), inference(resolution, [status(thm)], [c_984, c_2])).
% 4.63/1.84  tff(c_1034, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_876, c_1026])).
% 4.63/1.84  tff(c_1042, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_892, c_1034])).
% 4.63/1.84  tff(c_1068, plain, (![B_205]: (r2_hidden(k2_mcart_1('#skF_8'), B_205) | ~r1_tarski('#skF_4', B_205))), inference(resolution, [status(thm)], [c_1042, c_2])).
% 4.63/1.84  tff(c_1095, plain, (![B_210]: (~r1_tarski(B_210, k2_mcart_1('#skF_8')) | ~r1_tarski('#skF_4', B_210))), inference(resolution, [status(thm)], [c_1068, c_14])).
% 4.63/1.84  tff(c_1105, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1095])).
% 4.63/1.84  tff(c_1384, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1380, c_1105])).
% 4.63/1.84  tff(c_1393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_892, c_1384])).
% 4.63/1.84  tff(c_1394, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_860])).
% 4.63/1.84  tff(c_1403, plain, (![A_251, B_252, C_253, D_254]: (k7_mcart_1(A_251, B_252, C_253, D_254)=k2_mcart_1(D_254) | ~m1_subset_1(D_254, k3_zfmisc_1(A_251, B_252, C_253)) | k1_xboole_0=C_253 | k1_xboole_0=B_252 | k1_xboole_0=A_251)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.63/1.84  tff(c_1407, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_1403])).
% 4.63/1.84  tff(c_1439, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1407])).
% 4.63/1.84  tff(c_1441, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1439, c_8])).
% 4.63/1.84  tff(c_1486, plain, (![B_263]: (~r1_tarski(B_263, k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')) | ~r1_tarski('#skF_5', B_263))), inference(resolution, [status(thm)], [c_948, c_14])).
% 4.63/1.84  tff(c_1490, plain, (~r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_1441, c_1486])).
% 4.63/1.84  tff(c_1498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_878, c_1490])).
% 4.63/1.84  tff(c_1500, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1407])).
% 4.63/1.84  tff(c_1524, plain, (![A_267, B_268, C_269, D_270]: (k6_mcart_1(A_267, B_268, C_269, D_270)=k2_mcart_1(k1_mcart_1(D_270)) | ~m1_subset_1(D_270, k3_zfmisc_1(A_267, B_268, C_269)) | k1_xboole_0=C_269 | k1_xboole_0=B_268 | k1_xboole_0=A_267)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.63/1.84  tff(c_1527, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_1524])).
% 4.63/1.84  tff(c_1530, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1500, c_1527])).
% 4.63/1.84  tff(c_1602, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1530])).
% 4.63/1.84  tff(c_1610, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1602, c_8])).
% 4.63/1.84  tff(c_1640, plain, (![A_284, B_285, B_286]: (r2_hidden('#skF_1'(A_284, B_285), B_286) | ~r1_tarski(A_284, B_286) | r1_tarski(A_284, B_285))), inference(resolution, [status(thm)], [c_6, c_894])).
% 4.63/1.84  tff(c_1706, plain, (![B_298, A_299, B_300]: (~r1_tarski(B_298, '#skF_1'(A_299, B_300)) | ~r1_tarski(A_299, B_298) | r1_tarski(A_299, B_300))), inference(resolution, [status(thm)], [c_1640, c_14])).
% 4.63/1.84  tff(c_1717, plain, (![A_301, B_302]: (~r1_tarski(A_301, '#skF_3') | r1_tarski(A_301, B_302))), inference(resolution, [status(thm)], [c_1610, c_1706])).
% 4.63/1.84  tff(c_1730, plain, (![B_302]: (r1_tarski('#skF_6', B_302))), inference(resolution, [status(thm)], [c_877, c_1717])).
% 4.63/1.84  tff(c_1786, plain, (![A_306, A_307, B_308, C_309]: (r2_hidden(k1_mcart_1(A_306), k2_zfmisc_1(A_307, B_308)) | ~r2_hidden(A_306, k3_zfmisc_1(A_307, B_308, C_309)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_941])).
% 4.63/1.84  tff(c_1812, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_1786])).
% 4.63/1.84  tff(c_1823, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_1812, c_18])).
% 4.63/1.84  tff(c_1837, plain, (~r1_tarski('#skF_6', k2_mcart_1(k1_mcart_1('#skF_8')))), inference(resolution, [status(thm)], [c_1823, c_14])).
% 4.63/1.84  tff(c_1844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1730, c_1837])).
% 4.63/1.84  tff(c_1845, plain, (k1_xboole_0='#skF_4' | k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_1530])).
% 4.63/1.84  tff(c_1851, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_1845])).
% 4.63/1.84  tff(c_2021, plain, (![A_338, A_339, B_340, C_341]: (r2_hidden(k1_mcart_1(A_338), k2_zfmisc_1(A_339, B_340)) | ~r2_hidden(A_338, k3_zfmisc_1(A_339, B_340, C_341)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_941])).
% 4.63/1.84  tff(c_2051, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_2021])).
% 4.63/1.84  tff(c_2055, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_2051, c_18])).
% 4.63/1.84  tff(c_2064, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1851, c_2055])).
% 4.63/1.84  tff(c_2066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1394, c_2064])).
% 4.63/1.84  tff(c_2067, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1845])).
% 4.63/1.84  tff(c_1408, plain, (![B_255]: (r2_hidden(k2_mcart_1('#skF_8'), B_255) | ~r1_tarski('#skF_7', B_255))), inference(resolution, [status(thm)], [c_975, c_2])).
% 4.63/1.84  tff(c_1531, plain, (![B_271, B_272]: (r2_hidden(k2_mcart_1('#skF_8'), B_271) | ~r1_tarski(B_272, B_271) | ~r1_tarski('#skF_7', B_272))), inference(resolution, [status(thm)], [c_1408, c_2])).
% 4.63/1.84  tff(c_1539, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4') | ~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_876, c_1531])).
% 4.63/1.84  tff(c_1547, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_892, c_1539])).
% 4.63/1.84  tff(c_1558, plain, (![B_273]: (r2_hidden(k2_mcart_1('#skF_8'), B_273) | ~r1_tarski('#skF_4', B_273))), inference(resolution, [status(thm)], [c_1547, c_2])).
% 4.63/1.84  tff(c_1578, plain, (![B_274]: (~r1_tarski(B_274, k2_mcart_1('#skF_8')) | ~r1_tarski('#skF_4', B_274))), inference(resolution, [status(thm)], [c_1558, c_14])).
% 4.63/1.84  tff(c_1588, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1578])).
% 4.63/1.84  tff(c_2070, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2067, c_1588])).
% 4.63/1.84  tff(c_2080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_892, c_2070])).
% 4.63/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.84  
% 4.63/1.84  Inference rules
% 4.63/1.84  ----------------------
% 4.63/1.84  #Ref     : 0
% 4.63/1.84  #Sup     : 457
% 4.63/1.84  #Fact    : 0
% 4.63/1.84  #Define  : 0
% 4.63/1.84  #Split   : 36
% 4.63/1.84  #Chain   : 0
% 4.63/1.84  #Close   : 0
% 4.63/1.84  
% 4.63/1.84  Ordering : KBO
% 4.63/1.84  
% 4.63/1.84  Simplification rules
% 4.63/1.84  ----------------------
% 4.63/1.84  #Subsume      : 90
% 4.63/1.84  #Demod        : 207
% 4.63/1.84  #Tautology    : 106
% 4.63/1.84  #SimpNegUnit  : 11
% 4.63/1.84  #BackRed      : 60
% 4.63/1.84  
% 4.63/1.84  #Partial instantiations: 0
% 4.63/1.84  #Strategies tried      : 1
% 4.63/1.84  
% 4.63/1.84  Timing (in seconds)
% 4.63/1.84  ----------------------
% 4.63/1.84  Preprocessing        : 0.35
% 4.63/1.84  Parsing              : 0.20
% 4.63/1.84  CNF conversion       : 0.02
% 4.63/1.84  Main loop            : 0.73
% 4.63/1.84  Inferencing          : 0.26
% 4.63/1.84  Reduction            : 0.23
% 4.63/1.84  Demodulation         : 0.15
% 4.63/1.84  BG Simplification    : 0.03
% 4.63/1.84  Subsumption          : 0.15
% 4.63/1.84  Abstraction          : 0.03
% 4.63/1.84  MUC search           : 0.00
% 4.63/1.84  Cooper               : 0.00
% 4.63/1.84  Total                : 1.16
% 4.63/1.84  Index Insertion      : 0.00
% 4.63/1.84  Index Deletion       : 0.00
% 4.63/1.84  Index Matching       : 0.00
% 4.63/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
