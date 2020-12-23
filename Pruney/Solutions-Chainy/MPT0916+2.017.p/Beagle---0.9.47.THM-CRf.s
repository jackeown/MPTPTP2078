%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:12 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 573 expanded)
%              Number of leaves         :   33 ( 199 expanded)
%              Depth                    :   11
%              Number of atoms          :  319 (1622 expanded)
%              Number of equality atoms :  103 ( 476 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(c_28,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] : k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13) = k3_zfmisc_1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_441,plain,(
    ! [A_124,C_125,B_126] :
      ( r2_hidden(k2_mcart_1(A_124),C_125)
      | ~ r2_hidden(A_124,k2_zfmisc_1(B_126,C_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_448,plain,(
    ! [A_127,C_128,A_129,B_130] :
      ( r2_hidden(k2_mcart_1(A_127),C_128)
      | ~ r2_hidden(A_127,k3_zfmisc_1(A_129,B_130,C_128)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_441])).

tff(c_454,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_448])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_459,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_454,c_2])).

tff(c_32,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_397,plain,(
    ! [A_114,B_115] :
      ( r1_tarski(A_114,B_115)
      | ~ m1_subset_1(A_114,k1_zfmisc_1(B_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_407,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_397])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_466,plain,(
    ! [B_136,C_137] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_136,C_137))),C_137)
      | v1_xboole_0(k2_zfmisc_1(B_136,C_137)) ) ),
    inference(resolution,[status(thm)],[c_4,c_441])).

tff(c_485,plain,(
    ! [C_137,B_136] :
      ( ~ v1_xboole_0(C_137)
      | v1_xboole_0(k2_zfmisc_1(B_136,C_137)) ) ),
    inference(resolution,[status(thm)],[c_466,c_2])).

tff(c_434,plain,(
    ! [A_121,B_122,C_123] :
      ( r2_hidden(k1_mcart_1(A_121),B_122)
      | ~ r2_hidden(A_121,k2_zfmisc_1(B_122,C_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_501,plain,(
    ! [B_147,C_148] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_147,C_148))),B_147)
      | v1_xboole_0(k2_zfmisc_1(B_147,C_148)) ) ),
    inference(resolution,[status(thm)],[c_4,c_434])).

tff(c_555,plain,(
    ! [B_158,C_159] :
      ( ~ v1_xboole_0(B_158)
      | v1_xboole_0(k2_zfmisc_1(B_158,C_159)) ) ),
    inference(resolution,[status(thm)],[c_501,c_2])).

tff(c_559,plain,(
    ! [A_160,B_161,C_162] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_160,B_161))
      | v1_xboole_0(k3_zfmisc_1(A_160,B_161,C_162)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_555])).

tff(c_47,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_28,c_2])).

tff(c_563,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_559,c_47])).

tff(c_586,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_485,c_563])).

tff(c_34,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_408,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_397])).

tff(c_77,plain,(
    ! [A_47,B_48,C_49] : k2_zfmisc_1(k2_zfmisc_1(A_47,B_48),C_49) = k3_zfmisc_1(A_47,B_48,C_49) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_14,C_16,B_15] :
      ( r2_hidden(k2_mcart_1(A_14),C_16)
      | ~ r2_hidden(A_14,k2_zfmisc_1(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_101,plain,(
    ! [A_55,C_56,A_57,B_58] :
      ( r2_hidden(k2_mcart_1(A_55),C_56)
      | ~ r2_hidden(A_55,k3_zfmisc_1(A_57,B_58,C_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_16])).

tff(c_107,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_101])).

tff(c_112,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_49,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_59,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_49])).

tff(c_26,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_48,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_67,plain,(
    ! [A_41,C_42,B_43] :
      ( r2_hidden(k2_mcart_1(A_41),C_42)
      | ~ r2_hidden(A_41,k2_zfmisc_1(B_43,C_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_181,plain,(
    ! [B_77,C_78] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_77,C_78))),C_78)
      | v1_xboole_0(k2_zfmisc_1(B_77,C_78)) ) ),
    inference(resolution,[status(thm)],[c_4,c_67])).

tff(c_217,plain,(
    ! [C_80,B_81] :
      ( ~ v1_xboole_0(C_80)
      | v1_xboole_0(k2_zfmisc_1(B_81,C_80)) ) ),
    inference(resolution,[status(thm)],[c_181,c_2])).

tff(c_72,plain,(
    ! [A_44,B_45,C_46] :
      ( r2_hidden(k1_mcart_1(A_44),B_45)
      | ~ r2_hidden(A_44,k2_zfmisc_1(B_45,C_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_113,plain,(
    ! [B_59,C_60] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_59,C_60))),B_59)
      | v1_xboole_0(k2_zfmisc_1(B_59,C_60)) ) ),
    inference(resolution,[status(thm)],[c_4,c_72])).

tff(c_141,plain,(
    ! [B_65,C_66] :
      ( ~ v1_xboole_0(B_65)
      | v1_xboole_0(k2_zfmisc_1(B_65,C_66)) ) ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_145,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_67,B_68))
      | v1_xboole_0(k3_zfmisc_1(A_67,B_68,C_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_141])).

tff(c_149,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_145,c_47])).

tff(c_224,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_217,c_149])).

tff(c_60,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_134,plain,(
    ! [B_59,C_60] :
      ( ~ v1_xboole_0(B_59)
      | v1_xboole_0(k2_zfmisc_1(B_59,C_60)) ) ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_153,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_134,c_149])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_61,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_49])).

tff(c_30,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_136,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( k7_mcart_1(A_61,B_62,C_63,D_64) = k2_mcart_1(D_64)
      | ~ m1_subset_1(D_64,k3_zfmisc_1(A_61,B_62,C_63))
      | k1_xboole_0 = C_63
      | k1_xboole_0 = B_62
      | k1_xboole_0 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_140,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_136])).

tff(c_154,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_6,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_96,plain,(
    ! [A_50,B_51,C_52] :
      ( ~ r1_xboole_0(A_50,B_51)
      | ~ r1_tarski(C_52,B_51)
      | ~ r1_tarski(C_52,A_50)
      | v1_xboole_0(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_99,plain,(
    ! [C_52,A_5] :
      ( ~ r1_tarski(C_52,k1_xboole_0)
      | ~ r1_tarski(C_52,A_5)
      | v1_xboole_0(C_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_96])).

tff(c_166,plain,(
    ! [C_71,A_72] :
      ( ~ r1_tarski(C_71,'#skF_2')
      | ~ r1_tarski(C_71,A_72)
      | v1_xboole_0(C_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_99])).

tff(c_168,plain,(
    ! [A_72] :
      ( ~ r1_tarski('#skF_5',A_72)
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_61,c_166])).

tff(c_171,plain,(
    ! [A_72] : ~ r1_tarski('#skF_5',A_72) ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_168])).

tff(c_173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_61])).

tff(c_175,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_176,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( k5_mcart_1(A_73,B_74,C_75,D_76) = k1_mcart_1(k1_mcart_1(D_76))
      | ~ m1_subset_1(D_76,k3_zfmisc_1(A_73,B_74,C_75))
      | k1_xboole_0 = C_75
      | k1_xboole_0 = B_74
      | k1_xboole_0 = A_73 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_180,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_176])).

tff(c_202,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_180])).

tff(c_203,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_239,plain,(
    ! [C_89,A_90] :
      ( ~ r1_tarski(C_89,'#skF_3')
      | ~ r1_tarski(C_89,A_90)
      | v1_xboole_0(C_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_99])).

tff(c_241,plain,(
    ! [A_90] :
      ( ~ r1_tarski('#skF_6',A_90)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60,c_239])).

tff(c_244,plain,(
    ! [A_90] : ~ r1_tarski('#skF_6',A_90) ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_241])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_244,c_60])).

tff(c_247,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_274,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] :
      ( r2_hidden(k1_mcart_1(A_14),B_15)
      | ~ r2_hidden(A_14,k2_zfmisc_1(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_340,plain,(
    ! [A_107,A_108,B_109,C_110] :
      ( r2_hidden(k1_mcart_1(A_107),k2_zfmisc_1(A_108,B_109))
      | ~ r2_hidden(A_107,k3_zfmisc_1(A_108,B_109,C_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_18])).

tff(c_357,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_28,c_340])).

tff(c_360,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_357,c_18])).

tff(c_367,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_360])).

tff(c_369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_367])).

tff(c_370,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_387,plain,(
    ! [C_112,A_113] :
      ( ~ r1_tarski(C_112,'#skF_4')
      | ~ r1_tarski(C_112,A_113)
      | v1_xboole_0(C_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_99])).

tff(c_389,plain,(
    ! [A_113] :
      ( ~ r1_tarski('#skF_7',A_113)
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_59,c_387])).

tff(c_392,plain,(
    ! [A_113] : ~ r1_tarski('#skF_7',A_113) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_389])).

tff(c_394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_392,c_59])).

tff(c_396,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_413,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_396,c_2])).

tff(c_409,plain,(
    r1_tarski('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_397])).

tff(c_487,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( k7_mcart_1(A_138,B_139,C_140,D_141) = k2_mcart_1(D_141)
      | ~ m1_subset_1(D_141,k3_zfmisc_1(A_138,B_139,C_140))
      | k1_xboole_0 = C_140
      | k1_xboole_0 = B_139
      | k1_xboole_0 = A_138 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_491,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_487])).

tff(c_524,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_491])).

tff(c_461,plain,(
    ! [A_131,B_132,C_133] :
      ( ~ r1_xboole_0(A_131,B_132)
      | ~ r1_tarski(C_133,B_132)
      | ~ r1_tarski(C_133,A_131)
      | v1_xboole_0(C_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_464,plain,(
    ! [C_133,A_5] :
      ( ~ r1_tarski(C_133,k1_xboole_0)
      | ~ r1_tarski(C_133,A_5)
      | v1_xboole_0(C_133) ) ),
    inference(resolution,[status(thm)],[c_6,c_461])).

tff(c_540,plain,(
    ! [C_152,A_153] :
      ( ~ r1_tarski(C_152,'#skF_2')
      | ~ r1_tarski(C_152,A_153)
      | v1_xboole_0(C_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_464])).

tff(c_542,plain,(
    ! [A_153] :
      ( ~ r1_tarski('#skF_5',A_153)
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_409,c_540])).

tff(c_545,plain,(
    ! [A_153] : ~ r1_tarski('#skF_5',A_153) ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_542])).

tff(c_547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_545,c_409])).

tff(c_549,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_491])).

tff(c_550,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( k6_mcart_1(A_154,B_155,C_156,D_157) = k2_mcart_1(k1_mcart_1(D_157))
      | ~ m1_subset_1(D_157,k3_zfmisc_1(A_154,B_155,C_156))
      | k1_xboole_0 = C_156
      | k1_xboole_0 = B_155
      | k1_xboole_0 = A_154 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_554,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_550])).

tff(c_564,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_549,c_554])).

tff(c_565,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_564])).

tff(c_596,plain,(
    ! [C_168,A_169] :
      ( ~ r1_tarski(C_168,'#skF_3')
      | ~ r1_tarski(C_168,A_169)
      | v1_xboole_0(C_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_464])).

tff(c_598,plain,(
    ! [A_169] :
      ( ~ r1_tarski('#skF_6',A_169)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_408,c_596])).

tff(c_601,plain,(
    ! [A_169] : ~ r1_tarski('#skF_6',A_169) ),
    inference(negUnitSimplification,[status(thm)],[c_586,c_598])).

tff(c_603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_601,c_408])).

tff(c_605,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_564])).

tff(c_548,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_491])).

tff(c_619,plain,
    ( k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_605,c_548])).

tff(c_620,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_619])).

tff(c_395,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_460,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_395])).

tff(c_621,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_460])).

tff(c_624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_621])).

tff(c_625,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_619])).

tff(c_650,plain,(
    ! [C_175,A_176] :
      ( ~ r1_tarski(C_175,'#skF_4')
      | ~ r1_tarski(C_175,A_176)
      | v1_xboole_0(C_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_464])).

tff(c_652,plain,(
    ! [A_176] :
      ( ~ r1_tarski('#skF_7',A_176)
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_407,c_650])).

tff(c_655,plain,(
    ! [A_176] : ~ r1_tarski('#skF_7',A_176) ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_652])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_655,c_407])).

tff(c_658,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_395])).

tff(c_674,plain,(
    ! [B_186,C_187] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_186,C_187))),C_187)
      | v1_xboole_0(k2_zfmisc_1(B_186,C_187)) ) ),
    inference(resolution,[status(thm)],[c_4,c_441])).

tff(c_693,plain,(
    ! [C_187,B_186] :
      ( ~ v1_xboole_0(C_187)
      | v1_xboole_0(k2_zfmisc_1(B_186,C_187)) ) ),
    inference(resolution,[status(thm)],[c_674,c_2])).

tff(c_704,plain,(
    ! [B_193,C_194] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_193,C_194))),B_193)
      | v1_xboole_0(k2_zfmisc_1(B_193,C_194)) ) ),
    inference(resolution,[status(thm)],[c_4,c_434])).

tff(c_727,plain,(
    ! [B_195,C_196] :
      ( ~ v1_xboole_0(B_195)
      | v1_xboole_0(k2_zfmisc_1(B_195,C_196)) ) ),
    inference(resolution,[status(thm)],[c_704,c_2])).

tff(c_736,plain,(
    ! [A_201,B_202,C_203] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_201,B_202))
      | v1_xboole_0(k3_zfmisc_1(A_201,B_202,C_203)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_727])).

tff(c_740,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_736,c_47])).

tff(c_748,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_693,c_740])).

tff(c_669,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k7_mcart_1(A_182,B_183,C_184,D_185) = k2_mcart_1(D_185)
      | ~ m1_subset_1(D_185,k3_zfmisc_1(A_182,B_183,C_184))
      | k1_xboole_0 = C_184
      | k1_xboole_0 = B_183
      | k1_xboole_0 = A_182 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_673,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_669])).

tff(c_749,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_673])).

tff(c_664,plain,(
    ! [A_177,B_178,C_179] :
      ( ~ r1_xboole_0(A_177,B_178)
      | ~ r1_tarski(C_179,B_178)
      | ~ r1_tarski(C_179,A_177)
      | v1_xboole_0(C_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_667,plain,(
    ! [C_179,A_5] :
      ( ~ r1_tarski(C_179,k1_xboole_0)
      | ~ r1_tarski(C_179,A_5)
      | v1_xboole_0(C_179) ) ),
    inference(resolution,[status(thm)],[c_6,c_664])).

tff(c_762,plain,(
    ! [C_205,A_206] :
      ( ~ r1_tarski(C_205,'#skF_2')
      | ~ r1_tarski(C_205,A_206)
      | v1_xboole_0(C_205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_749,c_667])).

tff(c_764,plain,(
    ! [A_206] :
      ( ~ r1_tarski('#skF_5',A_206)
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_409,c_762])).

tff(c_767,plain,(
    ! [A_206] : ~ r1_tarski('#skF_5',A_206) ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_764])).

tff(c_769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_767,c_409])).

tff(c_771,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_673])).

tff(c_731,plain,(
    ! [A_197,B_198,C_199,D_200] :
      ( k5_mcart_1(A_197,B_198,C_199,D_200) = k1_mcart_1(k1_mcart_1(D_200))
      | ~ m1_subset_1(D_200,k3_zfmisc_1(A_197,B_198,C_199))
      | k1_xboole_0 = C_199
      | k1_xboole_0 = B_198
      | k1_xboole_0 = A_197 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_735,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_731])).

tff(c_817,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_771,c_735])).

tff(c_818,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_817])).

tff(c_833,plain,(
    ! [C_216,A_217] :
      ( ~ r1_tarski(C_216,'#skF_3')
      | ~ r1_tarski(C_216,A_217)
      | v1_xboole_0(C_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_667])).

tff(c_835,plain,(
    ! [A_217] :
      ( ~ r1_tarski('#skF_6',A_217)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_408,c_833])).

tff(c_838,plain,(
    ! [A_217] : ~ r1_tarski('#skF_6',A_217) ),
    inference(negUnitSimplification,[status(thm)],[c_748,c_835])).

tff(c_840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_838,c_408])).

tff(c_842,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_817])).

tff(c_772,plain,(
    ! [A_207,B_208,C_209,D_210] :
      ( k6_mcart_1(A_207,B_208,C_209,D_210) = k2_mcart_1(k1_mcart_1(D_210))
      | ~ m1_subset_1(D_210,k3_zfmisc_1(A_207,B_208,C_209))
      | k1_xboole_0 = C_209
      | k1_xboole_0 = B_208
      | k1_xboole_0 = A_207 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_775,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_772])).

tff(c_778,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_771,c_775])).

tff(c_849,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_842,c_778])).

tff(c_850,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_849])).

tff(c_866,plain,(
    ! [C_219,A_220] :
      ( ~ r1_tarski(C_219,'#skF_4')
      | ~ r1_tarski(C_219,A_220)
      | v1_xboole_0(C_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_667])).

tff(c_868,plain,(
    ! [A_220] :
      ( ~ r1_tarski('#skF_7',A_220)
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_407,c_866])).

tff(c_871,plain,(
    ! [A_220] : ~ r1_tarski('#skF_7',A_220) ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_868])).

tff(c_892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_871,c_407])).

tff(c_893,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_849])).

tff(c_899,plain,(
    ! [A_225,A_226,B_227,C_228] :
      ( r2_hidden(k1_mcart_1(A_225),k2_zfmisc_1(A_226,B_227))
      | ~ r2_hidden(A_225,k3_zfmisc_1(A_226,B_227,C_228)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_434])).

tff(c_916,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_28,c_899])).

tff(c_919,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_916,c_16])).

tff(c_926,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_919])).

tff(c_928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_658,c_926])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:05:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.49  
% 3.28/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 3.28/1.50  
% 3.28/1.50  %Foreground sorts:
% 3.28/1.50  
% 3.28/1.50  
% 3.28/1.50  %Background operators:
% 3.28/1.50  
% 3.28/1.50  
% 3.28/1.50  %Foreground operators:
% 3.28/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.28/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.28/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.28/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.28/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.28/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.50  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.28/1.50  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.28/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.50  tff('#skF_8', type, '#skF_8': $i).
% 3.28/1.50  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.28/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.50  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.28/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.28/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.50  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.28/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.50  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.28/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.28/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.50  
% 3.28/1.52  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 3.28/1.52  tff(f_49, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.28/1.52  tff(f_55, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.28/1.52  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.28/1.52  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.28/1.52  tff(f_75, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.28/1.52  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.28/1.52  tff(f_43, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 3.28/1.52  tff(c_28, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.28/1.52  tff(c_14, plain, (![A_11, B_12, C_13]: (k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13)=k3_zfmisc_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.28/1.52  tff(c_441, plain, (![A_124, C_125, B_126]: (r2_hidden(k2_mcart_1(A_124), C_125) | ~r2_hidden(A_124, k2_zfmisc_1(B_126, C_125)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.28/1.52  tff(c_448, plain, (![A_127, C_128, A_129, B_130]: (r2_hidden(k2_mcart_1(A_127), C_128) | ~r2_hidden(A_127, k3_zfmisc_1(A_129, B_130, C_128)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_441])).
% 3.28/1.52  tff(c_454, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_28, c_448])).
% 3.28/1.52  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.52  tff(c_459, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_454, c_2])).
% 3.28/1.52  tff(c_32, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.28/1.52  tff(c_397, plain, (![A_114, B_115]: (r1_tarski(A_114, B_115) | ~m1_subset_1(A_114, k1_zfmisc_1(B_115)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.28/1.52  tff(c_407, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_397])).
% 3.28/1.52  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.52  tff(c_466, plain, (![B_136, C_137]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_136, C_137))), C_137) | v1_xboole_0(k2_zfmisc_1(B_136, C_137)))), inference(resolution, [status(thm)], [c_4, c_441])).
% 3.28/1.52  tff(c_485, plain, (![C_137, B_136]: (~v1_xboole_0(C_137) | v1_xboole_0(k2_zfmisc_1(B_136, C_137)))), inference(resolution, [status(thm)], [c_466, c_2])).
% 3.28/1.52  tff(c_434, plain, (![A_121, B_122, C_123]: (r2_hidden(k1_mcart_1(A_121), B_122) | ~r2_hidden(A_121, k2_zfmisc_1(B_122, C_123)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.28/1.52  tff(c_501, plain, (![B_147, C_148]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_147, C_148))), B_147) | v1_xboole_0(k2_zfmisc_1(B_147, C_148)))), inference(resolution, [status(thm)], [c_4, c_434])).
% 3.28/1.52  tff(c_555, plain, (![B_158, C_159]: (~v1_xboole_0(B_158) | v1_xboole_0(k2_zfmisc_1(B_158, C_159)))), inference(resolution, [status(thm)], [c_501, c_2])).
% 3.28/1.52  tff(c_559, plain, (![A_160, B_161, C_162]: (~v1_xboole_0(k2_zfmisc_1(A_160, B_161)) | v1_xboole_0(k3_zfmisc_1(A_160, B_161, C_162)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_555])).
% 3.28/1.52  tff(c_47, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_28, c_2])).
% 3.28/1.52  tff(c_563, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_559, c_47])).
% 3.28/1.52  tff(c_586, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_485, c_563])).
% 3.28/1.52  tff(c_34, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.28/1.52  tff(c_408, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_397])).
% 3.28/1.52  tff(c_77, plain, (![A_47, B_48, C_49]: (k2_zfmisc_1(k2_zfmisc_1(A_47, B_48), C_49)=k3_zfmisc_1(A_47, B_48, C_49))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.28/1.52  tff(c_16, plain, (![A_14, C_16, B_15]: (r2_hidden(k2_mcart_1(A_14), C_16) | ~r2_hidden(A_14, k2_zfmisc_1(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.28/1.52  tff(c_101, plain, (![A_55, C_56, A_57, B_58]: (r2_hidden(k2_mcart_1(A_55), C_56) | ~r2_hidden(A_55, k3_zfmisc_1(A_57, B_58, C_56)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_16])).
% 3.28/1.52  tff(c_107, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_28, c_101])).
% 3.28/1.52  tff(c_112, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_107, c_2])).
% 3.28/1.52  tff(c_49, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.28/1.52  tff(c_59, plain, (r1_tarski('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_49])).
% 3.28/1.52  tff(c_26, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.28/1.52  tff(c_48, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_26])).
% 3.28/1.52  tff(c_67, plain, (![A_41, C_42, B_43]: (r2_hidden(k2_mcart_1(A_41), C_42) | ~r2_hidden(A_41, k2_zfmisc_1(B_43, C_42)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.28/1.52  tff(c_181, plain, (![B_77, C_78]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_77, C_78))), C_78) | v1_xboole_0(k2_zfmisc_1(B_77, C_78)))), inference(resolution, [status(thm)], [c_4, c_67])).
% 3.28/1.52  tff(c_217, plain, (![C_80, B_81]: (~v1_xboole_0(C_80) | v1_xboole_0(k2_zfmisc_1(B_81, C_80)))), inference(resolution, [status(thm)], [c_181, c_2])).
% 3.28/1.52  tff(c_72, plain, (![A_44, B_45, C_46]: (r2_hidden(k1_mcart_1(A_44), B_45) | ~r2_hidden(A_44, k2_zfmisc_1(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.28/1.52  tff(c_113, plain, (![B_59, C_60]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_59, C_60))), B_59) | v1_xboole_0(k2_zfmisc_1(B_59, C_60)))), inference(resolution, [status(thm)], [c_4, c_72])).
% 3.28/1.52  tff(c_141, plain, (![B_65, C_66]: (~v1_xboole_0(B_65) | v1_xboole_0(k2_zfmisc_1(B_65, C_66)))), inference(resolution, [status(thm)], [c_113, c_2])).
% 3.28/1.52  tff(c_145, plain, (![A_67, B_68, C_69]: (~v1_xboole_0(k2_zfmisc_1(A_67, B_68)) | v1_xboole_0(k3_zfmisc_1(A_67, B_68, C_69)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_141])).
% 3.28/1.52  tff(c_149, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_145, c_47])).
% 3.28/1.52  tff(c_224, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_217, c_149])).
% 3.28/1.52  tff(c_60, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_49])).
% 3.28/1.52  tff(c_134, plain, (![B_59, C_60]: (~v1_xboole_0(B_59) | v1_xboole_0(k2_zfmisc_1(B_59, C_60)))), inference(resolution, [status(thm)], [c_113, c_2])).
% 3.28/1.52  tff(c_153, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_134, c_149])).
% 3.28/1.52  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.28/1.52  tff(c_61, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_49])).
% 3.28/1.52  tff(c_30, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.28/1.52  tff(c_136, plain, (![A_61, B_62, C_63, D_64]: (k7_mcart_1(A_61, B_62, C_63, D_64)=k2_mcart_1(D_64) | ~m1_subset_1(D_64, k3_zfmisc_1(A_61, B_62, C_63)) | k1_xboole_0=C_63 | k1_xboole_0=B_62 | k1_xboole_0=A_61)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.28/1.52  tff(c_140, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_136])).
% 3.28/1.52  tff(c_154, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_140])).
% 3.28/1.52  tff(c_6, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.28/1.52  tff(c_96, plain, (![A_50, B_51, C_52]: (~r1_xboole_0(A_50, B_51) | ~r1_tarski(C_52, B_51) | ~r1_tarski(C_52, A_50) | v1_xboole_0(C_52))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.28/1.52  tff(c_99, plain, (![C_52, A_5]: (~r1_tarski(C_52, k1_xboole_0) | ~r1_tarski(C_52, A_5) | v1_xboole_0(C_52))), inference(resolution, [status(thm)], [c_6, c_96])).
% 3.28/1.52  tff(c_166, plain, (![C_71, A_72]: (~r1_tarski(C_71, '#skF_2') | ~r1_tarski(C_71, A_72) | v1_xboole_0(C_71))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_99])).
% 3.28/1.52  tff(c_168, plain, (![A_72]: (~r1_tarski('#skF_5', A_72) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_61, c_166])).
% 3.28/1.52  tff(c_171, plain, (![A_72]: (~r1_tarski('#skF_5', A_72))), inference(negUnitSimplification, [status(thm)], [c_153, c_168])).
% 3.28/1.52  tff(c_173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_61])).
% 3.28/1.52  tff(c_175, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_140])).
% 3.28/1.52  tff(c_176, plain, (![A_73, B_74, C_75, D_76]: (k5_mcart_1(A_73, B_74, C_75, D_76)=k1_mcart_1(k1_mcart_1(D_76)) | ~m1_subset_1(D_76, k3_zfmisc_1(A_73, B_74, C_75)) | k1_xboole_0=C_75 | k1_xboole_0=B_74 | k1_xboole_0=A_73)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.28/1.52  tff(c_180, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_176])).
% 3.28/1.52  tff(c_202, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_175, c_180])).
% 3.28/1.52  tff(c_203, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_202])).
% 3.28/1.52  tff(c_239, plain, (![C_89, A_90]: (~r1_tarski(C_89, '#skF_3') | ~r1_tarski(C_89, A_90) | v1_xboole_0(C_89))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_99])).
% 3.28/1.52  tff(c_241, plain, (![A_90]: (~r1_tarski('#skF_6', A_90) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_60, c_239])).
% 3.28/1.52  tff(c_244, plain, (![A_90]: (~r1_tarski('#skF_6', A_90))), inference(negUnitSimplification, [status(thm)], [c_224, c_241])).
% 3.28/1.52  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_244, c_60])).
% 3.28/1.52  tff(c_247, plain, (k1_xboole_0='#skF_4' | k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_202])).
% 3.28/1.52  tff(c_274, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_247])).
% 3.28/1.52  tff(c_18, plain, (![A_14, B_15, C_16]: (r2_hidden(k1_mcart_1(A_14), B_15) | ~r2_hidden(A_14, k2_zfmisc_1(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.28/1.52  tff(c_340, plain, (![A_107, A_108, B_109, C_110]: (r2_hidden(k1_mcart_1(A_107), k2_zfmisc_1(A_108, B_109)) | ~r2_hidden(A_107, k3_zfmisc_1(A_108, B_109, C_110)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_18])).
% 3.28/1.52  tff(c_357, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_340])).
% 3.28/1.52  tff(c_360, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_357, c_18])).
% 3.28/1.52  tff(c_367, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_360])).
% 3.28/1.52  tff(c_369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_367])).
% 3.28/1.52  tff(c_370, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_247])).
% 3.28/1.52  tff(c_387, plain, (![C_112, A_113]: (~r1_tarski(C_112, '#skF_4') | ~r1_tarski(C_112, A_113) | v1_xboole_0(C_112))), inference(demodulation, [status(thm), theory('equality')], [c_370, c_99])).
% 3.28/1.52  tff(c_389, plain, (![A_113]: (~r1_tarski('#skF_7', A_113) | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_59, c_387])).
% 3.28/1.52  tff(c_392, plain, (![A_113]: (~r1_tarski('#skF_7', A_113))), inference(negUnitSimplification, [status(thm)], [c_112, c_389])).
% 3.28/1.52  tff(c_394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_392, c_59])).
% 3.28/1.52  tff(c_396, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 3.28/1.52  tff(c_413, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_396, c_2])).
% 3.28/1.52  tff(c_409, plain, (r1_tarski('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_397])).
% 3.28/1.52  tff(c_487, plain, (![A_138, B_139, C_140, D_141]: (k7_mcart_1(A_138, B_139, C_140, D_141)=k2_mcart_1(D_141) | ~m1_subset_1(D_141, k3_zfmisc_1(A_138, B_139, C_140)) | k1_xboole_0=C_140 | k1_xboole_0=B_139 | k1_xboole_0=A_138)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.28/1.52  tff(c_491, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_487])).
% 3.28/1.52  tff(c_524, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_491])).
% 3.28/1.52  tff(c_461, plain, (![A_131, B_132, C_133]: (~r1_xboole_0(A_131, B_132) | ~r1_tarski(C_133, B_132) | ~r1_tarski(C_133, A_131) | v1_xboole_0(C_133))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.28/1.52  tff(c_464, plain, (![C_133, A_5]: (~r1_tarski(C_133, k1_xboole_0) | ~r1_tarski(C_133, A_5) | v1_xboole_0(C_133))), inference(resolution, [status(thm)], [c_6, c_461])).
% 3.28/1.52  tff(c_540, plain, (![C_152, A_153]: (~r1_tarski(C_152, '#skF_2') | ~r1_tarski(C_152, A_153) | v1_xboole_0(C_152))), inference(demodulation, [status(thm), theory('equality')], [c_524, c_464])).
% 3.28/1.52  tff(c_542, plain, (![A_153]: (~r1_tarski('#skF_5', A_153) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_409, c_540])).
% 3.28/1.52  tff(c_545, plain, (![A_153]: (~r1_tarski('#skF_5', A_153))), inference(negUnitSimplification, [status(thm)], [c_413, c_542])).
% 3.28/1.52  tff(c_547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_545, c_409])).
% 3.28/1.52  tff(c_549, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_491])).
% 3.28/1.52  tff(c_550, plain, (![A_154, B_155, C_156, D_157]: (k6_mcart_1(A_154, B_155, C_156, D_157)=k2_mcart_1(k1_mcart_1(D_157)) | ~m1_subset_1(D_157, k3_zfmisc_1(A_154, B_155, C_156)) | k1_xboole_0=C_156 | k1_xboole_0=B_155 | k1_xboole_0=A_154)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.28/1.52  tff(c_554, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_550])).
% 3.28/1.52  tff(c_564, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_549, c_554])).
% 3.28/1.52  tff(c_565, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_564])).
% 3.28/1.52  tff(c_596, plain, (![C_168, A_169]: (~r1_tarski(C_168, '#skF_3') | ~r1_tarski(C_168, A_169) | v1_xboole_0(C_168))), inference(demodulation, [status(thm), theory('equality')], [c_565, c_464])).
% 3.28/1.52  tff(c_598, plain, (![A_169]: (~r1_tarski('#skF_6', A_169) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_408, c_596])).
% 3.28/1.52  tff(c_601, plain, (![A_169]: (~r1_tarski('#skF_6', A_169))), inference(negUnitSimplification, [status(thm)], [c_586, c_598])).
% 3.28/1.52  tff(c_603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_601, c_408])).
% 3.28/1.52  tff(c_605, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_564])).
% 3.28/1.52  tff(c_548, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_491])).
% 3.28/1.52  tff(c_619, plain, (k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_605, c_548])).
% 3.28/1.52  tff(c_620, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_619])).
% 3.28/1.52  tff(c_395, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_26])).
% 3.28/1.52  tff(c_460, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_395])).
% 3.28/1.52  tff(c_621, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_620, c_460])).
% 3.28/1.52  tff(c_624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_454, c_621])).
% 3.28/1.52  tff(c_625, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_619])).
% 3.28/1.52  tff(c_650, plain, (![C_175, A_176]: (~r1_tarski(C_175, '#skF_4') | ~r1_tarski(C_175, A_176) | v1_xboole_0(C_175))), inference(demodulation, [status(thm), theory('equality')], [c_625, c_464])).
% 3.28/1.52  tff(c_652, plain, (![A_176]: (~r1_tarski('#skF_7', A_176) | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_407, c_650])).
% 3.28/1.52  tff(c_655, plain, (![A_176]: (~r1_tarski('#skF_7', A_176))), inference(negUnitSimplification, [status(thm)], [c_459, c_652])).
% 3.28/1.52  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_655, c_407])).
% 3.28/1.52  tff(c_658, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_395])).
% 3.28/1.52  tff(c_674, plain, (![B_186, C_187]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_186, C_187))), C_187) | v1_xboole_0(k2_zfmisc_1(B_186, C_187)))), inference(resolution, [status(thm)], [c_4, c_441])).
% 3.28/1.52  tff(c_693, plain, (![C_187, B_186]: (~v1_xboole_0(C_187) | v1_xboole_0(k2_zfmisc_1(B_186, C_187)))), inference(resolution, [status(thm)], [c_674, c_2])).
% 3.28/1.52  tff(c_704, plain, (![B_193, C_194]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_193, C_194))), B_193) | v1_xboole_0(k2_zfmisc_1(B_193, C_194)))), inference(resolution, [status(thm)], [c_4, c_434])).
% 3.28/1.52  tff(c_727, plain, (![B_195, C_196]: (~v1_xboole_0(B_195) | v1_xboole_0(k2_zfmisc_1(B_195, C_196)))), inference(resolution, [status(thm)], [c_704, c_2])).
% 3.28/1.52  tff(c_736, plain, (![A_201, B_202, C_203]: (~v1_xboole_0(k2_zfmisc_1(A_201, B_202)) | v1_xboole_0(k3_zfmisc_1(A_201, B_202, C_203)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_727])).
% 3.28/1.52  tff(c_740, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_736, c_47])).
% 3.28/1.52  tff(c_748, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_693, c_740])).
% 3.28/1.52  tff(c_669, plain, (![A_182, B_183, C_184, D_185]: (k7_mcart_1(A_182, B_183, C_184, D_185)=k2_mcart_1(D_185) | ~m1_subset_1(D_185, k3_zfmisc_1(A_182, B_183, C_184)) | k1_xboole_0=C_184 | k1_xboole_0=B_183 | k1_xboole_0=A_182)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.28/1.52  tff(c_673, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_669])).
% 3.28/1.52  tff(c_749, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_673])).
% 3.28/1.52  tff(c_664, plain, (![A_177, B_178, C_179]: (~r1_xboole_0(A_177, B_178) | ~r1_tarski(C_179, B_178) | ~r1_tarski(C_179, A_177) | v1_xboole_0(C_179))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.28/1.52  tff(c_667, plain, (![C_179, A_5]: (~r1_tarski(C_179, k1_xboole_0) | ~r1_tarski(C_179, A_5) | v1_xboole_0(C_179))), inference(resolution, [status(thm)], [c_6, c_664])).
% 3.28/1.52  tff(c_762, plain, (![C_205, A_206]: (~r1_tarski(C_205, '#skF_2') | ~r1_tarski(C_205, A_206) | v1_xboole_0(C_205))), inference(demodulation, [status(thm), theory('equality')], [c_749, c_667])).
% 3.28/1.52  tff(c_764, plain, (![A_206]: (~r1_tarski('#skF_5', A_206) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_409, c_762])).
% 3.28/1.52  tff(c_767, plain, (![A_206]: (~r1_tarski('#skF_5', A_206))), inference(negUnitSimplification, [status(thm)], [c_413, c_764])).
% 3.28/1.52  tff(c_769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_767, c_409])).
% 3.28/1.52  tff(c_771, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_673])).
% 3.28/1.52  tff(c_731, plain, (![A_197, B_198, C_199, D_200]: (k5_mcart_1(A_197, B_198, C_199, D_200)=k1_mcart_1(k1_mcart_1(D_200)) | ~m1_subset_1(D_200, k3_zfmisc_1(A_197, B_198, C_199)) | k1_xboole_0=C_199 | k1_xboole_0=B_198 | k1_xboole_0=A_197)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.28/1.52  tff(c_735, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_731])).
% 3.28/1.52  tff(c_817, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_771, c_735])).
% 3.28/1.52  tff(c_818, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_817])).
% 3.28/1.52  tff(c_833, plain, (![C_216, A_217]: (~r1_tarski(C_216, '#skF_3') | ~r1_tarski(C_216, A_217) | v1_xboole_0(C_216))), inference(demodulation, [status(thm), theory('equality')], [c_818, c_667])).
% 3.28/1.52  tff(c_835, plain, (![A_217]: (~r1_tarski('#skF_6', A_217) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_408, c_833])).
% 3.28/1.52  tff(c_838, plain, (![A_217]: (~r1_tarski('#skF_6', A_217))), inference(negUnitSimplification, [status(thm)], [c_748, c_835])).
% 3.28/1.52  tff(c_840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_838, c_408])).
% 3.28/1.52  tff(c_842, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_817])).
% 3.28/1.52  tff(c_772, plain, (![A_207, B_208, C_209, D_210]: (k6_mcart_1(A_207, B_208, C_209, D_210)=k2_mcart_1(k1_mcart_1(D_210)) | ~m1_subset_1(D_210, k3_zfmisc_1(A_207, B_208, C_209)) | k1_xboole_0=C_209 | k1_xboole_0=B_208 | k1_xboole_0=A_207)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.28/1.52  tff(c_775, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_772])).
% 3.28/1.52  tff(c_778, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_771, c_775])).
% 3.28/1.52  tff(c_849, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_842, c_778])).
% 3.28/1.52  tff(c_850, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_849])).
% 3.28/1.52  tff(c_866, plain, (![C_219, A_220]: (~r1_tarski(C_219, '#skF_4') | ~r1_tarski(C_219, A_220) | v1_xboole_0(C_219))), inference(demodulation, [status(thm), theory('equality')], [c_850, c_667])).
% 3.28/1.52  tff(c_868, plain, (![A_220]: (~r1_tarski('#skF_7', A_220) | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_407, c_866])).
% 3.28/1.52  tff(c_871, plain, (![A_220]: (~r1_tarski('#skF_7', A_220))), inference(negUnitSimplification, [status(thm)], [c_459, c_868])).
% 3.28/1.52  tff(c_892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_871, c_407])).
% 3.28/1.52  tff(c_893, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_849])).
% 3.28/1.52  tff(c_899, plain, (![A_225, A_226, B_227, C_228]: (r2_hidden(k1_mcart_1(A_225), k2_zfmisc_1(A_226, B_227)) | ~r2_hidden(A_225, k3_zfmisc_1(A_226, B_227, C_228)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_434])).
% 3.28/1.52  tff(c_916, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_899])).
% 3.28/1.52  tff(c_919, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_916, c_16])).
% 3.28/1.52  tff(c_926, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_893, c_919])).
% 3.28/1.52  tff(c_928, plain, $false, inference(negUnitSimplification, [status(thm)], [c_658, c_926])).
% 3.28/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.52  
% 3.28/1.52  Inference rules
% 3.28/1.52  ----------------------
% 3.28/1.52  #Ref     : 0
% 3.28/1.52  #Sup     : 195
% 3.28/1.52  #Fact    : 0
% 3.28/1.52  #Define  : 0
% 3.28/1.52  #Split   : 16
% 3.28/1.52  #Chain   : 0
% 3.28/1.52  #Close   : 0
% 3.28/1.52  
% 3.28/1.52  Ordering : KBO
% 3.28/1.52  
% 3.28/1.52  Simplification rules
% 3.28/1.52  ----------------------
% 3.28/1.52  #Subsume      : 17
% 3.28/1.52  #Demod        : 141
% 3.28/1.52  #Tautology    : 52
% 3.28/1.52  #SimpNegUnit  : 32
% 3.28/1.52  #BackRed      : 66
% 3.28/1.52  
% 3.28/1.52  #Partial instantiations: 0
% 3.28/1.52  #Strategies tried      : 1
% 3.28/1.52  
% 3.28/1.52  Timing (in seconds)
% 3.28/1.52  ----------------------
% 3.28/1.53  Preprocessing        : 0.30
% 3.28/1.53  Parsing              : 0.16
% 3.28/1.53  CNF conversion       : 0.02
% 3.28/1.53  Main loop            : 0.42
% 3.28/1.53  Inferencing          : 0.15
% 3.28/1.53  Reduction            : 0.14
% 3.28/1.53  Demodulation         : 0.09
% 3.28/1.53  BG Simplification    : 0.02
% 3.28/1.53  Subsumption          : 0.06
% 3.28/1.53  Abstraction          : 0.02
% 3.28/1.53  MUC search           : 0.00
% 3.28/1.53  Cooper               : 0.00
% 3.28/1.53  Total                : 0.78
% 3.28/1.53  Index Insertion      : 0.00
% 3.28/1.53  Index Deletion       : 0.00
% 3.28/1.53  Index Matching       : 0.00
% 3.28/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
