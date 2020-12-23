%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:10 EST 2020

% Result     : Theorem 11.94s
% Output     : CNFRefutation 11.94s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 763 expanded)
%              Number of leaves         :   32 ( 263 expanded)
%              Depth                    :   20
%              Number of atoms          :  203 (1793 expanded)
%              Number of equality atoms :   35 ( 427 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_115,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_119,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_115])).

tff(c_40,plain,
    ( k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7'
    | r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_63,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_128,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_63])).

tff(c_26,plain,(
    ! [A_30,B_31] : v1_relat_1(k2_zfmisc_1(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_34,c_48])).

tff(c_54,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_51])).

tff(c_77,plain,(
    ! [C_65,B_66,A_67] :
      ( v5_relat_1(C_65,B_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_81,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_34,c_77])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [A_54,B_55] :
      ( ~ r2_hidden('#skF_1'(A_54,B_55),B_55)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_82,plain,(
    ! [C_68,B_69,A_70] :
      ( r2_hidden(C_68,B_69)
      | ~ r2_hidden(C_68,A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_106,plain,(
    ! [A_77,B_78,B_79] :
      ( r2_hidden('#skF_1'(A_77,B_78),B_79)
      | ~ r1_tarski(A_77,B_79)
      | r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1152,plain,(
    ! [A_173,B_174,B_175,B_176] :
      ( r2_hidden('#skF_1'(A_173,B_174),B_175)
      | ~ r1_tarski(B_176,B_175)
      | ~ r1_tarski(A_173,B_176)
      | r1_tarski(A_173,B_174) ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_3538,plain,(
    ! [A_299,B_300,A_301,B_302] :
      ( r2_hidden('#skF_1'(A_299,B_300),A_301)
      | ~ r1_tarski(A_299,k2_relat_1(B_302))
      | r1_tarski(A_299,B_300)
      | ~ v5_relat_1(B_302,A_301)
      | ~ v1_relat_1(B_302) ) ),
    inference(resolution,[status(thm)],[c_12,c_1152])).

tff(c_3571,plain,(
    ! [B_303,B_304,A_305] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_303),B_304),A_305)
      | r1_tarski(k2_relat_1(B_303),B_304)
      | ~ v5_relat_1(B_303,A_305)
      | ~ v1_relat_1(B_303) ) ),
    inference(resolution,[status(thm)],[c_61,c_3538])).

tff(c_46,plain,(
    ! [D_44] :
      ( r2_hidden(k4_tarski('#skF_9'(D_44),D_44),'#skF_8')
      | ~ r2_hidden(D_44,'#skF_7')
      | k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_134,plain,(
    ! [D_44] :
      ( r2_hidden(k4_tarski('#skF_9'(D_44),D_44),'#skF_8')
      | ~ r2_hidden(D_44,'#skF_7')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_46])).

tff(c_136,plain,(
    ! [D_87] :
      ( r2_hidden(k4_tarski('#skF_9'(D_87),D_87),'#skF_8')
      | ~ r2_hidden(D_87,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_134])).

tff(c_16,plain,(
    ! [C_26,A_11,D_29] :
      ( r2_hidden(C_26,k2_relat_1(A_11))
      | ~ r2_hidden(k4_tarski(D_29,C_26),A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_144,plain,(
    ! [D_88] :
      ( r2_hidden(D_88,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_88,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_136,c_16])).

tff(c_158,plain,(
    ! [D_89,B_90] :
      ( r2_hidden(D_89,B_90)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_90)
      | ~ r2_hidden(D_89,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_144,c_2])).

tff(c_161,plain,(
    ! [D_89,A_9] :
      ( r2_hidden(D_89,A_9)
      | ~ r2_hidden(D_89,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_9)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_12,c_158])).

tff(c_167,plain,(
    ! [D_89,A_9] :
      ( r2_hidden(D_89,A_9)
      | ~ r2_hidden(D_89,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_161])).

tff(c_12269,plain,(
    ! [B_576,B_577,A_578] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_576),B_577),A_578)
      | ~ v5_relat_1('#skF_8',A_578)
      | r1_tarski(k2_relat_1(B_576),B_577)
      | ~ v5_relat_1(B_576,'#skF_7')
      | ~ v1_relat_1(B_576) ) ),
    inference(resolution,[status(thm)],[c_3571,c_167])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12368,plain,(
    ! [A_578,B_576] :
      ( ~ v5_relat_1('#skF_8',A_578)
      | r1_tarski(k2_relat_1(B_576),A_578)
      | ~ v5_relat_1(B_576,'#skF_7')
      | ~ v1_relat_1(B_576) ) ),
    inference(resolution,[status(thm)],[c_12269,c_4])).

tff(c_251,plain,(
    ! [A_100] :
      ( r1_tarski(A_100,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_100,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_144,c_4])).

tff(c_261,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_251])).

tff(c_446,plain,(
    ! [A_118,B_119] :
      ( r2_hidden(k4_tarski('#skF_3'(A_118,B_119),'#skF_2'(A_118,B_119)),A_118)
      | r2_hidden('#skF_4'(A_118,B_119),B_119)
      | k2_relat_1(A_118) = B_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_695,plain,(
    ! [A_143,B_144] :
      ( r2_hidden('#skF_2'(A_143,B_144),k2_relat_1(A_143))
      | r2_hidden('#skF_4'(A_143,B_144),B_144)
      | k2_relat_1(A_143) = B_144 ) ),
    inference(resolution,[status(thm)],[c_446,c_16])).

tff(c_1528,plain,(
    ! [A_198,B_199,B_200] :
      ( r2_hidden('#skF_2'(A_198,B_199),B_200)
      | ~ r1_tarski(k2_relat_1(A_198),B_200)
      | r2_hidden('#skF_4'(A_198,B_199),B_199)
      | k2_relat_1(A_198) = B_199 ) ),
    inference(resolution,[status(thm)],[c_695,c_2])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( ~ r2_hidden('#skF_2'(A_11,B_12),B_12)
      | r2_hidden('#skF_4'(A_11,B_12),B_12)
      | k2_relat_1(A_11) = B_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1578,plain,(
    ! [A_201,B_202] :
      ( ~ r1_tarski(k2_relat_1(A_201),B_202)
      | r2_hidden('#skF_4'(A_201,B_202),B_202)
      | k2_relat_1(A_201) = B_202 ) ),
    inference(resolution,[status(thm)],[c_1528,c_22])).

tff(c_3079,plain,(
    ! [A_264,A_265] :
      ( r2_hidden('#skF_4'(A_264,'#skF_7'),A_265)
      | ~ v5_relat_1('#skF_8',A_265)
      | ~ r1_tarski(k2_relat_1(A_264),'#skF_7')
      | k2_relat_1(A_264) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_1578,c_167])).

tff(c_14821,plain,(
    ! [A_640,B_641,A_642] :
      ( r2_hidden('#skF_4'(A_640,'#skF_7'),B_641)
      | ~ r1_tarski(A_642,B_641)
      | ~ v5_relat_1('#skF_8',A_642)
      | ~ r1_tarski(k2_relat_1(A_640),'#skF_7')
      | k2_relat_1(A_640) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_3079,c_2])).

tff(c_14867,plain,(
    ! [A_640] :
      ( r2_hidden('#skF_4'(A_640,'#skF_7'),k2_relat_1('#skF_8'))
      | ~ v5_relat_1('#skF_8','#skF_7')
      | ~ r1_tarski(k2_relat_1(A_640),'#skF_7')
      | k2_relat_1(A_640) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_261,c_14821])).

tff(c_14902,plain,(
    ! [A_643] :
      ( r2_hidden('#skF_4'(A_643,'#skF_7'),k2_relat_1('#skF_8'))
      | ~ r1_tarski(k2_relat_1(A_643),'#skF_7')
      | k2_relat_1(A_643) = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_14867])).

tff(c_14,plain,(
    ! [A_11,C_26] :
      ( r2_hidden(k4_tarski('#skF_5'(A_11,k2_relat_1(A_11),C_26),C_26),A_11)
      | ~ r2_hidden(C_26,k2_relat_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_567,plain,(
    ! [A_130,B_131,D_132] :
      ( r2_hidden(k4_tarski('#skF_3'(A_130,B_131),'#skF_2'(A_130,B_131)),A_130)
      | ~ r2_hidden(k4_tarski(D_132,'#skF_4'(A_130,B_131)),A_130)
      | k2_relat_1(A_130) = B_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_962,plain,(
    ! [A_158,B_159] :
      ( r2_hidden(k4_tarski('#skF_3'(A_158,B_159),'#skF_2'(A_158,B_159)),A_158)
      | k2_relat_1(A_158) = B_159
      | ~ r2_hidden('#skF_4'(A_158,B_159),k2_relat_1(A_158)) ) ),
    inference(resolution,[status(thm)],[c_14,c_567])).

tff(c_1329,plain,(
    ! [A_186,B_187] :
      ( r2_hidden('#skF_2'(A_186,B_187),k2_relat_1(A_186))
      | k2_relat_1(A_186) = B_187
      | ~ r2_hidden('#skF_4'(A_186,B_187),k2_relat_1(A_186)) ) ),
    inference(resolution,[status(thm)],[c_962,c_16])).

tff(c_1354,plain,(
    ! [A_186,B_187,B_2] :
      ( r2_hidden('#skF_2'(A_186,B_187),B_2)
      | ~ r1_tarski(k2_relat_1(A_186),B_2)
      | k2_relat_1(A_186) = B_187
      | ~ r2_hidden('#skF_4'(A_186,B_187),k2_relat_1(A_186)) ) ),
    inference(resolution,[status(thm)],[c_1329,c_2])).

tff(c_14907,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_14902,c_1354])).

tff(c_14920,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_128,c_14907])).

tff(c_14927,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_14920])).

tff(c_14930,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12368,c_14927])).

tff(c_14937,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_81,c_14930])).

tff(c_14939,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_14920])).

tff(c_15058,plain,(
    ! [B_644] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_644)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_644) ) ),
    inference(splitRight,[status(thm)],[c_14920])).

tff(c_15117,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_15058,c_22])).

tff(c_15148,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14939,c_15117])).

tff(c_15149,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_15148])).

tff(c_142,plain,(
    ! [D_87,B_2] :
      ( r2_hidden(k4_tarski('#skF_9'(D_87),D_87),B_2)
      | ~ r1_tarski('#skF_8',B_2)
      | ~ r2_hidden(D_87,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_136,c_2])).

tff(c_18,plain,(
    ! [A_11,B_12,D_25] :
      ( ~ r2_hidden('#skF_2'(A_11,B_12),B_12)
      | ~ r2_hidden(k4_tarski(D_25,'#skF_4'(A_11,B_12)),A_11)
      | k2_relat_1(A_11) = B_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_15113,plain,(
    ! [D_25] :
      ( ~ r2_hidden(k4_tarski(D_25,'#skF_4'('#skF_8','#skF_7')),'#skF_8')
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_15058,c_18])).

tff(c_15144,plain,(
    ! [D_25] :
      ( ~ r2_hidden(k4_tarski(D_25,'#skF_4'('#skF_8','#skF_7')),'#skF_8')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14939,c_15113])).

tff(c_15265,plain,(
    ! [D_647] : ~ r2_hidden(k4_tarski(D_647,'#skF_4'('#skF_8','#skF_7')),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_15144])).

tff(c_15277,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_142,c_15265])).

tff(c_15291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15149,c_61,c_15277])).

tff(c_15292,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_15293,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_15344,plain,(
    ! [A_667,B_668,C_669] :
      ( k2_relset_1(A_667,B_668,C_669) = k2_relat_1(C_669)
      | ~ m1_subset_1(C_669,k1_zfmisc_1(k2_zfmisc_1(A_667,B_668))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_15347,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_15344])).

tff(c_15349,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15293,c_15347])).

tff(c_15425,plain,(
    ! [A_680,C_681] :
      ( r2_hidden(k4_tarski('#skF_5'(A_680,k2_relat_1(A_680),C_681),C_681),A_680)
      | ~ r2_hidden(C_681,k2_relat_1(A_680)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ! [E_47] :
      ( k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7'
      | ~ r2_hidden(k4_tarski(E_47,'#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_15294,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_15300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15293,c_15294])).

tff(c_15301,plain,(
    ! [E_47] : ~ r2_hidden(k4_tarski(E_47,'#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_15434,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_15425,c_15301])).

tff(c_15443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15292,c_15349,c_15434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.94/4.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.94/4.68  
% 11.94/4.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.94/4.68  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 11.94/4.68  
% 11.94/4.68  %Foreground sorts:
% 11.94/4.68  
% 11.94/4.68  
% 11.94/4.68  %Background operators:
% 11.94/4.68  
% 11.94/4.68  
% 11.94/4.68  %Foreground operators:
% 11.94/4.68  tff('#skF_9', type, '#skF_9': $i > $i).
% 11.94/4.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 11.94/4.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.94/4.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.94/4.68  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.94/4.68  tff('#skF_7', type, '#skF_7': $i).
% 11.94/4.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.94/4.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.94/4.68  tff('#skF_10', type, '#skF_10': $i).
% 11.94/4.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 11.94/4.68  tff('#skF_6', type, '#skF_6': $i).
% 11.94/4.68  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 11.94/4.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 11.94/4.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.94/4.68  tff('#skF_8', type, '#skF_8': $i).
% 11.94/4.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.94/4.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.94/4.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.94/4.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.94/4.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.94/4.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 11.94/4.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.94/4.68  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.94/4.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.94/4.68  
% 11.94/4.70  tff(f_78, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 11.94/4.70  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.94/4.70  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.94/4.70  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.94/4.70  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.94/4.70  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.94/4.70  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 11.94/4.70  tff(f_53, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 11.94/4.70  tff(c_34, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.94/4.70  tff(c_115, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.94/4.70  tff(c_119, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_115])).
% 11.94/4.70  tff(c_40, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7' | r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.94/4.70  tff(c_63, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_40])).
% 11.94/4.70  tff(c_128, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_63])).
% 11.94/4.70  tff(c_26, plain, (![A_30, B_31]: (v1_relat_1(k2_zfmisc_1(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.94/4.70  tff(c_48, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_39])).
% 11.94/4.70  tff(c_51, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_34, c_48])).
% 11.94/4.70  tff(c_54, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_51])).
% 11.94/4.70  tff(c_77, plain, (![C_65, B_66, A_67]: (v5_relat_1(C_65, B_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.94/4.70  tff(c_81, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_34, c_77])).
% 11.94/4.70  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.94/4.70  tff(c_56, plain, (![A_54, B_55]: (~r2_hidden('#skF_1'(A_54, B_55), B_55) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.94/4.70  tff(c_61, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_56])).
% 11.94/4.70  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 11.94/4.70  tff(c_82, plain, (![C_68, B_69, A_70]: (r2_hidden(C_68, B_69) | ~r2_hidden(C_68, A_70) | ~r1_tarski(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.94/4.70  tff(c_106, plain, (![A_77, B_78, B_79]: (r2_hidden('#skF_1'(A_77, B_78), B_79) | ~r1_tarski(A_77, B_79) | r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_6, c_82])).
% 11.94/4.70  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.94/4.70  tff(c_1152, plain, (![A_173, B_174, B_175, B_176]: (r2_hidden('#skF_1'(A_173, B_174), B_175) | ~r1_tarski(B_176, B_175) | ~r1_tarski(A_173, B_176) | r1_tarski(A_173, B_174))), inference(resolution, [status(thm)], [c_106, c_2])).
% 11.94/4.70  tff(c_3538, plain, (![A_299, B_300, A_301, B_302]: (r2_hidden('#skF_1'(A_299, B_300), A_301) | ~r1_tarski(A_299, k2_relat_1(B_302)) | r1_tarski(A_299, B_300) | ~v5_relat_1(B_302, A_301) | ~v1_relat_1(B_302))), inference(resolution, [status(thm)], [c_12, c_1152])).
% 11.94/4.70  tff(c_3571, plain, (![B_303, B_304, A_305]: (r2_hidden('#skF_1'(k2_relat_1(B_303), B_304), A_305) | r1_tarski(k2_relat_1(B_303), B_304) | ~v5_relat_1(B_303, A_305) | ~v1_relat_1(B_303))), inference(resolution, [status(thm)], [c_61, c_3538])).
% 11.94/4.70  tff(c_46, plain, (![D_44]: (r2_hidden(k4_tarski('#skF_9'(D_44), D_44), '#skF_8') | ~r2_hidden(D_44, '#skF_7') | k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.94/4.70  tff(c_134, plain, (![D_44]: (r2_hidden(k4_tarski('#skF_9'(D_44), D_44), '#skF_8') | ~r2_hidden(D_44, '#skF_7') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_46])).
% 11.94/4.70  tff(c_136, plain, (![D_87]: (r2_hidden(k4_tarski('#skF_9'(D_87), D_87), '#skF_8') | ~r2_hidden(D_87, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_128, c_134])).
% 11.94/4.70  tff(c_16, plain, (![C_26, A_11, D_29]: (r2_hidden(C_26, k2_relat_1(A_11)) | ~r2_hidden(k4_tarski(D_29, C_26), A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.94/4.70  tff(c_144, plain, (![D_88]: (r2_hidden(D_88, k2_relat_1('#skF_8')) | ~r2_hidden(D_88, '#skF_7'))), inference(resolution, [status(thm)], [c_136, c_16])).
% 11.94/4.70  tff(c_158, plain, (![D_89, B_90]: (r2_hidden(D_89, B_90) | ~r1_tarski(k2_relat_1('#skF_8'), B_90) | ~r2_hidden(D_89, '#skF_7'))), inference(resolution, [status(thm)], [c_144, c_2])).
% 11.94/4.70  tff(c_161, plain, (![D_89, A_9]: (r2_hidden(D_89, A_9) | ~r2_hidden(D_89, '#skF_7') | ~v5_relat_1('#skF_8', A_9) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_12, c_158])).
% 11.94/4.70  tff(c_167, plain, (![D_89, A_9]: (r2_hidden(D_89, A_9) | ~r2_hidden(D_89, '#skF_7') | ~v5_relat_1('#skF_8', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_161])).
% 11.94/4.70  tff(c_12269, plain, (![B_576, B_577, A_578]: (r2_hidden('#skF_1'(k2_relat_1(B_576), B_577), A_578) | ~v5_relat_1('#skF_8', A_578) | r1_tarski(k2_relat_1(B_576), B_577) | ~v5_relat_1(B_576, '#skF_7') | ~v1_relat_1(B_576))), inference(resolution, [status(thm)], [c_3571, c_167])).
% 11.94/4.70  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.94/4.70  tff(c_12368, plain, (![A_578, B_576]: (~v5_relat_1('#skF_8', A_578) | r1_tarski(k2_relat_1(B_576), A_578) | ~v5_relat_1(B_576, '#skF_7') | ~v1_relat_1(B_576))), inference(resolution, [status(thm)], [c_12269, c_4])).
% 11.94/4.70  tff(c_251, plain, (![A_100]: (r1_tarski(A_100, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_100, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_144, c_4])).
% 11.94/4.70  tff(c_261, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_251])).
% 11.94/4.70  tff(c_446, plain, (![A_118, B_119]: (r2_hidden(k4_tarski('#skF_3'(A_118, B_119), '#skF_2'(A_118, B_119)), A_118) | r2_hidden('#skF_4'(A_118, B_119), B_119) | k2_relat_1(A_118)=B_119)), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.94/4.70  tff(c_695, plain, (![A_143, B_144]: (r2_hidden('#skF_2'(A_143, B_144), k2_relat_1(A_143)) | r2_hidden('#skF_4'(A_143, B_144), B_144) | k2_relat_1(A_143)=B_144)), inference(resolution, [status(thm)], [c_446, c_16])).
% 11.94/4.70  tff(c_1528, plain, (![A_198, B_199, B_200]: (r2_hidden('#skF_2'(A_198, B_199), B_200) | ~r1_tarski(k2_relat_1(A_198), B_200) | r2_hidden('#skF_4'(A_198, B_199), B_199) | k2_relat_1(A_198)=B_199)), inference(resolution, [status(thm)], [c_695, c_2])).
% 11.94/4.70  tff(c_22, plain, (![A_11, B_12]: (~r2_hidden('#skF_2'(A_11, B_12), B_12) | r2_hidden('#skF_4'(A_11, B_12), B_12) | k2_relat_1(A_11)=B_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.94/4.70  tff(c_1578, plain, (![A_201, B_202]: (~r1_tarski(k2_relat_1(A_201), B_202) | r2_hidden('#skF_4'(A_201, B_202), B_202) | k2_relat_1(A_201)=B_202)), inference(resolution, [status(thm)], [c_1528, c_22])).
% 11.94/4.70  tff(c_3079, plain, (![A_264, A_265]: (r2_hidden('#skF_4'(A_264, '#skF_7'), A_265) | ~v5_relat_1('#skF_8', A_265) | ~r1_tarski(k2_relat_1(A_264), '#skF_7') | k2_relat_1(A_264)='#skF_7')), inference(resolution, [status(thm)], [c_1578, c_167])).
% 11.94/4.70  tff(c_14821, plain, (![A_640, B_641, A_642]: (r2_hidden('#skF_4'(A_640, '#skF_7'), B_641) | ~r1_tarski(A_642, B_641) | ~v5_relat_1('#skF_8', A_642) | ~r1_tarski(k2_relat_1(A_640), '#skF_7') | k2_relat_1(A_640)='#skF_7')), inference(resolution, [status(thm)], [c_3079, c_2])).
% 11.94/4.70  tff(c_14867, plain, (![A_640]: (r2_hidden('#skF_4'(A_640, '#skF_7'), k2_relat_1('#skF_8')) | ~v5_relat_1('#skF_8', '#skF_7') | ~r1_tarski(k2_relat_1(A_640), '#skF_7') | k2_relat_1(A_640)='#skF_7')), inference(resolution, [status(thm)], [c_261, c_14821])).
% 11.94/4.70  tff(c_14902, plain, (![A_643]: (r2_hidden('#skF_4'(A_643, '#skF_7'), k2_relat_1('#skF_8')) | ~r1_tarski(k2_relat_1(A_643), '#skF_7') | k2_relat_1(A_643)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_14867])).
% 11.94/4.70  tff(c_14, plain, (![A_11, C_26]: (r2_hidden(k4_tarski('#skF_5'(A_11, k2_relat_1(A_11), C_26), C_26), A_11) | ~r2_hidden(C_26, k2_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.94/4.70  tff(c_567, plain, (![A_130, B_131, D_132]: (r2_hidden(k4_tarski('#skF_3'(A_130, B_131), '#skF_2'(A_130, B_131)), A_130) | ~r2_hidden(k4_tarski(D_132, '#skF_4'(A_130, B_131)), A_130) | k2_relat_1(A_130)=B_131)), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.94/4.70  tff(c_962, plain, (![A_158, B_159]: (r2_hidden(k4_tarski('#skF_3'(A_158, B_159), '#skF_2'(A_158, B_159)), A_158) | k2_relat_1(A_158)=B_159 | ~r2_hidden('#skF_4'(A_158, B_159), k2_relat_1(A_158)))), inference(resolution, [status(thm)], [c_14, c_567])).
% 11.94/4.70  tff(c_1329, plain, (![A_186, B_187]: (r2_hidden('#skF_2'(A_186, B_187), k2_relat_1(A_186)) | k2_relat_1(A_186)=B_187 | ~r2_hidden('#skF_4'(A_186, B_187), k2_relat_1(A_186)))), inference(resolution, [status(thm)], [c_962, c_16])).
% 11.94/4.70  tff(c_1354, plain, (![A_186, B_187, B_2]: (r2_hidden('#skF_2'(A_186, B_187), B_2) | ~r1_tarski(k2_relat_1(A_186), B_2) | k2_relat_1(A_186)=B_187 | ~r2_hidden('#skF_4'(A_186, B_187), k2_relat_1(A_186)))), inference(resolution, [status(thm)], [c_1329, c_2])).
% 11.94/4.70  tff(c_14907, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7')), inference(resolution, [status(thm)], [c_14902, c_1354])).
% 11.94/4.70  tff(c_14920, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_128, c_128, c_14907])).
% 11.94/4.70  tff(c_14927, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_14920])).
% 11.94/4.70  tff(c_14930, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12368, c_14927])).
% 11.94/4.70  tff(c_14937, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_81, c_14930])).
% 11.94/4.70  tff(c_14939, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_14920])).
% 11.94/4.70  tff(c_15058, plain, (![B_644]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_644) | ~r1_tarski(k2_relat_1('#skF_8'), B_644))), inference(splitRight, [status(thm)], [c_14920])).
% 11.94/4.70  tff(c_15117, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_15058, c_22])).
% 11.94/4.70  tff(c_15148, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_14939, c_15117])).
% 11.94/4.70  tff(c_15149, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_128, c_15148])).
% 11.94/4.70  tff(c_142, plain, (![D_87, B_2]: (r2_hidden(k4_tarski('#skF_9'(D_87), D_87), B_2) | ~r1_tarski('#skF_8', B_2) | ~r2_hidden(D_87, '#skF_7'))), inference(resolution, [status(thm)], [c_136, c_2])).
% 11.94/4.70  tff(c_18, plain, (![A_11, B_12, D_25]: (~r2_hidden('#skF_2'(A_11, B_12), B_12) | ~r2_hidden(k4_tarski(D_25, '#skF_4'(A_11, B_12)), A_11) | k2_relat_1(A_11)=B_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.94/4.70  tff(c_15113, plain, (![D_25]: (~r2_hidden(k4_tarski(D_25, '#skF_4'('#skF_8', '#skF_7')), '#skF_8') | k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_15058, c_18])).
% 11.94/4.70  tff(c_15144, plain, (![D_25]: (~r2_hidden(k4_tarski(D_25, '#skF_4'('#skF_8', '#skF_7')), '#skF_8') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14939, c_15113])).
% 11.94/4.70  tff(c_15265, plain, (![D_647]: (~r2_hidden(k4_tarski(D_647, '#skF_4'('#skF_8', '#skF_7')), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_128, c_15144])).
% 11.94/4.70  tff(c_15277, plain, (~r1_tarski('#skF_8', '#skF_8') | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_142, c_15265])).
% 11.94/4.70  tff(c_15291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15149, c_61, c_15277])).
% 11.94/4.70  tff(c_15292, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_40])).
% 11.94/4.70  tff(c_15293, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_40])).
% 11.94/4.70  tff(c_15344, plain, (![A_667, B_668, C_669]: (k2_relset_1(A_667, B_668, C_669)=k2_relat_1(C_669) | ~m1_subset_1(C_669, k1_zfmisc_1(k2_zfmisc_1(A_667, B_668))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 11.94/4.70  tff(c_15347, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_15344])).
% 11.94/4.70  tff(c_15349, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_15293, c_15347])).
% 11.94/4.70  tff(c_15425, plain, (![A_680, C_681]: (r2_hidden(k4_tarski('#skF_5'(A_680, k2_relat_1(A_680), C_681), C_681), A_680) | ~r2_hidden(C_681, k2_relat_1(A_680)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.94/4.70  tff(c_36, plain, (![E_47]: (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7' | ~r2_hidden(k4_tarski(E_47, '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.94/4.70  tff(c_15294, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_36])).
% 11.94/4.70  tff(c_15300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15293, c_15294])).
% 11.94/4.70  tff(c_15301, plain, (![E_47]: (~r2_hidden(k4_tarski(E_47, '#skF_10'), '#skF_8'))), inference(splitRight, [status(thm)], [c_36])).
% 11.94/4.70  tff(c_15434, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_15425, c_15301])).
% 11.94/4.70  tff(c_15443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15292, c_15349, c_15434])).
% 11.94/4.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.94/4.70  
% 11.94/4.70  Inference rules
% 11.94/4.70  ----------------------
% 11.94/4.70  #Ref     : 0
% 11.94/4.70  #Sup     : 3765
% 11.94/4.70  #Fact    : 0
% 11.94/4.70  #Define  : 0
% 11.94/4.70  #Split   : 43
% 11.94/4.70  #Chain   : 0
% 11.94/4.70  #Close   : 0
% 11.94/4.70  
% 11.94/4.70  Ordering : KBO
% 11.94/4.70  
% 11.94/4.70  Simplification rules
% 11.94/4.70  ----------------------
% 11.94/4.70  #Subsume      : 1551
% 11.94/4.70  #Demod        : 691
% 11.94/4.70  #Tautology    : 157
% 11.94/4.70  #SimpNegUnit  : 13
% 11.94/4.70  #BackRed      : 15
% 11.94/4.70  
% 11.94/4.70  #Partial instantiations: 0
% 11.94/4.70  #Strategies tried      : 1
% 11.94/4.70  
% 11.94/4.70  Timing (in seconds)
% 11.94/4.70  ----------------------
% 11.94/4.70  Preprocessing        : 0.29
% 11.94/4.70  Parsing              : 0.15
% 11.94/4.70  CNF conversion       : 0.02
% 11.94/4.70  Main loop            : 3.59
% 11.94/4.70  Inferencing          : 0.64
% 11.94/4.70  Reduction            : 0.65
% 11.94/4.70  Demodulation         : 0.40
% 11.94/4.70  BG Simplification    : 0.07
% 11.94/4.70  Subsumption          : 2.03
% 11.94/4.70  Abstraction          : 0.11
% 11.94/4.70  MUC search           : 0.00
% 11.94/4.70  Cooper               : 0.00
% 11.94/4.70  Total                : 3.93
% 11.94/4.70  Index Insertion      : 0.00
% 11.94/4.70  Index Deletion       : 0.00
% 11.94/4.70  Index Matching       : 0.00
% 11.94/4.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
