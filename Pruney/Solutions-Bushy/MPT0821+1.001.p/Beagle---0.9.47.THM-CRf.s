%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0821+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:53 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 930 expanded)
%              Number of leaves         :   27 ( 308 expanded)
%              Depth                    :   16
%              Number of atoms          :  254 (2052 expanded)
%              Number of equality atoms :   51 ( 448 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_9 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
        <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_24,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_67,plain,(
    ! [A_61,B_62,C_63] :
      ( k1_relset_1(A_61,B_62,C_63) = k1_relat_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_71,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_67])).

tff(c_30,plain,
    ( k1_relset_1('#skF_6','#skF_5','#skF_7') != '#skF_6'
    | r2_hidden('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_72,plain,(
    k1_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_38])).

tff(c_1307,plain,(
    ! [A_189,B_190] :
      ( r2_hidden(k4_tarski('#skF_1'(A_189,B_190),'#skF_2'(A_189,B_190)),A_189)
      | r2_hidden('#skF_3'(A_189,B_190),B_190)
      | k1_relat_1(A_189) = B_190 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_26,B_27] :
      ( r2_hidden(A_26,B_27)
      | v1_xboole_0(B_27)
      | ~ m1_subset_1(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_78,plain,(
    ! [A_64,B_65,C_66] :
      ( m1_subset_1(k1_relset_1(A_64,B_65,C_66),k1_zfmisc_1(A_64))
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_89,plain,
    ( m1_subset_1(k1_relat_1('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_78])).

tff(c_94,plain,(
    m1_subset_1(k1_relat_1('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_89])).

tff(c_22,plain,(
    ! [C_33,B_32,A_31] :
      ( ~ v1_xboole_0(C_33)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(C_33))
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_151,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden(A_31,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_94,c_22])).

tff(c_152,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_452,plain,(
    ! [A_113,B_114] :
      ( r2_hidden(k4_tarski('#skF_1'(A_113,B_114),'#skF_2'(A_113,B_114)),A_113)
      | r2_hidden('#skF_3'(A_113,B_114),B_114)
      | k1_relat_1(A_113) = B_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k1_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(C_16,D_19),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_495,plain,(
    ! [A_115,B_116] :
      ( r2_hidden('#skF_1'(A_115,B_116),k1_relat_1(A_115))
      | r2_hidden('#skF_3'(A_115,B_116),B_116)
      | k1_relat_1(A_115) = B_116 ) ),
    inference(resolution,[status(thm)],[c_452,c_4])).

tff(c_20,plain,(
    ! [A_28,C_30,B_29] :
      ( m1_subset_1(A_28,C_30)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(C_30))
      | ~ r2_hidden(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_150,plain,(
    ! [A_28] :
      ( m1_subset_1(A_28,'#skF_6')
      | ~ r2_hidden(A_28,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_94,c_20])).

tff(c_513,plain,(
    ! [B_117] :
      ( m1_subset_1('#skF_1'('#skF_7',B_117),'#skF_6')
      | r2_hidden('#skF_3'('#skF_7',B_117),B_117)
      | k1_relat_1('#skF_7') = B_117 ) ),
    inference(resolution,[status(thm)],[c_495,c_150])).

tff(c_32,plain,(
    ! [D_40] :
      ( r2_hidden(k4_tarski(D_40,'#skF_8'(D_40)),'#skF_7')
      | ~ r2_hidden(D_40,'#skF_6')
      | r2_hidden('#skF_9','#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_77,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_36,plain,(
    ! [D_40] :
      ( r2_hidden(k4_tarski(D_40,'#skF_8'(D_40)),'#skF_7')
      | ~ r2_hidden(D_40,'#skF_6')
      | k1_relset_1('#skF_6','#skF_5','#skF_7') = '#skF_6' ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_129,plain,(
    ! [D_40] :
      ( r2_hidden(k4_tarski(D_40,'#skF_8'(D_40)),'#skF_7')
      | ~ r2_hidden(D_40,'#skF_6')
      | k1_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_36])).

tff(c_131,plain,(
    ! [D_71] :
      ( r2_hidden(k4_tarski(D_71,'#skF_8'(D_71)),'#skF_7')
      | ~ r2_hidden(D_71,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_129])).

tff(c_28,plain,(
    ! [D_40,E_43] :
      ( r2_hidden(k4_tarski(D_40,'#skF_8'(D_40)),'#skF_7')
      | ~ r2_hidden(D_40,'#skF_6')
      | ~ r2_hidden(k4_tarski('#skF_9',E_43),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_95,plain,(
    ! [E_43] : ~ r2_hidden(k4_tarski('#skF_9',E_43),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_135,plain,(
    ~ r2_hidden('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_131,c_95])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_135])).

tff(c_159,plain,(
    ! [D_73] :
      ( r2_hidden(k4_tarski(D_73,'#skF_8'(D_73)),'#skF_7')
      | ~ r2_hidden(D_73,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_181,plain,(
    ! [D_76] :
      ( r2_hidden(D_76,k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_76,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_159,c_4])).

tff(c_189,plain,(
    ! [D_76] :
      ( m1_subset_1(D_76,'#skF_6')
      | ~ r2_hidden(D_76,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_181,c_150])).

tff(c_520,plain,
    ( m1_subset_1('#skF_3'('#skF_7','#skF_6'),'#skF_6')
    | m1_subset_1('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_513,c_189])).

tff(c_528,plain,
    ( m1_subset_1('#skF_3'('#skF_7','#skF_6'),'#skF_6')
    | m1_subset_1('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_520])).

tff(c_531,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_528])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_3'(A_1,B_2),B_2)
      | k1_relat_1(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_145,plain,(
    ! [D_40] :
      ( r2_hidden(k4_tarski(D_40,'#skF_8'(D_40)),'#skF_7')
      | ~ r2_hidden(D_40,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_286,plain,(
    ! [A_95,B_96,D_97] :
      ( ~ r2_hidden('#skF_1'(A_95,B_96),B_96)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_95,B_96),D_97),A_95)
      | k1_relat_1(A_95) = B_96 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_756,plain,(
    ! [A_137,B_138,D_139] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_137,B_138),D_139),A_137)
      | k1_relat_1(A_137) = B_138
      | v1_xboole_0(B_138)
      | ~ m1_subset_1('#skF_1'(A_137,B_138),B_138) ) ),
    inference(resolution,[status(thm)],[c_18,c_286])).

tff(c_805,plain,(
    ! [B_140] :
      ( k1_relat_1('#skF_7') = B_140
      | v1_xboole_0(B_140)
      | ~ m1_subset_1('#skF_1'('#skF_7',B_140),B_140)
      | ~ r2_hidden('#skF_3'('#skF_7',B_140),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_145,c_756])).

tff(c_807,plain,
    ( k1_relat_1('#skF_7') = '#skF_6'
    | v1_xboole_0('#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_531,c_805])).

tff(c_813,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_72,c_807])).

tff(c_823,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10,c_813])).

tff(c_832,plain,(
    ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_823])).

tff(c_838,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_832])).

tff(c_841,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_838])).

tff(c_843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_841])).

tff(c_845,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_528])).

tff(c_510,plain,(
    ! [B_116] :
      ( m1_subset_1('#skF_1'('#skF_7',B_116),'#skF_6')
      | r2_hidden('#skF_3'('#skF_7',B_116),B_116)
      | k1_relat_1('#skF_7') = B_116 ) ),
    inference(resolution,[status(thm)],[c_495,c_150])).

tff(c_866,plain,(
    ! [A_143,B_144,D_145] :
      ( r2_hidden(k4_tarski('#skF_1'(A_143,B_144),'#skF_2'(A_143,B_144)),A_143)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_143,B_144),D_145),A_143)
      | k1_relat_1(A_143) = B_144 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1000,plain,(
    ! [B_155] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_7',B_155),'#skF_2'('#skF_7',B_155)),'#skF_7')
      | k1_relat_1('#skF_7') = B_155
      | ~ r2_hidden('#skF_3'('#skF_7',B_155),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_145,c_866])).

tff(c_1008,plain,(
    ! [B_156] :
      ( r2_hidden('#skF_1'('#skF_7',B_156),k1_relat_1('#skF_7'))
      | k1_relat_1('#skF_7') = B_156
      | ~ r2_hidden('#skF_3'('#skF_7',B_156),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1000,c_4])).

tff(c_1018,plain,(
    ! [B_157] :
      ( m1_subset_1('#skF_1'('#skF_7',B_157),'#skF_6')
      | k1_relat_1('#skF_7') = B_157
      | ~ r2_hidden('#skF_3'('#skF_7',B_157),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1008,c_150])).

tff(c_1022,plain,
    ( m1_subset_1('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_510,c_1018])).

tff(c_1035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_845,c_72,c_845,c_1022])).

tff(c_1036,plain,(
    ! [A_31] : ~ r2_hidden(A_31,k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_1044,plain,(
    ! [D_159] :
      ( r2_hidden(k4_tarski(D_159,'#skF_8'(D_159)),'#skF_7')
      | ~ r2_hidden(D_159,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1049,plain,(
    ! [D_159] :
      ( r2_hidden(D_159,k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_159,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1044,c_4])).

tff(c_1053,plain,(
    ! [D_159] : ~ r2_hidden(D_159,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1036,c_1049])).

tff(c_1055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1053,c_77])).

tff(c_1071,plain,(
    ! [D_162] :
      ( r2_hidden(k4_tarski(D_162,'#skF_8'(D_162)),'#skF_7')
      | ~ r2_hidden(D_162,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1084,plain,(
    ! [D_163] :
      ( r2_hidden(D_163,k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_163,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1071,c_4])).

tff(c_1096,plain,(
    ! [C_165,D_166] :
      ( r2_hidden(C_165,k1_relat_1(k1_relat_1('#skF_7')))
      | ~ r2_hidden(k4_tarski(C_165,D_166),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1084,c_4])).

tff(c_1100,plain,(
    ! [C_165,D_166] :
      ( r2_hidden(C_165,k1_relat_1(k1_relat_1('#skF_7')))
      | v1_xboole_0('#skF_6')
      | ~ m1_subset_1(k4_tarski(C_165,D_166),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_18,c_1096])).

tff(c_1103,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1100])).

tff(c_1133,plain,(
    ! [A_173,B_174,C_175] :
      ( m1_subset_1(k1_relset_1(A_173,B_174,C_175),k1_zfmisc_1(A_173))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_173,B_174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1144,plain,
    ( m1_subset_1(k1_relat_1('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1133])).

tff(c_1149,plain,(
    m1_subset_1(k1_relat_1('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1144])).

tff(c_1161,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden(A_31,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1149,c_22])).

tff(c_1165,plain,(
    ! [A_31] : ~ r2_hidden(A_31,k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1103,c_1161])).

tff(c_1083,plain,(
    ! [D_162] :
      ( r2_hidden(D_162,k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_162,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1071,c_4])).

tff(c_1166,plain,(
    ! [D_162] : ~ r2_hidden(D_162,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1165,c_1083])).

tff(c_1377,plain,(
    ! [B_192] :
      ( r2_hidden('#skF_3'('#skF_6',B_192),B_192)
      | k1_relat_1('#skF_6') = B_192 ) ),
    inference(resolution,[status(thm)],[c_1307,c_1166])).

tff(c_1422,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1377,c_1166])).

tff(c_1423,plain,(
    k1_relat_1('#skF_7') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1377,c_1165])).

tff(c_1440,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1422,c_1423])).

tff(c_1441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1440])).

tff(c_1443,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1100])).

tff(c_1756,plain,(
    ! [A_235,B_236] :
      ( r2_hidden(k4_tarski('#skF_1'(A_235,B_236),'#skF_2'(A_235,B_236)),A_235)
      | r2_hidden('#skF_3'(A_235,B_236),B_236)
      | k1_relat_1(A_235) = B_236 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1818,plain,(
    ! [A_238,B_239] :
      ( r2_hidden('#skF_1'(A_238,B_239),k1_relat_1(A_238))
      | r2_hidden('#skF_3'(A_238,B_239),B_239)
      | k1_relat_1(A_238) = B_239 ) ),
    inference(resolution,[status(thm)],[c_1756,c_4])).

tff(c_1512,plain,(
    ! [A_209,B_210,C_211] :
      ( m1_subset_1(k1_relset_1(A_209,B_210,C_211),k1_zfmisc_1(A_209))
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1523,plain,
    ( m1_subset_1(k1_relat_1('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_1512])).

tff(c_1528,plain,(
    m1_subset_1(k1_relat_1('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1523])).

tff(c_1533,plain,(
    ! [A_28] :
      ( m1_subset_1(A_28,'#skF_6')
      | ~ r2_hidden(A_28,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1528,c_20])).

tff(c_1836,plain,(
    ! [B_240] :
      ( m1_subset_1('#skF_1'('#skF_7',B_240),'#skF_6')
      | r2_hidden('#skF_3'('#skF_7',B_240),B_240)
      | k1_relat_1('#skF_7') = B_240 ) ),
    inference(resolution,[status(thm)],[c_1818,c_1533])).

tff(c_1535,plain,(
    ! [A_212] :
      ( m1_subset_1(A_212,'#skF_6')
      | ~ r2_hidden(A_212,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_1528,c_20])).

tff(c_1553,plain,(
    ! [D_162] :
      ( m1_subset_1(D_162,'#skF_6')
      | ~ r2_hidden(D_162,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1083,c_1535])).

tff(c_1843,plain,
    ( m1_subset_1('#skF_3'('#skF_7','#skF_6'),'#skF_6')
    | m1_subset_1('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1836,c_1553])).

tff(c_1851,plain,
    ( m1_subset_1('#skF_3'('#skF_7','#skF_6'),'#skF_6')
    | m1_subset_1('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1843])).

tff(c_1854,plain,(
    m1_subset_1('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1851])).

tff(c_1056,plain,(
    ! [D_40] :
      ( r2_hidden(k4_tarski(D_40,'#skF_8'(D_40)),'#skF_7')
      | ~ r2_hidden(D_40,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1595,plain,(
    ! [A_217,B_218,D_219] :
      ( ~ r2_hidden('#skF_1'(A_217,B_218),B_218)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_217,B_218),D_219),A_217)
      | k1_relat_1(A_217) = B_218 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2152,plain,(
    ! [A_265,B_266,D_267] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_265,B_266),D_267),A_265)
      | k1_relat_1(A_265) = B_266
      | v1_xboole_0(B_266)
      | ~ m1_subset_1('#skF_1'(A_265,B_266),B_266) ) ),
    inference(resolution,[status(thm)],[c_18,c_1595])).

tff(c_2205,plain,(
    ! [B_268] :
      ( k1_relat_1('#skF_7') = B_268
      | v1_xboole_0(B_268)
      | ~ m1_subset_1('#skF_1'('#skF_7',B_268),B_268)
      | ~ r2_hidden('#skF_3'('#skF_7',B_268),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1056,c_2152])).

tff(c_2207,plain,
    ( k1_relat_1('#skF_7') = '#skF_6'
    | v1_xboole_0('#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1854,c_2205])).

tff(c_2213,plain,(
    ~ r2_hidden('#skF_3'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1443,c_72,c_2207])).

tff(c_2224,plain,
    ( ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10,c_2213])).

tff(c_2233,plain,(
    ~ r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2224])).

tff(c_2239,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_2233])).

tff(c_2242,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1854,c_2239])).

tff(c_2244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1443,c_2242])).

tff(c_2246,plain,(
    ~ m1_subset_1('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1851])).

tff(c_1833,plain,(
    ! [B_239] :
      ( m1_subset_1('#skF_1'('#skF_7',B_239),'#skF_6')
      | r2_hidden('#skF_3'('#skF_7',B_239),B_239)
      | k1_relat_1('#skF_7') = B_239 ) ),
    inference(resolution,[status(thm)],[c_1818,c_1533])).

tff(c_2283,plain,(
    ! [A_273,B_274,D_275] :
      ( r2_hidden(k4_tarski('#skF_1'(A_273,B_274),'#skF_2'(A_273,B_274)),A_273)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_273,B_274),D_275),A_273)
      | k1_relat_1(A_273) = B_274 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2393,plain,(
    ! [B_281] :
      ( r2_hidden(k4_tarski('#skF_1'('#skF_7',B_281),'#skF_2'('#skF_7',B_281)),'#skF_7')
      | k1_relat_1('#skF_7') = B_281
      | ~ r2_hidden('#skF_3'('#skF_7',B_281),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1056,c_2283])).

tff(c_2401,plain,(
    ! [B_282] :
      ( r2_hidden('#skF_1'('#skF_7',B_282),k1_relat_1('#skF_7'))
      | k1_relat_1('#skF_7') = B_282
      | ~ r2_hidden('#skF_3'('#skF_7',B_282),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2393,c_4])).

tff(c_2411,plain,(
    ! [B_283] :
      ( m1_subset_1('#skF_1'('#skF_7',B_283),'#skF_6')
      | k1_relat_1('#skF_7') = B_283
      | ~ r2_hidden('#skF_3'('#skF_7',B_283),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2401,c_1533])).

tff(c_2415,plain,
    ( m1_subset_1('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1833,c_2411])).

tff(c_2428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2246,c_72,c_2246,c_2415])).

tff(c_2429,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_2430,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_2467,plain,(
    ! [A_299,B_300,C_301] :
      ( k1_relset_1(A_299,B_300,C_301) = k1_relat_1(C_301)
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_299,B_300))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2470,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_2467])).

tff(c_2472,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2430,c_2470])).

tff(c_2484,plain,(
    ! [C_304,A_305] :
      ( r2_hidden(k4_tarski(C_304,'#skF_4'(A_305,k1_relat_1(A_305),C_304)),A_305)
      | ~ r2_hidden(C_304,k1_relat_1(A_305)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [E_43] :
      ( k1_relset_1('#skF_6','#skF_5','#skF_7') != '#skF_6'
      | ~ r2_hidden(k4_tarski('#skF_9',E_43),'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2447,plain,(
    ! [E_43] : ~ r2_hidden(k4_tarski('#skF_9',E_43),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2430,c_26])).

tff(c_2491,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_2484,c_2447])).

tff(c_2503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_2472,c_2491])).

%------------------------------------------------------------------------------
