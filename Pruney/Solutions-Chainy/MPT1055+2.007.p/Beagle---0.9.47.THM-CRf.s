%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:19 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 156 expanded)
%              Number of leaves         :   39 (  70 expanded)
%              Depth                    :    8
%              Number of atoms          :  156 ( 425 expanded)
%              Number of equality atoms :   22 (  39 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(A))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(B))
                       => ( r1_tarski(k7_relset_1(A,B,C,D),E)
                        <=> r1_tarski(D,k8_relset_1(A,B,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_597,plain,(
    ! [A_140,B_141] :
      ( r2_hidden(A_140,B_141)
      | v1_xboole_0(B_141)
      | ~ m1_subset_1(A_140,B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [C_8,A_4] :
      ( r1_tarski(C_8,A_4)
      | ~ r2_hidden(C_8,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_601,plain,(
    ! [A_140,A_4] :
      ( r1_tarski(A_140,A_4)
      | v1_xboole_0(k1_zfmisc_1(A_4))
      | ~ m1_subset_1(A_140,k1_zfmisc_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_597,c_6])).

tff(c_607,plain,(
    ! [A_142,A_143] :
      ( r1_tarski(A_142,A_143)
      | ~ m1_subset_1(A_142,k1_zfmisc_1(A_143)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_601])).

tff(c_619,plain,(
    r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_607])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_620,plain,(
    ! [C_144,A_145,B_146] :
      ( v1_relat_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_624,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_620])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_46,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_807,plain,(
    ! [A_180,B_181,C_182,D_183] :
      ( k8_relset_1(A_180,B_181,C_182,D_183) = k10_relat_1(C_182,D_183)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_810,plain,(
    ! [D_183] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_183) = k10_relat_1('#skF_5',D_183) ),
    inference(resolution,[status(thm)],[c_44,c_807])).

tff(c_1190,plain,(
    ! [B_221,A_222,C_223] :
      ( k1_xboole_0 = B_221
      | k8_relset_1(A_222,B_221,C_223,B_221) = A_222
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_222,B_221)))
      | ~ v1_funct_2(C_223,A_222,B_221)
      | ~ v1_funct_1(C_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1192,plain,
    ( k1_xboole_0 = '#skF_4'
    | k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_1190])).

tff(c_1195,plain,
    ( k1_xboole_0 = '#skF_4'
    | k10_relat_1('#skF_5','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_810,c_1192])).

tff(c_1196,plain,(
    k10_relat_1('#skF_5','#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1195])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k10_relat_1(B_16,A_15),k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_626,plain,(
    ! [A_149,C_150,B_151] :
      ( r1_tarski(A_149,C_150)
      | ~ r1_tarski(B_151,C_150)
      | ~ r1_tarski(A_149,B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_637,plain,(
    ! [A_149,B_16,A_15] :
      ( r1_tarski(A_149,k1_relat_1(B_16))
      | ~ r1_tarski(A_149,k10_relat_1(B_16,A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_24,c_626])).

tff(c_1207,plain,(
    ! [A_149] :
      ( r1_tarski(A_149,k1_relat_1('#skF_5'))
      | ~ r1_tarski(A_149,'#skF_3')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1196,c_637])).

tff(c_1262,plain,(
    ! [A_226] :
      ( r1_tarski(A_226,k1_relat_1('#skF_5'))
      | ~ r1_tarski(A_226,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_1207])).

tff(c_70,plain,(
    ! [C_69,A_70,B_71] :
      ( v1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_74,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_70])).

tff(c_291,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( k8_relset_1(A_107,B_108,C_109,D_110) = k10_relat_1(C_109,D_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_294,plain,(
    ! [D_110] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_110) = k10_relat_1('#skF_5',D_110) ),
    inference(resolution,[status(thm)],[c_44,c_291])).

tff(c_54,plain,
    ( ~ r1_tarski('#skF_6',k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_7'))
    | ~ r1_tarski(k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_62,plain,(
    ~ r1_tarski(k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_60,plain,
    ( r1_tarski(k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7')
    | r1_tarski('#skF_6',k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_96,plain,(
    r1_tarski('#skF_6',k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_60])).

tff(c_298,plain,(
    r1_tarski('#skF_6',k10_relat_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_96])).

tff(c_22,plain,(
    ! [C_14,A_12,B_13] :
      ( r1_tarski(k9_relat_1(C_14,A_12),k9_relat_1(C_14,B_13))
      | ~ r1_tarski(A_12,B_13)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_115,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(k9_relat_1(B_81,k10_relat_1(B_81,A_82)),A_82)
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_534,plain,(
    ! [A_130,A_131,B_132] :
      ( r1_tarski(A_130,A_131)
      | ~ r1_tarski(A_130,k9_relat_1(B_132,k10_relat_1(B_132,A_131)))
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(resolution,[status(thm)],[c_115,c_4])).

tff(c_550,plain,(
    ! [C_133,A_134,A_135] :
      ( r1_tarski(k9_relat_1(C_133,A_134),A_135)
      | ~ v1_funct_1(C_133)
      | ~ r1_tarski(A_134,k10_relat_1(C_133,A_135))
      | ~ v1_relat_1(C_133) ) ),
    inference(resolution,[status(thm)],[c_22,c_534])).

tff(c_326,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k7_relset_1(A_112,B_113,C_114,D_115) = k9_relat_1(C_114,D_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_329,plain,(
    ! [D_115] : k7_relset_1('#skF_3','#skF_4','#skF_5',D_115) = k9_relat_1('#skF_5',D_115) ),
    inference(resolution,[status(thm)],[c_44,c_326])).

tff(c_342,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_62])).

tff(c_564,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ r1_tarski('#skF_6',k10_relat_1('#skF_5','#skF_7'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_550,c_342])).

tff(c_588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_298,c_48,c_564])).

tff(c_589,plain,(
    ~ r1_tarski('#skF_6',k8_relset_1('#skF_3','#skF_4','#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_811,plain,(
    ~ r1_tarski('#skF_6',k10_relat_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_589])).

tff(c_821,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( k7_relset_1(A_185,B_186,C_187,D_188) = k9_relat_1(C_187,D_188)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_824,plain,(
    ! [D_188] : k7_relset_1('#skF_3','#skF_4','#skF_5',D_188) = k9_relat_1('#skF_5',D_188) ),
    inference(resolution,[status(thm)],[c_44,c_821])).

tff(c_590,plain,(
    r1_tarski(k7_relset_1('#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_829,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_824,c_590])).

tff(c_978,plain,(
    ! [A_206,C_207,B_208] :
      ( r1_tarski(A_206,k10_relat_1(C_207,B_208))
      | ~ r1_tarski(k9_relat_1(C_207,A_206),B_208)
      | ~ r1_tarski(A_206,k1_relat_1(C_207))
      | ~ v1_funct_1(C_207)
      | ~ v1_relat_1(C_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_996,plain,
    ( r1_tarski('#skF_6',k10_relat_1('#skF_5','#skF_7'))
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_829,c_978])).

tff(c_1026,plain,
    ( r1_tarski('#skF_6',k10_relat_1('#skF_5','#skF_7'))
    | ~ r1_tarski('#skF_6',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_48,c_996])).

tff(c_1027,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_811,c_1026])).

tff(c_1265,plain,(
    ~ r1_tarski('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_1262,c_1027])).

tff(c_1281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_619,c_1265])).

tff(c_1282,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1195])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1286,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1282,c_2])).

tff(c_1288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:40:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.57  
% 3.61/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.57  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.61/1.57  
% 3.61/1.57  %Foreground sorts:
% 3.61/1.57  
% 3.61/1.57  
% 3.61/1.57  %Background operators:
% 3.61/1.57  
% 3.61/1.57  
% 3.61/1.57  %Foreground operators:
% 3.61/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.61/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.61/1.57  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.61/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.61/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.61/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.57  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.61/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.61/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.61/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.61/1.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.61/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.61/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.61/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.61/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.61/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.61/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.61/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.61/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.61/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.61/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.61/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.57  
% 3.61/1.59  tff(f_123, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_2)).
% 3.61/1.59  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.61/1.59  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.61/1.59  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.61/1.59  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.61/1.59  tff(f_86, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.61/1.59  tff(f_98, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 3.61/1.59  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 3.61/1.59  tff(f_32, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.61/1.59  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_relat_1)).
% 3.61/1.59  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 3.61/1.59  tff(f_82, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.61/1.59  tff(f_74, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 3.61/1.59  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.61/1.59  tff(c_50, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.61/1.59  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.61/1.59  tff(c_18, plain, (![A_9]: (~v1_xboole_0(k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.61/1.59  tff(c_597, plain, (![A_140, B_141]: (r2_hidden(A_140, B_141) | v1_xboole_0(B_141) | ~m1_subset_1(A_140, B_141))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.61/1.59  tff(c_6, plain, (![C_8, A_4]: (r1_tarski(C_8, A_4) | ~r2_hidden(C_8, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.61/1.59  tff(c_601, plain, (![A_140, A_4]: (r1_tarski(A_140, A_4) | v1_xboole_0(k1_zfmisc_1(A_4)) | ~m1_subset_1(A_140, k1_zfmisc_1(A_4)))), inference(resolution, [status(thm)], [c_597, c_6])).
% 3.61/1.59  tff(c_607, plain, (![A_142, A_143]: (r1_tarski(A_142, A_143) | ~m1_subset_1(A_142, k1_zfmisc_1(A_143)))), inference(negUnitSimplification, [status(thm)], [c_18, c_601])).
% 3.61/1.59  tff(c_619, plain, (r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_607])).
% 3.61/1.59  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.61/1.59  tff(c_620, plain, (![C_144, A_145, B_146]: (v1_relat_1(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.61/1.59  tff(c_624, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_620])).
% 3.61/1.59  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.61/1.59  tff(c_46, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.61/1.59  tff(c_807, plain, (![A_180, B_181, C_182, D_183]: (k8_relset_1(A_180, B_181, C_182, D_183)=k10_relat_1(C_182, D_183) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.61/1.59  tff(c_810, plain, (![D_183]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_183)=k10_relat_1('#skF_5', D_183))), inference(resolution, [status(thm)], [c_44, c_807])).
% 3.61/1.59  tff(c_1190, plain, (![B_221, A_222, C_223]: (k1_xboole_0=B_221 | k8_relset_1(A_222, B_221, C_223, B_221)=A_222 | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_222, B_221))) | ~v1_funct_2(C_223, A_222, B_221) | ~v1_funct_1(C_223))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.61/1.59  tff(c_1192, plain, (k1_xboole_0='#skF_4' | k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_1190])).
% 3.61/1.59  tff(c_1195, plain, (k1_xboole_0='#skF_4' | k10_relat_1('#skF_5', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_810, c_1192])).
% 3.61/1.59  tff(c_1196, plain, (k10_relat_1('#skF_5', '#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_1195])).
% 3.61/1.59  tff(c_24, plain, (![B_16, A_15]: (r1_tarski(k10_relat_1(B_16, A_15), k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.61/1.59  tff(c_626, plain, (![A_149, C_150, B_151]: (r1_tarski(A_149, C_150) | ~r1_tarski(B_151, C_150) | ~r1_tarski(A_149, B_151))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.61/1.59  tff(c_637, plain, (![A_149, B_16, A_15]: (r1_tarski(A_149, k1_relat_1(B_16)) | ~r1_tarski(A_149, k10_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_24, c_626])).
% 3.61/1.59  tff(c_1207, plain, (![A_149]: (r1_tarski(A_149, k1_relat_1('#skF_5')) | ~r1_tarski(A_149, '#skF_3') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1196, c_637])).
% 3.61/1.59  tff(c_1262, plain, (![A_226]: (r1_tarski(A_226, k1_relat_1('#skF_5')) | ~r1_tarski(A_226, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_1207])).
% 3.61/1.59  tff(c_70, plain, (![C_69, A_70, B_71]: (v1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.61/1.59  tff(c_74, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_70])).
% 3.61/1.59  tff(c_291, plain, (![A_107, B_108, C_109, D_110]: (k8_relset_1(A_107, B_108, C_109, D_110)=k10_relat_1(C_109, D_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.61/1.59  tff(c_294, plain, (![D_110]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_110)=k10_relat_1('#skF_5', D_110))), inference(resolution, [status(thm)], [c_44, c_291])).
% 3.61/1.59  tff(c_54, plain, (~r1_tarski('#skF_6', k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')) | ~r1_tarski(k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.61/1.59  tff(c_62, plain, (~r1_tarski(k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')), inference(splitLeft, [status(thm)], [c_54])).
% 3.61/1.59  tff(c_60, plain, (r1_tarski(k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7') | r1_tarski('#skF_6', k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.61/1.59  tff(c_96, plain, (r1_tarski('#skF_6', k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_62, c_60])).
% 3.61/1.59  tff(c_298, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_294, c_96])).
% 3.61/1.59  tff(c_22, plain, (![C_14, A_12, B_13]: (r1_tarski(k9_relat_1(C_14, A_12), k9_relat_1(C_14, B_13)) | ~r1_tarski(A_12, B_13) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.61/1.59  tff(c_115, plain, (![B_81, A_82]: (r1_tarski(k9_relat_1(B_81, k10_relat_1(B_81, A_82)), A_82) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.61/1.59  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.61/1.59  tff(c_534, plain, (![A_130, A_131, B_132]: (r1_tarski(A_130, A_131) | ~r1_tarski(A_130, k9_relat_1(B_132, k10_relat_1(B_132, A_131))) | ~v1_funct_1(B_132) | ~v1_relat_1(B_132))), inference(resolution, [status(thm)], [c_115, c_4])).
% 3.61/1.59  tff(c_550, plain, (![C_133, A_134, A_135]: (r1_tarski(k9_relat_1(C_133, A_134), A_135) | ~v1_funct_1(C_133) | ~r1_tarski(A_134, k10_relat_1(C_133, A_135)) | ~v1_relat_1(C_133))), inference(resolution, [status(thm)], [c_22, c_534])).
% 3.61/1.59  tff(c_326, plain, (![A_112, B_113, C_114, D_115]: (k7_relset_1(A_112, B_113, C_114, D_115)=k9_relat_1(C_114, D_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.61/1.59  tff(c_329, plain, (![D_115]: (k7_relset_1('#skF_3', '#skF_4', '#skF_5', D_115)=k9_relat_1('#skF_5', D_115))), inference(resolution, [status(thm)], [c_44, c_326])).
% 3.61/1.59  tff(c_342, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_329, c_62])).
% 3.61/1.59  tff(c_564, plain, (~v1_funct_1('#skF_5') | ~r1_tarski('#skF_6', k10_relat_1('#skF_5', '#skF_7')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_550, c_342])).
% 3.61/1.59  tff(c_588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_298, c_48, c_564])).
% 3.61/1.59  tff(c_589, plain, (~r1_tarski('#skF_6', k8_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_54])).
% 3.61/1.59  tff(c_811, plain, (~r1_tarski('#skF_6', k10_relat_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_810, c_589])).
% 3.61/1.59  tff(c_821, plain, (![A_185, B_186, C_187, D_188]: (k7_relset_1(A_185, B_186, C_187, D_188)=k9_relat_1(C_187, D_188) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.61/1.59  tff(c_824, plain, (![D_188]: (k7_relset_1('#skF_3', '#skF_4', '#skF_5', D_188)=k9_relat_1('#skF_5', D_188))), inference(resolution, [status(thm)], [c_44, c_821])).
% 3.61/1.59  tff(c_590, plain, (r1_tarski(k7_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 3.61/1.59  tff(c_829, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_824, c_590])).
% 3.61/1.59  tff(c_978, plain, (![A_206, C_207, B_208]: (r1_tarski(A_206, k10_relat_1(C_207, B_208)) | ~r1_tarski(k9_relat_1(C_207, A_206), B_208) | ~r1_tarski(A_206, k1_relat_1(C_207)) | ~v1_funct_1(C_207) | ~v1_relat_1(C_207))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.61/1.59  tff(c_996, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_5', '#skF_7')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_829, c_978])).
% 3.61/1.59  tff(c_1026, plain, (r1_tarski('#skF_6', k10_relat_1('#skF_5', '#skF_7')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_48, c_996])).
% 3.61/1.59  tff(c_1027, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_811, c_1026])).
% 3.61/1.59  tff(c_1265, plain, (~r1_tarski('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_1262, c_1027])).
% 3.61/1.59  tff(c_1281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_619, c_1265])).
% 3.61/1.59  tff(c_1282, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1195])).
% 3.61/1.59  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.61/1.59  tff(c_1286, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1282, c_2])).
% 3.61/1.59  tff(c_1288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1286])).
% 3.61/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.59  
% 3.61/1.59  Inference rules
% 3.61/1.59  ----------------------
% 3.61/1.59  #Ref     : 0
% 3.61/1.59  #Sup     : 285
% 3.61/1.59  #Fact    : 0
% 3.61/1.59  #Define  : 0
% 3.61/1.59  #Split   : 11
% 3.61/1.59  #Chain   : 0
% 3.61/1.59  #Close   : 0
% 3.61/1.59  
% 3.61/1.59  Ordering : KBO
% 3.61/1.59  
% 3.61/1.59  Simplification rules
% 3.61/1.59  ----------------------
% 3.61/1.59  #Subsume      : 57
% 3.61/1.59  #Demod        : 67
% 3.61/1.59  #Tautology    : 32
% 3.61/1.59  #SimpNegUnit  : 6
% 3.61/1.59  #BackRed      : 15
% 3.61/1.59  
% 3.61/1.59  #Partial instantiations: 0
% 3.61/1.59  #Strategies tried      : 1
% 3.61/1.59  
% 3.61/1.59  Timing (in seconds)
% 3.61/1.59  ----------------------
% 3.61/1.59  Preprocessing        : 0.33
% 3.61/1.59  Parsing              : 0.17
% 3.61/1.59  CNF conversion       : 0.03
% 3.61/1.59  Main loop            : 0.48
% 3.61/1.59  Inferencing          : 0.17
% 3.61/1.59  Reduction            : 0.14
% 3.61/1.59  Demodulation         : 0.09
% 3.61/1.59  BG Simplification    : 0.02
% 3.61/1.59  Subsumption          : 0.11
% 3.61/1.59  Abstraction          : 0.02
% 3.61/1.59  MUC search           : 0.00
% 3.61/1.59  Cooper               : 0.00
% 3.61/1.59  Total                : 0.85
% 3.61/1.59  Index Insertion      : 0.00
% 3.61/1.59  Index Deletion       : 0.00
% 3.61/1.59  Index Matching       : 0.00
% 3.61/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
