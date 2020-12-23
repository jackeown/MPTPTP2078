%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:19 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 321 expanded)
%              Number of leaves         :   40 ( 121 expanded)
%              Depth                    :    9
%              Number of atoms          :  157 ( 680 expanded)
%              Number of equality atoms :   53 ( 162 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(c_20,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_79,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_85,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_79])).

tff(c_89,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_85])).

tff(c_24,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_97,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_89,c_24])).

tff(c_105,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_115,plain,(
    ! [C_67,B_68,A_69] :
      ( v5_relat_1(C_67,B_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_124,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_115])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v5_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_336,plain,(
    ! [A_124,B_125,C_126] :
      ( k2_relset_1(A_124,B_125,C_126) = k2_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_350,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_336])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_180,plain,(
    ! [A_89,C_90,B_91] :
      ( m1_subset_1(A_89,C_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(C_90))
      | ~ r2_hidden(A_89,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_188,plain,(
    ! [A_93,B_94,A_95] :
      ( m1_subset_1(A_93,B_94)
      | ~ r2_hidden(A_93,A_95)
      | ~ r1_tarski(A_95,B_94) ) ),
    inference(resolution,[status(thm)],[c_10,c_180])).

tff(c_192,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1('#skF_2'(A_96),B_97)
      | ~ r1_tarski(A_96,B_97)
      | k1_xboole_0 = A_96 ) ),
    inference(resolution,[status(thm)],[c_6,c_188])).

tff(c_64,plain,(
    ! [D_55] :
      ( ~ r2_hidden(D_55,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_55,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_69,plain,
    ( ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_64])).

tff(c_106,plain,(
    ~ m1_subset_1('#skF_2'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_218,plain,
    ( ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_192,c_106])).

tff(c_221,plain,(
    ~ r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_351,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_221])).

tff(c_360,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_351])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_124,c_360])).

tff(c_365,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_430,plain,(
    ! [A_138,B_139,C_140] :
      ( k2_relset_1(A_138,B_139,C_140) = k2_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_441,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_430])).

tff(c_445,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_441])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_445])).

tff(c_448,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_606,plain,(
    ! [A_185,B_186,C_187] :
      ( k2_relset_1(A_185,B_186,C_187) = k2_relat_1(C_187)
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_185,B_186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_617,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_606])).

tff(c_621,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_617])).

tff(c_623,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_621])).

tff(c_624,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_26,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_96,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_89,c_26])).

tff(c_98,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_626,plain,(
    k1_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_98])).

tff(c_629,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_6])).

tff(c_709,plain,(
    ! [C_201,A_202,B_203] :
      ( v4_relat_1(C_201,A_202)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_202,B_203))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_718,plain,(
    v4_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_709])).

tff(c_730,plain,(
    ! [B_207,A_208] :
      ( k7_relat_1(B_207,A_208) = B_207
      | ~ v4_relat_1(B_207,A_208)
      | ~ v1_relat_1(B_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_733,plain,
    ( k7_relat_1('#skF_5','#skF_3') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_718,c_730])).

tff(c_736,plain,(
    k7_relat_1('#skF_5','#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_733])).

tff(c_32,plain,(
    ! [B_26,A_25] :
      ( r1_xboole_0(k1_relat_1(B_26),A_25)
      | k7_relat_1(B_26,A_25) != k1_xboole_0
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_782,plain,(
    ! [B_26,A_25] :
      ( r1_xboole_0(k1_relat_1(B_26),A_25)
      | k7_relat_1(B_26,A_25) != '#skF_5'
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_32])).

tff(c_792,plain,(
    ! [B_225,A_226] :
      ( k3_xboole_0(k1_relat_1(B_225),A_226) = k1_relat_1(k7_relat_1(B_225,A_226))
      | ~ v1_relat_1(B_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1013,plain,(
    ! [B_263,A_264,C_265] :
      ( ~ r1_xboole_0(k1_relat_1(B_263),A_264)
      | ~ r2_hidden(C_265,k1_relat_1(k7_relat_1(B_263,A_264)))
      | ~ v1_relat_1(B_263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_792,c_4])).

tff(c_1016,plain,(
    ! [C_265] :
      ( ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_3')
      | ~ r2_hidden(C_265,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_736,c_1013])).

tff(c_1022,plain,(
    ! [C_265] :
      ( ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_3')
      | ~ r2_hidden(C_265,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1016])).

tff(c_1024,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_5'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1022])).

tff(c_1027,plain,
    ( k7_relat_1('#skF_5','#skF_3') != '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_782,c_1024])).

tff(c_1031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_736,c_1027])).

tff(c_1034,plain,(
    ! [C_266] : ~ r2_hidden(C_266,k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1022])).

tff(c_1038,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_629,c_1034])).

tff(c_1042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_626,c_1038])).

tff(c_1043,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_44,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_1048,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1043,c_44])).

tff(c_1044,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_1053,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1043,c_1044])).

tff(c_1367,plain,(
    ! [A_324,B_325,C_326] :
      ( k1_relset_1(A_324,B_325,C_326) = k1_relat_1(C_326)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_324,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1378,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_1367])).

tff(c_1382,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_1378])).

tff(c_1384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1048,c_1382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.59  
% 3.21/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.59  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 3.21/1.59  
% 3.21/1.59  %Foreground sorts:
% 3.21/1.59  
% 3.21/1.59  
% 3.21/1.59  %Background operators:
% 3.21/1.59  
% 3.21/1.59  
% 3.21/1.59  %Foreground operators:
% 3.21/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.21/1.59  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.21/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.21/1.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.21/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.21/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.21/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.21/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.21/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.21/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.21/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.21/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.21/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.21/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.21/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.21/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.21/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.59  
% 3.21/1.61  tff(f_72, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.21/1.61  tff(f_131, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 3.21/1.61  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.21/1.61  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.21/1.61  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.21/1.61  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.21/1.61  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.21/1.61  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.21/1.61  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.21/1.61  tff(f_57, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.21/1.61  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.21/1.61  tff(f_96, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 3.21/1.61  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.21/1.61  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.21/1.61  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.21/1.61  tff(c_20, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.21/1.61  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.21/1.61  tff(c_79, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.21/1.61  tff(c_85, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_79])).
% 3.21/1.61  tff(c_89, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_85])).
% 3.21/1.61  tff(c_24, plain, (![A_22]: (k2_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.21/1.61  tff(c_97, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_89, c_24])).
% 3.21/1.61  tff(c_105, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_97])).
% 3.21/1.61  tff(c_115, plain, (![C_67, B_68, A_69]: (v5_relat_1(C_67, B_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.21/1.61  tff(c_124, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_115])).
% 3.21/1.61  tff(c_18, plain, (![B_17, A_16]: (r1_tarski(k2_relat_1(B_17), A_16) | ~v5_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.21/1.61  tff(c_336, plain, (![A_124, B_125, C_126]: (k2_relset_1(A_124, B_125, C_126)=k2_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.21/1.61  tff(c_350, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_336])).
% 3.21/1.61  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.21/1.61  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.21/1.61  tff(c_180, plain, (![A_89, C_90, B_91]: (m1_subset_1(A_89, C_90) | ~m1_subset_1(B_91, k1_zfmisc_1(C_90)) | ~r2_hidden(A_89, B_91))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.21/1.61  tff(c_188, plain, (![A_93, B_94, A_95]: (m1_subset_1(A_93, B_94) | ~r2_hidden(A_93, A_95) | ~r1_tarski(A_95, B_94))), inference(resolution, [status(thm)], [c_10, c_180])).
% 3.21/1.61  tff(c_192, plain, (![A_96, B_97]: (m1_subset_1('#skF_2'(A_96), B_97) | ~r1_tarski(A_96, B_97) | k1_xboole_0=A_96)), inference(resolution, [status(thm)], [c_6, c_188])).
% 3.21/1.61  tff(c_64, plain, (![D_55]: (~r2_hidden(D_55, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_55, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.21/1.61  tff(c_69, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_64])).
% 3.21/1.61  tff(c_106, plain, (~m1_subset_1('#skF_2'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_69])).
% 3.21/1.61  tff(c_218, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_192, c_106])).
% 3.21/1.61  tff(c_221, plain, (~r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_218])).
% 3.21/1.61  tff(c_351, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_350, c_221])).
% 3.21/1.61  tff(c_360, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_18, c_351])).
% 3.21/1.61  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_124, c_360])).
% 3.21/1.61  tff(c_365, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_218])).
% 3.21/1.61  tff(c_430, plain, (![A_138, B_139, C_140]: (k2_relset_1(A_138, B_139, C_140)=k2_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.21/1.61  tff(c_441, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_430])).
% 3.21/1.61  tff(c_445, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_365, c_441])).
% 3.21/1.61  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_445])).
% 3.21/1.61  tff(c_448, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_69])).
% 3.21/1.61  tff(c_606, plain, (![A_185, B_186, C_187]: (k2_relset_1(A_185, B_186, C_187)=k2_relat_1(C_187) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_185, B_186))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.21/1.61  tff(c_617, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_606])).
% 3.21/1.61  tff(c_621, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_448, c_617])).
% 3.21/1.61  tff(c_623, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_621])).
% 3.21/1.61  tff(c_624, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_97])).
% 3.21/1.61  tff(c_26, plain, (![A_22]: (k1_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.21/1.61  tff(c_96, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_89, c_26])).
% 3.21/1.61  tff(c_98, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_96])).
% 3.21/1.61  tff(c_626, plain, (k1_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_624, c_98])).
% 3.21/1.61  tff(c_629, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_624, c_6])).
% 3.21/1.61  tff(c_709, plain, (![C_201, A_202, B_203]: (v4_relat_1(C_201, A_202) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_202, B_203))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.21/1.61  tff(c_718, plain, (v4_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_709])).
% 3.21/1.61  tff(c_730, plain, (![B_207, A_208]: (k7_relat_1(B_207, A_208)=B_207 | ~v4_relat_1(B_207, A_208) | ~v1_relat_1(B_207))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.21/1.61  tff(c_733, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_718, c_730])).
% 3.21/1.61  tff(c_736, plain, (k7_relat_1('#skF_5', '#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_89, c_733])).
% 3.21/1.61  tff(c_32, plain, (![B_26, A_25]: (r1_xboole_0(k1_relat_1(B_26), A_25) | k7_relat_1(B_26, A_25)!=k1_xboole_0 | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.21/1.61  tff(c_782, plain, (![B_26, A_25]: (r1_xboole_0(k1_relat_1(B_26), A_25) | k7_relat_1(B_26, A_25)!='#skF_5' | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_32])).
% 3.21/1.61  tff(c_792, plain, (![B_225, A_226]: (k3_xboole_0(k1_relat_1(B_225), A_226)=k1_relat_1(k7_relat_1(B_225, A_226)) | ~v1_relat_1(B_225))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.21/1.61  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.21/1.61  tff(c_1013, plain, (![B_263, A_264, C_265]: (~r1_xboole_0(k1_relat_1(B_263), A_264) | ~r2_hidden(C_265, k1_relat_1(k7_relat_1(B_263, A_264))) | ~v1_relat_1(B_263))), inference(superposition, [status(thm), theory('equality')], [c_792, c_4])).
% 3.21/1.61  tff(c_1016, plain, (![C_265]: (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_3') | ~r2_hidden(C_265, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_736, c_1013])).
% 3.21/1.61  tff(c_1022, plain, (![C_265]: (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_3') | ~r2_hidden(C_265, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_1016])).
% 3.21/1.61  tff(c_1024, plain, (~r1_xboole_0(k1_relat_1('#skF_5'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1022])).
% 3.21/1.61  tff(c_1027, plain, (k7_relat_1('#skF_5', '#skF_3')!='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_782, c_1024])).
% 3.21/1.61  tff(c_1031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_736, c_1027])).
% 3.21/1.61  tff(c_1034, plain, (![C_266]: (~r2_hidden(C_266, k1_relat_1('#skF_5')))), inference(splitRight, [status(thm)], [c_1022])).
% 3.21/1.61  tff(c_1038, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_629, c_1034])).
% 3.21/1.61  tff(c_1042, plain, $false, inference(negUnitSimplification, [status(thm)], [c_626, c_1038])).
% 3.21/1.61  tff(c_1043, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_96])).
% 3.21/1.61  tff(c_44, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.21/1.61  tff(c_1048, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1043, c_44])).
% 3.21/1.61  tff(c_1044, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_96])).
% 3.21/1.61  tff(c_1053, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1043, c_1044])).
% 3.21/1.61  tff(c_1367, plain, (![A_324, B_325, C_326]: (k1_relset_1(A_324, B_325, C_326)=k1_relat_1(C_326) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_324, B_325))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.21/1.61  tff(c_1378, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_1367])).
% 3.21/1.61  tff(c_1382, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_1378])).
% 3.21/1.61  tff(c_1384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1048, c_1382])).
% 3.21/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.61  
% 3.21/1.61  Inference rules
% 3.21/1.61  ----------------------
% 3.21/1.61  #Ref     : 0
% 3.21/1.61  #Sup     : 271
% 3.21/1.61  #Fact    : 0
% 3.21/1.61  #Define  : 0
% 3.21/1.61  #Split   : 11
% 3.21/1.61  #Chain   : 0
% 3.21/1.61  #Close   : 0
% 3.21/1.61  
% 3.21/1.61  Ordering : KBO
% 3.21/1.61  
% 3.21/1.61  Simplification rules
% 3.21/1.61  ----------------------
% 3.21/1.61  #Subsume      : 18
% 3.21/1.61  #Demod        : 110
% 3.21/1.61  #Tautology    : 96
% 3.21/1.61  #SimpNegUnit  : 6
% 3.21/1.61  #BackRed      : 19
% 3.21/1.61  
% 3.21/1.61  #Partial instantiations: 0
% 3.21/1.61  #Strategies tried      : 1
% 3.21/1.61  
% 3.21/1.61  Timing (in seconds)
% 3.21/1.61  ----------------------
% 3.21/1.61  Preprocessing        : 0.35
% 3.21/1.62  Parsing              : 0.19
% 3.21/1.62  CNF conversion       : 0.03
% 3.21/1.62  Main loop            : 0.43
% 3.21/1.62  Inferencing          : 0.17
% 3.21/1.62  Reduction            : 0.12
% 3.21/1.62  Demodulation         : 0.08
% 3.21/1.62  BG Simplification    : 0.02
% 3.21/1.62  Subsumption          : 0.06
% 3.21/1.62  Abstraction          : 0.02
% 3.21/1.62  MUC search           : 0.00
% 3.21/1.62  Cooper               : 0.00
% 3.21/1.62  Total                : 0.82
% 3.21/1.62  Index Insertion      : 0.00
% 3.21/1.62  Index Deletion       : 0.00
% 3.21/1.62  Index Matching       : 0.00
% 3.21/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
