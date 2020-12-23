%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:21 EST 2020

% Result     : Theorem 5.09s
% Output     : CNFRefutation 5.09s
% Verified   : 
% Statistics : Number of formulae       :  150 (1141 expanded)
%              Number of leaves         :   38 ( 396 expanded)
%              Depth                    :   15
%              Number of atoms          :  269 (3243 expanded)
%              Number of equality atoms :   68 ( 960 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r2_hidden('#skF_3'(A_6,B_7),A_6)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_76,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_80,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_76])).

tff(c_137,plain,(
    ! [C_65,B_66,A_67] :
      ( v5_relat_1(C_65,B_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_141,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_137])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_277,plain,(
    ! [A_96,B_97,C_98] :
      ( k2_relset_1(A_96,B_97,C_98) = k2_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_281,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_277])).

tff(c_48,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_282,plain,(
    k2_relat_1('#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_48])).

tff(c_158,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_2'(A_70,B_71),B_71)
      | r2_hidden('#skF_3'(A_70,B_71),A_70)
      | B_71 = A_70 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2624,plain,(
    ! [A_309,B_310,B_311] :
      ( r2_hidden('#skF_3'(A_309,B_310),B_311)
      | ~ r1_tarski(A_309,B_311)
      | r2_hidden('#skF_2'(A_309,B_310),B_310)
      | B_310 = A_309 ) ),
    inference(resolution,[status(thm)],[c_158,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2656,plain,(
    ! [A_309,B_311] :
      ( ~ r1_tarski(A_309,B_311)
      | r2_hidden('#skF_2'(A_309,B_311),B_311)
      | B_311 = A_309 ) ),
    inference(resolution,[status(thm)],[c_2624,c_10])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_1'(A_47,B_48),B_48)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_86])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_256,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_260,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_256])).

tff(c_1135,plain,(
    ! [B_202,A_203,C_204] :
      ( k1_xboole_0 = B_202
      | k1_relset_1(A_203,B_202,C_204) = A_203
      | ~ v1_funct_2(C_204,A_203,B_202)
      | ~ m1_subset_1(C_204,k1_zfmisc_1(k2_zfmisc_1(A_203,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1138,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_1135])).

tff(c_1141,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_260,c_1138])).

tff(c_1142,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1141])).

tff(c_58,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_7'(D_34),'#skF_4')
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_100,plain,(
    ! [C_52,B_53,A_54] :
      ( r2_hidden(C_52,B_53)
      | ~ r2_hidden(C_52,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_106,plain,(
    ! [D_34,B_53] :
      ( r2_hidden('#skF_7'(D_34),B_53)
      | ~ r1_tarski('#skF_4',B_53)
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_100])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_56,plain,(
    ! [D_34] :
      ( k1_funct_1('#skF_6','#skF_7'(D_34)) = D_34
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_424,plain,(
    ! [B_116,A_117] :
      ( r2_hidden(k1_funct_1(B_116,A_117),k2_relat_1(B_116))
      | ~ r2_hidden(A_117,k1_relat_1(B_116))
      | ~ v1_funct_1(B_116)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_432,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_7'(D_34),k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_424])).

tff(c_460,plain,(
    ! [D_121] :
      ( r2_hidden(D_121,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_7'(D_121),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_121,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_54,c_432])).

tff(c_465,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,k2_relat_1('#skF_6'))
      | ~ r1_tarski('#skF_4',k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_106,c_460])).

tff(c_466,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_465])).

tff(c_1145,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1142,c_466])).

tff(c_1150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1145])).

tff(c_1151,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1141])).

tff(c_38,plain,(
    ! [C_30,A_28] :
      ( k1_xboole_0 = C_30
      | ~ v1_funct_2(C_30,A_28,k1_xboole_0)
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1318,plain,(
    ! [C_214,A_215] :
      ( C_214 = '#skF_5'
      | ~ v1_funct_2(C_214,A_215,'#skF_5')
      | A_215 = '#skF_5'
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_215,'#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_1151,c_1151,c_1151,c_38])).

tff(c_1321,plain,
    ( '#skF_5' = '#skF_6'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_1318])).

tff(c_1324,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1321])).

tff(c_1325,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1324])).

tff(c_118,plain,(
    ! [D_60,B_61] :
      ( r2_hidden('#skF_7'(D_60),B_61)
      | ~ r1_tarski('#skF_4',B_61)
      | ~ r2_hidden(D_60,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_100])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( ~ r1_tarski(B_15,A_14)
      | ~ r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_142,plain,(
    ! [B_68,D_69] :
      ( ~ r1_tarski(B_68,'#skF_7'(D_69))
      | ~ r1_tarski('#skF_4',B_68)
      | ~ r2_hidden(D_69,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_118,c_24])).

tff(c_157,plain,(
    ! [D_69] :
      ( ~ r1_tarski('#skF_4',k1_xboole_0)
      | ~ r2_hidden(D_69,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_142])).

tff(c_173,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_1188,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_173])).

tff(c_1334,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1325,c_1188])).

tff(c_1356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1334])).

tff(c_1357,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1324])).

tff(c_1375,plain,(
    k2_relat_1('#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_282])).

tff(c_1380,plain,(
    v5_relat_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_141])).

tff(c_174,plain,(
    ! [A_72,B_73,B_74] :
      ( r2_hidden('#skF_1'(A_72,B_73),B_74)
      | ~ r1_tarski(A_72,B_74)
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_197,plain,(
    ! [B_78,A_79,B_80] :
      ( ~ r1_tarski(B_78,'#skF_1'(A_79,B_80))
      | ~ r1_tarski(A_79,B_78)
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_174,c_24])).

tff(c_213,plain,(
    ! [A_81,B_82] :
      ( ~ r1_tarski(A_81,k1_xboole_0)
      | r1_tarski(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_16,c_197])).

tff(c_228,plain,(
    ! [B_83,B_84] :
      ( r1_tarski(k2_relat_1(B_83),B_84)
      | ~ v5_relat_1(B_83,k1_xboole_0)
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_20,c_213])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( v5_relat_1(B_11,A_10)
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_253,plain,(
    ! [B_83,B_84] :
      ( v5_relat_1(B_83,B_84)
      | ~ v5_relat_1(B_83,k1_xboole_0)
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_228,c_18])).

tff(c_1185,plain,(
    ! [B_83,B_84] :
      ( v5_relat_1(B_83,B_84)
      | ~ v5_relat_1(B_83,'#skF_5')
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_253])).

tff(c_1648,plain,(
    ! [B_236,B_237] :
      ( v5_relat_1(B_236,B_237)
      | ~ v5_relat_1(B_236,'#skF_6')
      | ~ v1_relat_1(B_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_1185])).

tff(c_1650,plain,(
    ! [B_237] :
      ( v5_relat_1('#skF_6',B_237)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1380,c_1648])).

tff(c_1663,plain,(
    ! [B_240] : v5_relat_1('#skF_6',B_240) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1650])).

tff(c_112,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(k2_relat_1(B_58),A_59)
      | ~ v5_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_81,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_1'(A_45,B_46),A_45)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,(
    ! [A_45,B_46] :
      ( ~ r1_tarski(A_45,'#skF_1'(A_45,B_46))
      | r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_81,c_24])).

tff(c_117,plain,(
    ! [B_58,B_46] :
      ( r1_tarski(k2_relat_1(B_58),B_46)
      | ~ v5_relat_1(B_58,'#skF_1'(k2_relat_1(B_58),B_46))
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_112,c_85])).

tff(c_1678,plain,(
    ! [B_46] :
      ( r1_tarski(k2_relat_1('#skF_6'),B_46)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1663,c_117])).

tff(c_1813,plain,(
    ! [B_245] : r1_tarski(k2_relat_1('#skF_6'),B_245) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1678])).

tff(c_1194,plain,(
    ! [A_205] : r1_tarski('#skF_5',A_205) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_16])).

tff(c_170,plain,(
    ! [B_71,A_70] :
      ( ~ r1_tarski(B_71,'#skF_2'(A_70,B_71))
      | r2_hidden('#skF_3'(A_70,B_71),A_70)
      | B_71 = A_70 ) ),
    inference(resolution,[status(thm)],[c_158,c_24])).

tff(c_1219,plain,(
    ! [A_70] :
      ( r2_hidden('#skF_3'(A_70,'#skF_5'),A_70)
      | A_70 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_1194,c_170])).

tff(c_1515,plain,(
    ! [A_223] :
      ( r2_hidden('#skF_3'(A_223,'#skF_6'),A_223)
      | A_223 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_1357,c_1219])).

tff(c_1528,plain,(
    ! [A_223] :
      ( ~ r1_tarski(A_223,'#skF_3'(A_223,'#skF_6'))
      | A_223 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_1515,c_24])).

tff(c_1817,plain,(
    k2_relat_1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1813,c_1528])).

tff(c_1855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1375,c_1817])).

tff(c_1856,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_34,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_287,plain,(
    ! [A_99,B_100] :
      ( ~ r2_hidden('#skF_2'(A_99,B_100),A_99)
      | r2_hidden('#skF_3'(A_99,B_100),A_99)
      | B_100 = A_99 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2968,plain,(
    ! [A_323,B_324,B_325] :
      ( r2_hidden('#skF_3'(A_323,B_324),B_325)
      | ~ r1_tarski(A_323,B_325)
      | ~ r2_hidden('#skF_2'(A_323,B_324),A_323)
      | B_324 = A_323 ) ),
    inference(resolution,[status(thm)],[c_287,c_2])).

tff(c_3338,plain,(
    ! [B_350,B_351] :
      ( r2_hidden('#skF_3'(k2_relat_1('#skF_6'),B_350),B_351)
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_351)
      | k2_relat_1('#skF_6') = B_350
      | ~ r2_hidden('#skF_2'(k2_relat_1('#skF_6'),B_350),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1856,c_2968])).

tff(c_1863,plain,(
    ! [D_246] :
      ( r2_hidden(D_246,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_246,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),A_6)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1881,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3'(k2_relat_1('#skF_6'),B_7),B_7)
      | k2_relat_1('#skF_6') = B_7
      | ~ r2_hidden('#skF_2'(k2_relat_1('#skF_6'),B_7),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1863,c_8])).

tff(c_3474,plain,(
    ! [B_366] :
      ( ~ r1_tarski(k2_relat_1('#skF_6'),B_366)
      | k2_relat_1('#skF_6') = B_366
      | ~ r2_hidden('#skF_2'(k2_relat_1('#skF_6'),B_366),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3338,c_1881])).

tff(c_3480,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2656,c_3474])).

tff(c_3487,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_282,c_3480])).

tff(c_3493,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_3487])).

tff(c_3500,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_141,c_3493])).

tff(c_3503,plain,(
    ! [D_367] : ~ r2_hidden(D_367,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_3523,plain,(
    ! [B_369] :
      ( r2_hidden('#skF_2'('#skF_5',B_369),B_369)
      | B_369 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_14,c_3503])).

tff(c_3550,plain,(
    ! [B_372] :
      ( ~ r1_tarski(B_372,'#skF_2'('#skF_5',B_372))
      | B_372 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_3523,c_24])).

tff(c_3566,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_16,c_3550])).

tff(c_3502,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_3567,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3566,c_3502])).

tff(c_3574,plain,(
    ! [B_373,B_374] :
      ( r2_hidden('#skF_2'('#skF_5',B_373),B_374)
      | ~ r1_tarski(B_373,B_374)
      | B_373 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_3523,c_2])).

tff(c_3501,plain,(
    ! [D_69] : ~ r2_hidden(D_69,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_3587,plain,(
    ! [B_375] :
      ( ~ r1_tarski(B_375,'#skF_5')
      | B_375 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_3574,c_3501])).

tff(c_3603,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3567,c_3587])).

tff(c_3619,plain,(
    k2_relset_1('#skF_4','#skF_4','#skF_6') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3603,c_3603,c_48])).

tff(c_3617,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3603,c_141])).

tff(c_3606,plain,(
    ! [B_11] :
      ( k2_relat_1(B_11) = '#skF_5'
      | ~ v5_relat_1(B_11,'#skF_5')
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_20,c_3587])).

tff(c_3727,plain,(
    ! [B_385] :
      ( k2_relat_1(B_385) = '#skF_4'
      | ~ v5_relat_1(B_385,'#skF_4')
      | ~ v1_relat_1(B_385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3603,c_3603,c_3606])).

tff(c_3730,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3617,c_3727])).

tff(c_3733,plain,(
    k2_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_3730])).

tff(c_3618,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3603,c_50])).

tff(c_3794,plain,(
    ! [A_391,B_392,C_393] :
      ( k2_relset_1(A_391,B_392,C_393) = k2_relat_1(C_393)
      | ~ m1_subset_1(C_393,k1_zfmisc_1(k2_zfmisc_1(A_391,B_392))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3797,plain,(
    k2_relset_1('#skF_4','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3618,c_3794])).

tff(c_3799,plain,(
    k2_relset_1('#skF_4','#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3733,c_3797])).

tff(c_3801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3619,c_3799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:27:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.09/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/1.96  
% 5.09/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/1.96  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 5.09/1.96  
% 5.09/1.96  %Foreground sorts:
% 5.09/1.96  
% 5.09/1.96  
% 5.09/1.96  %Background operators:
% 5.09/1.96  
% 5.09/1.96  
% 5.09/1.96  %Foreground operators:
% 5.09/1.96  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.09/1.96  tff('#skF_7', type, '#skF_7': $i > $i).
% 5.09/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.09/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.09/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.09/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.09/1.96  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.09/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.09/1.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.09/1.96  tff('#skF_5', type, '#skF_5': $i).
% 5.09/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.09/1.96  tff('#skF_6', type, '#skF_6': $i).
% 5.09/1.96  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.09/1.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.09/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.09/1.96  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.09/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.09/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.09/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.09/1.96  tff('#skF_4', type, '#skF_4': $i).
% 5.09/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.09/1.96  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.09/1.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.09/1.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.09/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.09/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.09/1.96  
% 5.09/1.98  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.09/1.98  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 5.09/1.98  tff(f_115, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 5.09/1.98  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.09/1.98  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.09/1.98  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.09/1.98  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.09/1.98  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.09/1.98  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.09/1.98  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.09/1.98  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 5.09/1.98  tff(f_60, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.09/1.98  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.09/1.98  tff(c_14, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r2_hidden('#skF_3'(A_6, B_7), A_6) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.09/1.98  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.09/1.98  tff(c_76, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.09/1.98  tff(c_80, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_76])).
% 5.09/1.98  tff(c_137, plain, (![C_65, B_66, A_67]: (v5_relat_1(C_65, B_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.09/1.98  tff(c_141, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_137])).
% 5.09/1.98  tff(c_20, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.09/1.98  tff(c_277, plain, (![A_96, B_97, C_98]: (k2_relset_1(A_96, B_97, C_98)=k2_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.09/1.98  tff(c_281, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_277])).
% 5.09/1.98  tff(c_48, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.09/1.98  tff(c_282, plain, (k2_relat_1('#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_281, c_48])).
% 5.09/1.99  tff(c_158, plain, (![A_70, B_71]: (r2_hidden('#skF_2'(A_70, B_71), B_71) | r2_hidden('#skF_3'(A_70, B_71), A_70) | B_71=A_70)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.09/1.99  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.99  tff(c_2624, plain, (![A_309, B_310, B_311]: (r2_hidden('#skF_3'(A_309, B_310), B_311) | ~r1_tarski(A_309, B_311) | r2_hidden('#skF_2'(A_309, B_310), B_310) | B_310=A_309)), inference(resolution, [status(thm)], [c_158, c_2])).
% 5.09/1.99  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.09/1.99  tff(c_2656, plain, (![A_309, B_311]: (~r1_tarski(A_309, B_311) | r2_hidden('#skF_2'(A_309, B_311), B_311) | B_311=A_309)), inference(resolution, [status(thm)], [c_2624, c_10])).
% 5.09/1.99  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.99  tff(c_86, plain, (![A_47, B_48]: (~r2_hidden('#skF_1'(A_47, B_48), B_48) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.99  tff(c_91, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_86])).
% 5.09/1.99  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.09/1.99  tff(c_256, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.09/1.99  tff(c_260, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_256])).
% 5.09/1.99  tff(c_1135, plain, (![B_202, A_203, C_204]: (k1_xboole_0=B_202 | k1_relset_1(A_203, B_202, C_204)=A_203 | ~v1_funct_2(C_204, A_203, B_202) | ~m1_subset_1(C_204, k1_zfmisc_1(k2_zfmisc_1(A_203, B_202))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.09/1.99  tff(c_1138, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_1135])).
% 5.09/1.99  tff(c_1141, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_260, c_1138])).
% 5.09/1.99  tff(c_1142, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1141])).
% 5.09/1.99  tff(c_58, plain, (![D_34]: (r2_hidden('#skF_7'(D_34), '#skF_4') | ~r2_hidden(D_34, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.09/1.99  tff(c_100, plain, (![C_52, B_53, A_54]: (r2_hidden(C_52, B_53) | ~r2_hidden(C_52, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.99  tff(c_106, plain, (![D_34, B_53]: (r2_hidden('#skF_7'(D_34), B_53) | ~r1_tarski('#skF_4', B_53) | ~r2_hidden(D_34, '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_100])).
% 5.09/1.99  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.09/1.99  tff(c_56, plain, (![D_34]: (k1_funct_1('#skF_6', '#skF_7'(D_34))=D_34 | ~r2_hidden(D_34, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.09/1.99  tff(c_424, plain, (![B_116, A_117]: (r2_hidden(k1_funct_1(B_116, A_117), k2_relat_1(B_116)) | ~r2_hidden(A_117, k1_relat_1(B_116)) | ~v1_funct_1(B_116) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.09/1.99  tff(c_432, plain, (![D_34]: (r2_hidden(D_34, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_7'(D_34), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(D_34, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_424])).
% 5.09/1.99  tff(c_460, plain, (![D_121]: (r2_hidden(D_121, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_7'(D_121), k1_relat_1('#skF_6')) | ~r2_hidden(D_121, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_54, c_432])).
% 5.09/1.99  tff(c_465, plain, (![D_34]: (r2_hidden(D_34, k2_relat_1('#skF_6')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_6')) | ~r2_hidden(D_34, '#skF_5'))), inference(resolution, [status(thm)], [c_106, c_460])).
% 5.09/1.99  tff(c_466, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_465])).
% 5.09/1.99  tff(c_1145, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1142, c_466])).
% 5.09/1.99  tff(c_1150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_1145])).
% 5.09/1.99  tff(c_1151, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1141])).
% 5.09/1.99  tff(c_38, plain, (![C_30, A_28]: (k1_xboole_0=C_30 | ~v1_funct_2(C_30, A_28, k1_xboole_0) | k1_xboole_0=A_28 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.09/1.99  tff(c_1318, plain, (![C_214, A_215]: (C_214='#skF_5' | ~v1_funct_2(C_214, A_215, '#skF_5') | A_215='#skF_5' | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_215, '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_1151, c_1151, c_1151, c_38])).
% 5.09/1.99  tff(c_1321, plain, ('#skF_5'='#skF_6' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_50, c_1318])).
% 5.09/1.99  tff(c_1324, plain, ('#skF_5'='#skF_6' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1321])).
% 5.09/1.99  tff(c_1325, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_1324])).
% 5.09/1.99  tff(c_118, plain, (![D_60, B_61]: (r2_hidden('#skF_7'(D_60), B_61) | ~r1_tarski('#skF_4', B_61) | ~r2_hidden(D_60, '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_100])).
% 5.09/1.99  tff(c_24, plain, (![B_15, A_14]: (~r1_tarski(B_15, A_14) | ~r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.09/1.99  tff(c_142, plain, (![B_68, D_69]: (~r1_tarski(B_68, '#skF_7'(D_69)) | ~r1_tarski('#skF_4', B_68) | ~r2_hidden(D_69, '#skF_5'))), inference(resolution, [status(thm)], [c_118, c_24])).
% 5.09/1.99  tff(c_157, plain, (![D_69]: (~r1_tarski('#skF_4', k1_xboole_0) | ~r2_hidden(D_69, '#skF_5'))), inference(resolution, [status(thm)], [c_16, c_142])).
% 5.09/1.99  tff(c_173, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_157])).
% 5.09/1.99  tff(c_1188, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_173])).
% 5.09/1.99  tff(c_1334, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1325, c_1188])).
% 5.09/1.99  tff(c_1356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_1334])).
% 5.09/1.99  tff(c_1357, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_1324])).
% 5.09/1.99  tff(c_1375, plain, (k2_relat_1('#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1357, c_282])).
% 5.09/1.99  tff(c_1380, plain, (v5_relat_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1357, c_141])).
% 5.09/1.99  tff(c_174, plain, (![A_72, B_73, B_74]: (r2_hidden('#skF_1'(A_72, B_73), B_74) | ~r1_tarski(A_72, B_74) | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_6, c_100])).
% 5.09/1.99  tff(c_197, plain, (![B_78, A_79, B_80]: (~r1_tarski(B_78, '#skF_1'(A_79, B_80)) | ~r1_tarski(A_79, B_78) | r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_174, c_24])).
% 5.09/1.99  tff(c_213, plain, (![A_81, B_82]: (~r1_tarski(A_81, k1_xboole_0) | r1_tarski(A_81, B_82))), inference(resolution, [status(thm)], [c_16, c_197])).
% 5.09/1.99  tff(c_228, plain, (![B_83, B_84]: (r1_tarski(k2_relat_1(B_83), B_84) | ~v5_relat_1(B_83, k1_xboole_0) | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_20, c_213])).
% 5.09/1.99  tff(c_18, plain, (![B_11, A_10]: (v5_relat_1(B_11, A_10) | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.09/1.99  tff(c_253, plain, (![B_83, B_84]: (v5_relat_1(B_83, B_84) | ~v5_relat_1(B_83, k1_xboole_0) | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_228, c_18])).
% 5.09/1.99  tff(c_1185, plain, (![B_83, B_84]: (v5_relat_1(B_83, B_84) | ~v5_relat_1(B_83, '#skF_5') | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_253])).
% 5.09/1.99  tff(c_1648, plain, (![B_236, B_237]: (v5_relat_1(B_236, B_237) | ~v5_relat_1(B_236, '#skF_6') | ~v1_relat_1(B_236))), inference(demodulation, [status(thm), theory('equality')], [c_1357, c_1185])).
% 5.09/1.99  tff(c_1650, plain, (![B_237]: (v5_relat_1('#skF_6', B_237) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1380, c_1648])).
% 5.09/1.99  tff(c_1663, plain, (![B_240]: (v5_relat_1('#skF_6', B_240))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1650])).
% 5.09/1.99  tff(c_112, plain, (![B_58, A_59]: (r1_tarski(k2_relat_1(B_58), A_59) | ~v5_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.09/1.99  tff(c_81, plain, (![A_45, B_46]: (r2_hidden('#skF_1'(A_45, B_46), A_45) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.09/1.99  tff(c_85, plain, (![A_45, B_46]: (~r1_tarski(A_45, '#skF_1'(A_45, B_46)) | r1_tarski(A_45, B_46))), inference(resolution, [status(thm)], [c_81, c_24])).
% 5.09/1.99  tff(c_117, plain, (![B_58, B_46]: (r1_tarski(k2_relat_1(B_58), B_46) | ~v5_relat_1(B_58, '#skF_1'(k2_relat_1(B_58), B_46)) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_112, c_85])).
% 5.09/1.99  tff(c_1678, plain, (![B_46]: (r1_tarski(k2_relat_1('#skF_6'), B_46) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1663, c_117])).
% 5.09/1.99  tff(c_1813, plain, (![B_245]: (r1_tarski(k2_relat_1('#skF_6'), B_245))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1678])).
% 5.09/1.99  tff(c_1194, plain, (![A_205]: (r1_tarski('#skF_5', A_205))), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_16])).
% 5.09/1.99  tff(c_170, plain, (![B_71, A_70]: (~r1_tarski(B_71, '#skF_2'(A_70, B_71)) | r2_hidden('#skF_3'(A_70, B_71), A_70) | B_71=A_70)), inference(resolution, [status(thm)], [c_158, c_24])).
% 5.09/1.99  tff(c_1219, plain, (![A_70]: (r2_hidden('#skF_3'(A_70, '#skF_5'), A_70) | A_70='#skF_5')), inference(resolution, [status(thm)], [c_1194, c_170])).
% 5.09/1.99  tff(c_1515, plain, (![A_223]: (r2_hidden('#skF_3'(A_223, '#skF_6'), A_223) | A_223='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1357, c_1357, c_1219])).
% 5.09/1.99  tff(c_1528, plain, (![A_223]: (~r1_tarski(A_223, '#skF_3'(A_223, '#skF_6')) | A_223='#skF_6')), inference(resolution, [status(thm)], [c_1515, c_24])).
% 5.09/1.99  tff(c_1817, plain, (k2_relat_1('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_1813, c_1528])).
% 5.09/1.99  tff(c_1855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1375, c_1817])).
% 5.09/1.99  tff(c_1856, plain, (![D_34]: (r2_hidden(D_34, k2_relat_1('#skF_6')) | ~r2_hidden(D_34, '#skF_5'))), inference(splitRight, [status(thm)], [c_465])).
% 5.09/1.99  tff(c_287, plain, (![A_99, B_100]: (~r2_hidden('#skF_2'(A_99, B_100), A_99) | r2_hidden('#skF_3'(A_99, B_100), A_99) | B_100=A_99)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.09/1.99  tff(c_2968, plain, (![A_323, B_324, B_325]: (r2_hidden('#skF_3'(A_323, B_324), B_325) | ~r1_tarski(A_323, B_325) | ~r2_hidden('#skF_2'(A_323, B_324), A_323) | B_324=A_323)), inference(resolution, [status(thm)], [c_287, c_2])).
% 5.09/1.99  tff(c_3338, plain, (![B_350, B_351]: (r2_hidden('#skF_3'(k2_relat_1('#skF_6'), B_350), B_351) | ~r1_tarski(k2_relat_1('#skF_6'), B_351) | k2_relat_1('#skF_6')=B_350 | ~r2_hidden('#skF_2'(k2_relat_1('#skF_6'), B_350), '#skF_5'))), inference(resolution, [status(thm)], [c_1856, c_2968])).
% 5.09/1.99  tff(c_1863, plain, (![D_246]: (r2_hidden(D_246, k2_relat_1('#skF_6')) | ~r2_hidden(D_246, '#skF_5'))), inference(splitRight, [status(thm)], [c_465])).
% 5.09/1.99  tff(c_8, plain, (![A_6, B_7]: (~r2_hidden('#skF_2'(A_6, B_7), A_6) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.09/1.99  tff(c_1881, plain, (![B_7]: (~r2_hidden('#skF_3'(k2_relat_1('#skF_6'), B_7), B_7) | k2_relat_1('#skF_6')=B_7 | ~r2_hidden('#skF_2'(k2_relat_1('#skF_6'), B_7), '#skF_5'))), inference(resolution, [status(thm)], [c_1863, c_8])).
% 5.09/1.99  tff(c_3474, plain, (![B_366]: (~r1_tarski(k2_relat_1('#skF_6'), B_366) | k2_relat_1('#skF_6')=B_366 | ~r2_hidden('#skF_2'(k2_relat_1('#skF_6'), B_366), '#skF_5'))), inference(resolution, [status(thm)], [c_3338, c_1881])).
% 5.09/1.99  tff(c_3480, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_2656, c_3474])).
% 5.09/1.99  tff(c_3487, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_282, c_282, c_3480])).
% 5.09/1.99  tff(c_3493, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_3487])).
% 5.09/1.99  tff(c_3500, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_141, c_3493])).
% 5.09/1.99  tff(c_3503, plain, (![D_367]: (~r2_hidden(D_367, '#skF_5'))), inference(splitRight, [status(thm)], [c_157])).
% 5.09/1.99  tff(c_3523, plain, (![B_369]: (r2_hidden('#skF_2'('#skF_5', B_369), B_369) | B_369='#skF_5')), inference(resolution, [status(thm)], [c_14, c_3503])).
% 5.09/1.99  tff(c_3550, plain, (![B_372]: (~r1_tarski(B_372, '#skF_2'('#skF_5', B_372)) | B_372='#skF_5')), inference(resolution, [status(thm)], [c_3523, c_24])).
% 5.09/1.99  tff(c_3566, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_16, c_3550])).
% 5.09/1.99  tff(c_3502, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_157])).
% 5.09/1.99  tff(c_3567, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3566, c_3502])).
% 5.09/1.99  tff(c_3574, plain, (![B_373, B_374]: (r2_hidden('#skF_2'('#skF_5', B_373), B_374) | ~r1_tarski(B_373, B_374) | B_373='#skF_5')), inference(resolution, [status(thm)], [c_3523, c_2])).
% 5.09/1.99  tff(c_3501, plain, (![D_69]: (~r2_hidden(D_69, '#skF_5'))), inference(splitRight, [status(thm)], [c_157])).
% 5.09/1.99  tff(c_3587, plain, (![B_375]: (~r1_tarski(B_375, '#skF_5') | B_375='#skF_5')), inference(resolution, [status(thm)], [c_3574, c_3501])).
% 5.09/1.99  tff(c_3603, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_3567, c_3587])).
% 5.09/1.99  tff(c_3619, plain, (k2_relset_1('#skF_4', '#skF_4', '#skF_6')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3603, c_3603, c_48])).
% 5.09/1.99  tff(c_3617, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3603, c_141])).
% 5.09/1.99  tff(c_3606, plain, (![B_11]: (k2_relat_1(B_11)='#skF_5' | ~v5_relat_1(B_11, '#skF_5') | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_20, c_3587])).
% 5.09/1.99  tff(c_3727, plain, (![B_385]: (k2_relat_1(B_385)='#skF_4' | ~v5_relat_1(B_385, '#skF_4') | ~v1_relat_1(B_385))), inference(demodulation, [status(thm), theory('equality')], [c_3603, c_3603, c_3606])).
% 5.09/1.99  tff(c_3730, plain, (k2_relat_1('#skF_6')='#skF_4' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3617, c_3727])).
% 5.09/1.99  tff(c_3733, plain, (k2_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_3730])).
% 5.09/1.99  tff(c_3618, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_3603, c_50])).
% 5.09/1.99  tff(c_3794, plain, (![A_391, B_392, C_393]: (k2_relset_1(A_391, B_392, C_393)=k2_relat_1(C_393) | ~m1_subset_1(C_393, k1_zfmisc_1(k2_zfmisc_1(A_391, B_392))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.09/1.99  tff(c_3797, plain, (k2_relset_1('#skF_4', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3618, c_3794])).
% 5.09/1.99  tff(c_3799, plain, (k2_relset_1('#skF_4', '#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3733, c_3797])).
% 5.09/1.99  tff(c_3801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3619, c_3799])).
% 5.09/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.09/1.99  
% 5.09/1.99  Inference rules
% 5.09/1.99  ----------------------
% 5.09/1.99  #Ref     : 0
% 5.09/1.99  #Sup     : 707
% 5.09/1.99  #Fact    : 0
% 5.09/1.99  #Define  : 0
% 5.09/1.99  #Split   : 13
% 5.09/1.99  #Chain   : 0
% 5.09/1.99  #Close   : 0
% 5.09/1.99  
% 5.09/1.99  Ordering : KBO
% 5.09/1.99  
% 5.09/1.99  Simplification rules
% 5.09/1.99  ----------------------
% 5.09/1.99  #Subsume      : 274
% 5.09/1.99  #Demod        : 501
% 5.09/1.99  #Tautology    : 156
% 5.09/1.99  #SimpNegUnit  : 17
% 5.09/1.99  #BackRed      : 177
% 5.09/1.99  
% 5.09/1.99  #Partial instantiations: 0
% 5.09/1.99  #Strategies tried      : 1
% 5.09/1.99  
% 5.09/1.99  Timing (in seconds)
% 5.09/1.99  ----------------------
% 5.09/1.99  Preprocessing        : 0.31
% 5.09/1.99  Parsing              : 0.16
% 5.09/1.99  CNF conversion       : 0.02
% 5.09/1.99  Main loop            : 0.83
% 5.09/1.99  Inferencing          : 0.30
% 5.09/1.99  Reduction            : 0.25
% 5.09/1.99  Demodulation         : 0.17
% 5.09/1.99  BG Simplification    : 0.03
% 5.09/1.99  Subsumption          : 0.19
% 5.09/1.99  Abstraction          : 0.04
% 5.09/1.99  MUC search           : 0.00
% 5.09/1.99  Cooper               : 0.00
% 5.09/1.99  Total                : 1.19
% 5.09/1.99  Index Insertion      : 0.00
% 5.09/1.99  Index Deletion       : 0.00
% 5.09/1.99  Index Matching       : 0.00
% 5.09/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
