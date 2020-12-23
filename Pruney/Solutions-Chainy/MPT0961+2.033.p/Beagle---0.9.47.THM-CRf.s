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
% DateTime   : Thu Dec  3 10:10:46 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 242 expanded)
%              Number of leaves         :   27 (  89 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 567 expanded)
%              Number of equality atoms :   67 ( 239 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_zfmisc_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_94,axiom,(
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

tff(f_42,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_64,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1385,plain,(
    ! [C_239,A_240,B_241] :
      ( m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | ~ r1_tarski(k2_relat_1(C_239),B_241)
      | ~ r1_tarski(k1_relat_1(C_239),A_240)
      | ~ v1_relat_1(C_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_390,plain,(
    ! [C_81,A_82,B_83] :
      ( m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83)))
      | ~ r1_tarski(k2_relat_1(C_81),B_83)
      | ~ r1_tarski(k1_relat_1(C_81),A_82)
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_relset_1(A_8,B_9,C_10) = k1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_624,plain,(
    ! [A_114,B_115,C_116] :
      ( k1_relset_1(A_114,B_115,C_116) = k1_relat_1(C_116)
      | ~ r1_tarski(k2_relat_1(C_116),B_115)
      | ~ r1_tarski(k1_relat_1(C_116),A_114)
      | ~ v1_relat_1(C_116) ) ),
    inference(resolution,[status(thm)],[c_390,c_20])).

tff(c_632,plain,(
    ! [A_117,C_118] :
      ( k1_relset_1(A_117,k2_relat_1(C_118),C_118) = k1_relat_1(C_118)
      | ~ r1_tarski(k1_relat_1(C_118),A_117)
      | ~ v1_relat_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_6,c_624])).

tff(c_638,plain,(
    ! [C_118] :
      ( k1_relset_1(k1_relat_1(C_118),k2_relat_1(C_118),C_118) = k1_relat_1(C_118)
      | ~ v1_relat_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_6,c_632])).

tff(c_119,plain,(
    ! [A_33] :
      ( k2_relat_1(A_33) != k1_xboole_0
      | k1_xboole_0 = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_123,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_50,c_119])).

tff(c_124,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_22,plain,(
    ! [C_13,A_11,B_12] :
      ( m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ r1_tarski(k2_relat_1(C_13),B_12)
      | ~ r1_tarski(k1_relat_1(C_13),A_11)
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_559,plain,(
    ! [B_103,C_104,A_105] :
      ( k1_xboole_0 = B_103
      | v1_funct_2(C_104,A_105,B_103)
      | k1_relset_1(A_105,B_103,C_104) != A_105
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_686,plain,(
    ! [B_130,C_131,A_132] :
      ( k1_xboole_0 = B_130
      | v1_funct_2(C_131,A_132,B_130)
      | k1_relset_1(A_132,B_130,C_131) != A_132
      | ~ r1_tarski(k2_relat_1(C_131),B_130)
      | ~ r1_tarski(k1_relat_1(C_131),A_132)
      | ~ v1_relat_1(C_131) ) ),
    inference(resolution,[status(thm)],[c_22,c_559])).

tff(c_694,plain,(
    ! [C_133,A_134] :
      ( k2_relat_1(C_133) = k1_xboole_0
      | v1_funct_2(C_133,A_134,k2_relat_1(C_133))
      | k1_relset_1(A_134,k2_relat_1(C_133),C_133) != A_134
      | ~ r1_tarski(k1_relat_1(C_133),A_134)
      | ~ v1_relat_1(C_133) ) ),
    inference(resolution,[status(thm)],[c_6,c_686])).

tff(c_48,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_46,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_111,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_704,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_694,c_111])).

tff(c_713,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6,c_704])).

tff(c_714,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_713])).

tff(c_718,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_714])).

tff(c_722,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_718])).

tff(c_723,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_734,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_723,c_14])).

tff(c_113,plain,(
    ! [A_32] :
      ( k1_relat_1(A_32) != k1_xboole_0
      | k1_xboole_0 = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_117,plain,
    ( k1_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_50,c_113])).

tff(c_118,plain,(
    k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_726,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_118])).

tff(c_751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_734,c_726])).

tff(c_752,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_753,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_766,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_753])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_759,plain,(
    ! [A_3] : m1_subset_1('#skF_1',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_8])).

tff(c_889,plain,(
    ! [A_158,B_159,C_160] :
      ( k1_relset_1(A_158,B_159,C_160) = k1_relat_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_896,plain,(
    ! [A_158,B_159] : k1_relset_1(A_158,B_159,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_759,c_889])).

tff(c_898,plain,(
    ! [A_158,B_159] : k1_relset_1(A_158,B_159,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_896])).

tff(c_28,plain,(
    ! [A_17,B_18] : k3_zfmisc_1(A_17,B_18,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_758,plain,(
    ! [A_17,B_18] : k3_zfmisc_1(A_17,B_18,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_752,c_28])).

tff(c_852,plain,(
    ! [A_147,B_148,C_149] : k2_zfmisc_1(k2_zfmisc_1(A_147,B_148),C_149) = k3_zfmisc_1(A_147,B_148,C_149) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [A_14,B_15,C_16] : k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16) = k3_zfmisc_1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_906,plain,(
    ! [A_163,B_164,C_165,C_166] : k3_zfmisc_1(k2_zfmisc_1(A_163,B_164),C_165,C_166) = k2_zfmisc_1(k3_zfmisc_1(A_163,B_164,C_165),C_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_24])).

tff(c_30,plain,(
    ! [A_17,C_19] : k3_zfmisc_1(A_17,k1_xboole_0,C_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_757,plain,(
    ! [A_17,C_19] : k3_zfmisc_1(A_17,'#skF_1',C_19) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_752,c_30])).

tff(c_916,plain,(
    ! [A_163,B_164,C_166] : k2_zfmisc_1(k3_zfmisc_1(A_163,B_164,'#skF_1'),C_166) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_906,c_757])).

tff(c_936,plain,(
    ! [C_166] : k2_zfmisc_1('#skF_1',C_166) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_916])).

tff(c_38,plain,(
    ! [C_22,B_21] :
      ( v1_funct_2(C_22,k1_xboole_0,B_21)
      | k1_relset_1(k1_xboole_0,B_21,C_22) != k1_xboole_0
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1056,plain,(
    ! [C_177,B_178] :
      ( v1_funct_2(C_177,'#skF_1',B_178)
      | k1_relset_1('#skF_1',B_178,C_177) != '#skF_1'
      | ~ m1_subset_1(C_177,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_752,c_752,c_752,c_752,c_38])).

tff(c_1059,plain,(
    ! [B_178] :
      ( v1_funct_2('#skF_1','#skF_1',B_178)
      | k1_relset_1('#skF_1',B_178,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_759,c_1056])).

tff(c_1062,plain,(
    ! [B_178] : v1_funct_2('#skF_1','#skF_1',B_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_1059])).

tff(c_12,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_760,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_752,c_752,c_12])).

tff(c_767,plain,(
    ~ v1_funct_2('#skF_1','#skF_1',k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_111])).

tff(c_785,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_767])).

tff(c_1065,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1062,c_785])).

tff(c_1066,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1397,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1385,c_1066])).

tff(c_1416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6,c_6,c_1397])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.41  
% 3.20/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.42  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k3_zfmisc_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.20/1.42  
% 3.20/1.42  %Foreground sorts:
% 3.20/1.42  
% 3.20/1.42  
% 3.20/1.42  %Background operators:
% 3.20/1.42  
% 3.20/1.42  
% 3.20/1.42  %Foreground operators:
% 3.20/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.20/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.20/1.42  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.20/1.42  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.20/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.42  
% 3.20/1.43  tff(f_105, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.20/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.20/1.43  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.20/1.43  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.20/1.43  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.20/1.43  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.20/1.43  tff(f_42, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.20/1.43  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.20/1.43  tff(f_76, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 3.20/1.43  tff(f_64, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.20/1.43  tff(c_50, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.20/1.43  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.43  tff(c_1385, plain, (![C_239, A_240, B_241]: (m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | ~r1_tarski(k2_relat_1(C_239), B_241) | ~r1_tarski(k1_relat_1(C_239), A_240) | ~v1_relat_1(C_239))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.20/1.43  tff(c_390, plain, (![C_81, A_82, B_83]: (m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))) | ~r1_tarski(k2_relat_1(C_81), B_83) | ~r1_tarski(k1_relat_1(C_81), A_82) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.20/1.43  tff(c_20, plain, (![A_8, B_9, C_10]: (k1_relset_1(A_8, B_9, C_10)=k1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.20/1.43  tff(c_624, plain, (![A_114, B_115, C_116]: (k1_relset_1(A_114, B_115, C_116)=k1_relat_1(C_116) | ~r1_tarski(k2_relat_1(C_116), B_115) | ~r1_tarski(k1_relat_1(C_116), A_114) | ~v1_relat_1(C_116))), inference(resolution, [status(thm)], [c_390, c_20])).
% 3.20/1.43  tff(c_632, plain, (![A_117, C_118]: (k1_relset_1(A_117, k2_relat_1(C_118), C_118)=k1_relat_1(C_118) | ~r1_tarski(k1_relat_1(C_118), A_117) | ~v1_relat_1(C_118))), inference(resolution, [status(thm)], [c_6, c_624])).
% 3.20/1.43  tff(c_638, plain, (![C_118]: (k1_relset_1(k1_relat_1(C_118), k2_relat_1(C_118), C_118)=k1_relat_1(C_118) | ~v1_relat_1(C_118))), inference(resolution, [status(thm)], [c_6, c_632])).
% 3.20/1.43  tff(c_119, plain, (![A_33]: (k2_relat_1(A_33)!=k1_xboole_0 | k1_xboole_0=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.20/1.43  tff(c_123, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_50, c_119])).
% 3.20/1.43  tff(c_124, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_123])).
% 3.20/1.43  tff(c_22, plain, (![C_13, A_11, B_12]: (m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~r1_tarski(k2_relat_1(C_13), B_12) | ~r1_tarski(k1_relat_1(C_13), A_11) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.20/1.43  tff(c_559, plain, (![B_103, C_104, A_105]: (k1_xboole_0=B_103 | v1_funct_2(C_104, A_105, B_103) | k1_relset_1(A_105, B_103, C_104)!=A_105 | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_103))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.20/1.43  tff(c_686, plain, (![B_130, C_131, A_132]: (k1_xboole_0=B_130 | v1_funct_2(C_131, A_132, B_130) | k1_relset_1(A_132, B_130, C_131)!=A_132 | ~r1_tarski(k2_relat_1(C_131), B_130) | ~r1_tarski(k1_relat_1(C_131), A_132) | ~v1_relat_1(C_131))), inference(resolution, [status(thm)], [c_22, c_559])).
% 3.20/1.43  tff(c_694, plain, (![C_133, A_134]: (k2_relat_1(C_133)=k1_xboole_0 | v1_funct_2(C_133, A_134, k2_relat_1(C_133)) | k1_relset_1(A_134, k2_relat_1(C_133), C_133)!=A_134 | ~r1_tarski(k1_relat_1(C_133), A_134) | ~v1_relat_1(C_133))), inference(resolution, [status(thm)], [c_6, c_686])).
% 3.20/1.43  tff(c_48, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.20/1.43  tff(c_46, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.20/1.43  tff(c_52, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 3.20/1.43  tff(c_111, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.20/1.43  tff(c_704, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_694, c_111])).
% 3.20/1.43  tff(c_713, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6, c_704])).
% 3.20/1.43  tff(c_714, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_124, c_713])).
% 3.20/1.43  tff(c_718, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_638, c_714])).
% 3.20/1.43  tff(c_722, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_718])).
% 3.20/1.43  tff(c_723, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_123])).
% 3.20/1.43  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.20/1.43  tff(c_734, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_723, c_723, c_14])).
% 3.20/1.43  tff(c_113, plain, (![A_32]: (k1_relat_1(A_32)!=k1_xboole_0 | k1_xboole_0=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.20/1.43  tff(c_117, plain, (k1_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_50, c_113])).
% 3.20/1.43  tff(c_118, plain, (k1_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_117])).
% 3.20/1.43  tff(c_726, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_723, c_118])).
% 3.20/1.43  tff(c_751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_734, c_726])).
% 3.20/1.43  tff(c_752, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_117])).
% 3.20/1.43  tff(c_753, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_117])).
% 3.20/1.43  tff(c_766, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_752, c_753])).
% 3.20/1.43  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.20/1.43  tff(c_759, plain, (![A_3]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_752, c_8])).
% 3.20/1.43  tff(c_889, plain, (![A_158, B_159, C_160]: (k1_relset_1(A_158, B_159, C_160)=k1_relat_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.20/1.43  tff(c_896, plain, (![A_158, B_159]: (k1_relset_1(A_158, B_159, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_759, c_889])).
% 3.20/1.43  tff(c_898, plain, (![A_158, B_159]: (k1_relset_1(A_158, B_159, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_766, c_896])).
% 3.20/1.43  tff(c_28, plain, (![A_17, B_18]: (k3_zfmisc_1(A_17, B_18, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.20/1.43  tff(c_758, plain, (![A_17, B_18]: (k3_zfmisc_1(A_17, B_18, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_752, c_752, c_28])).
% 3.20/1.43  tff(c_852, plain, (![A_147, B_148, C_149]: (k2_zfmisc_1(k2_zfmisc_1(A_147, B_148), C_149)=k3_zfmisc_1(A_147, B_148, C_149))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.20/1.43  tff(c_24, plain, (![A_14, B_15, C_16]: (k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)=k3_zfmisc_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.20/1.43  tff(c_906, plain, (![A_163, B_164, C_165, C_166]: (k3_zfmisc_1(k2_zfmisc_1(A_163, B_164), C_165, C_166)=k2_zfmisc_1(k3_zfmisc_1(A_163, B_164, C_165), C_166))), inference(superposition, [status(thm), theory('equality')], [c_852, c_24])).
% 3.20/1.43  tff(c_30, plain, (![A_17, C_19]: (k3_zfmisc_1(A_17, k1_xboole_0, C_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.20/1.43  tff(c_757, plain, (![A_17, C_19]: (k3_zfmisc_1(A_17, '#skF_1', C_19)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_752, c_752, c_30])).
% 3.20/1.43  tff(c_916, plain, (![A_163, B_164, C_166]: (k2_zfmisc_1(k3_zfmisc_1(A_163, B_164, '#skF_1'), C_166)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_906, c_757])).
% 3.20/1.43  tff(c_936, plain, (![C_166]: (k2_zfmisc_1('#skF_1', C_166)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_758, c_916])).
% 3.20/1.43  tff(c_38, plain, (![C_22, B_21]: (v1_funct_2(C_22, k1_xboole_0, B_21) | k1_relset_1(k1_xboole_0, B_21, C_22)!=k1_xboole_0 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.20/1.43  tff(c_1056, plain, (![C_177, B_178]: (v1_funct_2(C_177, '#skF_1', B_178) | k1_relset_1('#skF_1', B_178, C_177)!='#skF_1' | ~m1_subset_1(C_177, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_936, c_752, c_752, c_752, c_752, c_38])).
% 3.20/1.43  tff(c_1059, plain, (![B_178]: (v1_funct_2('#skF_1', '#skF_1', B_178) | k1_relset_1('#skF_1', B_178, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_759, c_1056])).
% 3.20/1.43  tff(c_1062, plain, (![B_178]: (v1_funct_2('#skF_1', '#skF_1', B_178))), inference(demodulation, [status(thm), theory('equality')], [c_898, c_1059])).
% 3.20/1.43  tff(c_12, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.20/1.43  tff(c_760, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_752, c_752, c_12])).
% 3.20/1.43  tff(c_767, plain, (~v1_funct_2('#skF_1', '#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_766, c_111])).
% 3.20/1.43  tff(c_785, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_760, c_767])).
% 3.20/1.43  tff(c_1065, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1062, c_785])).
% 3.20/1.43  tff(c_1066, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_52])).
% 3.20/1.43  tff(c_1397, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1385, c_1066])).
% 3.20/1.43  tff(c_1416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_6, c_6, c_1397])).
% 3.20/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.43  
% 3.20/1.43  Inference rules
% 3.20/1.43  ----------------------
% 3.20/1.43  #Ref     : 0
% 3.20/1.43  #Sup     : 310
% 3.20/1.43  #Fact    : 0
% 3.20/1.43  #Define  : 0
% 3.20/1.43  #Split   : 7
% 3.20/1.43  #Chain   : 0
% 3.20/1.43  #Close   : 0
% 3.20/1.43  
% 3.20/1.43  Ordering : KBO
% 3.20/1.43  
% 3.20/1.43  Simplification rules
% 3.20/1.43  ----------------------
% 3.20/1.43  #Subsume      : 22
% 3.20/1.43  #Demod        : 295
% 3.20/1.43  #Tautology    : 217
% 3.20/1.43  #SimpNegUnit  : 1
% 3.20/1.43  #BackRed      : 23
% 3.20/1.43  
% 3.20/1.43  #Partial instantiations: 0
% 3.20/1.43  #Strategies tried      : 1
% 3.20/1.43  
% 3.20/1.43  Timing (in seconds)
% 3.20/1.43  ----------------------
% 3.20/1.44  Preprocessing        : 0.31
% 3.20/1.44  Parsing              : 0.16
% 3.20/1.44  CNF conversion       : 0.02
% 3.20/1.44  Main loop            : 0.43
% 3.20/1.44  Inferencing          : 0.16
% 3.20/1.44  Reduction            : 0.14
% 3.20/1.44  Demodulation         : 0.10
% 3.20/1.44  BG Simplification    : 0.02
% 3.20/1.44  Subsumption          : 0.07
% 3.20/1.44  Abstraction          : 0.03
% 3.20/1.44  MUC search           : 0.00
% 3.20/1.44  Cooper               : 0.00
% 3.20/1.44  Total                : 0.77
% 3.20/1.44  Index Insertion      : 0.00
% 3.20/1.44  Index Deletion       : 0.00
% 3.20/1.44  Index Matching       : 0.00
% 3.20/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
