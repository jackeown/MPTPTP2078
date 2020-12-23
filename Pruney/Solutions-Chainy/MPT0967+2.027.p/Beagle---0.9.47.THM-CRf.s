%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:17 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :  221 (1197 expanded)
%              Number of leaves         :   31 ( 401 expanded)
%              Depth                    :   16
%              Number of atoms          :  423 (3501 expanded)
%              Number of equality atoms :  108 ( 686 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_18,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1461,plain,(
    ! [B_145,A_146] :
      ( v1_relat_1(B_145)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(A_146))
      | ~ v1_relat_1(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1464,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_1461])).

tff(c_1467,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1464])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1474,plain,(
    ! [B_150,A_151] :
      ( v5_relat_1(B_150,A_151)
      | ~ r1_tarski(k2_relat_1(B_150),A_151)
      | ~ v1_relat_1(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1479,plain,(
    ! [B_150] :
      ( v5_relat_1(B_150,k2_relat_1(B_150))
      | ~ v1_relat_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_6,c_1474])).

tff(c_1469,plain,(
    ! [C_147,B_148,A_149] :
      ( v5_relat_1(C_147,B_148)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_149,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1473,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_1469])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1520,plain,(
    ! [B_162,A_163] :
      ( r1_tarski(k2_relat_1(B_162),A_163)
      | ~ v5_relat_1(B_162,A_163)
      | ~ v1_relat_1(B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1623,plain,(
    ! [A_178,A_179,B_180] :
      ( r1_tarski(A_178,A_179)
      | ~ r1_tarski(A_178,k2_relat_1(B_180))
      | ~ v5_relat_1(B_180,A_179)
      | ~ v1_relat_1(B_180) ) ),
    inference(resolution,[status(thm)],[c_1520,c_8])).

tff(c_1707,plain,(
    ! [B_196,A_197,B_198] :
      ( r1_tarski(k2_relat_1(B_196),A_197)
      | ~ v5_relat_1(B_198,A_197)
      | ~ v1_relat_1(B_198)
      | ~ v5_relat_1(B_196,k2_relat_1(B_198))
      | ~ v1_relat_1(B_196) ) ),
    inference(resolution,[status(thm)],[c_16,c_1623])).

tff(c_1713,plain,(
    ! [B_196] :
      ( r1_tarski(k2_relat_1(B_196),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v5_relat_1(B_196,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_196) ) ),
    inference(resolution,[status(thm)],[c_1473,c_1707])).

tff(c_1721,plain,(
    ! [B_199] :
      ( r1_tarski(k2_relat_1(B_199),'#skF_2')
      | ~ v5_relat_1(B_199,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1467,c_1713])).

tff(c_1725,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1479,c_1721])).

tff(c_1728,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1467,c_1725])).

tff(c_44,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1486,plain,(
    ! [A_156,C_157,B_158] :
      ( r1_tarski(A_156,C_157)
      | ~ r1_tarski(B_158,C_157)
      | ~ r1_tarski(A_156,B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1495,plain,(
    ! [A_156] :
      ( r1_tarski(A_156,'#skF_3')
      | ~ r1_tarski(A_156,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_1486])).

tff(c_1739,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1728,c_1495])).

tff(c_1781,plain,(
    ! [D_201,C_202,B_203,A_204] :
      ( m1_subset_1(D_201,k1_zfmisc_1(k2_zfmisc_1(C_202,B_203)))
      | ~ r1_tarski(k2_relat_1(D_201),B_203)
      | ~ m1_subset_1(D_201,k1_zfmisc_1(k2_zfmisc_1(C_202,A_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1809,plain,(
    ! [B_206] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_206)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_206) ) ),
    inference(resolution,[status(thm)],[c_46,c_1781])).

tff(c_42,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_57,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_48,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_214,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_218,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_214])).

tff(c_1179,plain,(
    ! [B_125,A_126,C_127] :
      ( k1_xboole_0 = B_125
      | k1_relset_1(A_126,B_125,C_127) = A_126
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1185,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_1179])).

tff(c_1189,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_218,c_1185])).

tff(c_1190,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_1189])).

tff(c_893,plain,(
    ! [B_109,A_110,C_111] :
      ( k1_xboole_0 = B_109
      | k1_relset_1(A_110,B_109,C_111) = A_110
      | ~ v1_funct_2(C_111,A_110,B_109)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_110,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_896,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_893])).

tff(c_899,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_218,c_896])).

tff(c_900,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_899])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_89,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_86])).

tff(c_92,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_89])).

tff(c_132,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(k2_relat_1(B_45),A_46)
      | ~ v5_relat_1(B_45,A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_93,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(A_36,C_37)
      | ~ r1_tarski(B_38,C_37)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [A_36,A_6] :
      ( r1_tarski(A_36,A_6)
      | ~ r1_tarski(A_36,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_93])).

tff(c_149,plain,(
    ! [B_45,A_6] :
      ( r1_tarski(k2_relat_1(B_45),A_6)
      | ~ v5_relat_1(B_45,k1_xboole_0)
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_132,c_101])).

tff(c_406,plain,(
    ! [D_90,C_91,B_92,A_93] :
      ( m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(C_91,B_92)))
      | ~ r1_tarski(k2_relat_1(D_90),B_92)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(C_91,A_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_433,plain,(
    ! [B_95] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_95)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_95) ) ),
    inference(resolution,[status(thm)],[c_46,c_406])).

tff(c_20,plain,(
    ! [C_16,B_15,A_14] :
      ( v5_relat_1(C_16,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_461,plain,(
    ! [B_96] :
      ( v5_relat_1('#skF_4',B_96)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_96) ) ),
    inference(resolution,[status(thm)],[c_433,c_20])).

tff(c_471,plain,(
    ! [A_6] :
      ( v5_relat_1('#skF_4',A_6)
      | ~ v5_relat_1('#skF_4',k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_149,c_461])).

tff(c_490,plain,(
    ! [A_6] :
      ( v5_relat_1('#skF_4',A_6)
      | ~ v5_relat_1('#skF_4',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_471])).

tff(c_545,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_490])).

tff(c_159,plain,(
    ! [B_51,A_52] :
      ( v5_relat_1(B_51,A_52)
      | ~ r1_tarski(k2_relat_1(B_51),A_52)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_168,plain,(
    ! [B_51] :
      ( v5_relat_1(B_51,k2_relat_1(B_51))
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_6,c_159])).

tff(c_127,plain,(
    ! [C_42,B_43,A_44] :
      ( v5_relat_1(C_42,B_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_131,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_127])).

tff(c_224,plain,(
    ! [A_64,A_65,B_66] :
      ( r1_tarski(A_64,A_65)
      | ~ r1_tarski(A_64,k2_relat_1(B_66))
      | ~ v5_relat_1(B_66,A_65)
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_132,c_8])).

tff(c_331,plain,(
    ! [B_85,A_86,B_87] :
      ( r1_tarski(k2_relat_1(B_85),A_86)
      | ~ v5_relat_1(B_87,A_86)
      | ~ v1_relat_1(B_87)
      | ~ v5_relat_1(B_85,k2_relat_1(B_87))
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_16,c_224])).

tff(c_337,plain,(
    ! [B_85] :
      ( r1_tarski(k2_relat_1(B_85),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v5_relat_1(B_85,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_131,c_331])).

tff(c_345,plain,(
    ! [B_88] :
      ( r1_tarski(k2_relat_1(B_88),'#skF_2')
      | ~ v5_relat_1(B_88,k2_relat_1('#skF_4'))
      | ~ v1_relat_1(B_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_337])).

tff(c_349,plain,
    ( r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_168,c_345])).

tff(c_352,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_349])).

tff(c_102,plain,(
    ! [A_36] :
      ( r1_tarski(A_36,'#skF_3')
      | ~ r1_tarski(A_36,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_44,c_93])).

tff(c_366,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_352,c_102])).

tff(c_658,plain,(
    ! [B_104,A_105,C_106] :
      ( k1_xboole_0 = B_104
      | k1_relset_1(A_105,B_104,C_106) = A_105
      | ~ v1_funct_2(C_106,A_105,B_104)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_105,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_664,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_658])).

tff(c_668,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_218,c_664])).

tff(c_669,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_668])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_40])).

tff(c_58,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_148,plain,(
    ! [B_45] :
      ( r1_tarski(k2_relat_1(B_45),'#skF_3')
      | ~ v5_relat_1(B_45,'#skF_2')
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_132,c_102])).

tff(c_24,plain,(
    ! [A_17,B_18,C_19] :
      ( k1_relset_1(A_17,B_18,C_19) = k1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_498,plain,(
    ! [B_97] :
      ( k1_relset_1('#skF_1',B_97,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_97) ) ),
    inference(resolution,[status(thm)],[c_433,c_24])).

tff(c_512,plain,
    ( k1_relset_1('#skF_1','#skF_3','#skF_4') = k1_relat_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_148,c_498])).

tff(c_529,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_131,c_512])).

tff(c_409,plain,(
    ! [B_92] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_92)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_92) ) ),
    inference(resolution,[status(thm)],[c_46,c_406])).

tff(c_551,plain,(
    ! [B_98,C_99,A_100] :
      ( k1_xboole_0 = B_98
      | v1_funct_2(C_99,A_100,B_98)
      | k1_relset_1(A_100,B_98,C_99) != A_100
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_616,plain,(
    ! [B_103] :
      ( k1_xboole_0 = B_103
      | v1_funct_2('#skF_4','#skF_1',B_103)
      | k1_relset_1('#skF_1',B_103,'#skF_4') != '#skF_1'
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_103) ) ),
    inference(resolution,[status(thm)],[c_409,c_551])).

tff(c_630,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_148,c_616])).

tff(c_650,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_131,c_529,c_630])).

tff(c_651,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_650])).

tff(c_657,plain,(
    k1_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_651])).

tff(c_680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_657])).

tff(c_681,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_651])).

tff(c_30,plain,(
    ! [C_26,A_24] :
      ( k1_xboole_0 = C_26
      | ~ v1_funct_2(C_26,A_24,k1_xboole_0)
      | k1_xboole_0 = A_24
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_453,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_1',k1_xboole_0)
    | k1_xboole_0 = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_4'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_433,c_30])).

tff(c_589,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_453])).

tff(c_684,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_589])).

tff(c_703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_684])).

tff(c_705,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_453])).

tff(c_457,plain,(
    ! [B_95] :
      ( v5_relat_1('#skF_4',B_95)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_95) ) ),
    inference(resolution,[status(thm)],[c_433,c_20])).

tff(c_755,plain,(
    v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_705,c_457])).

tff(c_774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_545,c_755])).

tff(c_781,plain,(
    ! [A_108] : v5_relat_1('#skF_4',A_108) ),
    inference(splitRight,[status(thm)],[c_490])).

tff(c_59,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_59])).

tff(c_151,plain,(
    ! [B_45] :
      ( k2_relat_1(B_45) = k1_xboole_0
      | ~ v5_relat_1(B_45,k1_xboole_0)
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_132,c_70])).

tff(c_801,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_781,c_151])).

tff(c_819,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_801])).

tff(c_822,plain,(
    ! [B_92] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_92)))
      | ~ r1_tarski(k1_xboole_0,B_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_409])).

tff(c_919,plain,(
    ! [B_112] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_112))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_822])).

tff(c_931,plain,(
    ! [B_112] : k1_relset_1('#skF_1',B_112,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_919,c_24])).

tff(c_947,plain,(
    ! [B_112] : k1_relset_1('#skF_1',B_112,'#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_900,c_931])).

tff(c_833,plain,(
    ! [B_92] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_92))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_822])).

tff(c_965,plain,(
    ! [B_114,C_115,A_116] :
      ( k1_xboole_0 = B_114
      | v1_funct_2(C_115,A_116,B_114)
      | k1_relset_1(A_116,B_114,C_115) != A_116
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_116,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_968,plain,(
    ! [B_92] :
      ( k1_xboole_0 = B_92
      | v1_funct_2('#skF_4','#skF_1',B_92)
      | k1_relset_1('#skF_1',B_92,'#skF_4') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_833,c_965])).

tff(c_972,plain,(
    ! [B_117] :
      ( k1_xboole_0 = B_117
      | v1_funct_2('#skF_4','#skF_1',B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_947,c_968])).

tff(c_981,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_972,c_58])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_380,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_366,c_2])).

tff(c_405,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_380])).

tff(c_824,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_405])).

tff(c_985,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_824])).

tff(c_1005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_985])).

tff(c_1006,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_368,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_352,c_2])).

tff(c_381,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_1009,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1006,c_381])).

tff(c_1015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1009])).

tff(c_1016,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_1084,plain,(
    ! [D_118,C_119,B_120,A_121] :
      ( m1_subset_1(D_118,k1_zfmisc_1(k2_zfmisc_1(C_119,B_120)))
      | ~ r1_tarski(k2_relat_1(D_118),B_120)
      | ~ m1_subset_1(D_118,k1_zfmisc_1(k2_zfmisc_1(C_119,A_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1086,plain,(
    ! [B_120] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_120)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_120) ) ),
    inference(resolution,[status(thm)],[c_46,c_1084])).

tff(c_1126,plain,(
    ! [B_123] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_123)))
      | ~ r1_tarski('#skF_2',B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_1086])).

tff(c_1148,plain,(
    ! [B_123] :
      ( k1_relset_1('#skF_1',B_123,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_123) ) ),
    inference(resolution,[status(thm)],[c_1126,c_24])).

tff(c_1224,plain,(
    ! [B_129] :
      ( k1_relset_1('#skF_1',B_129,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_2',B_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_1148])).

tff(c_1234,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_1224])).

tff(c_1088,plain,(
    ! [B_120] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_120)))
      | ~ r1_tarski('#skF_2',B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_1086])).

tff(c_1258,plain,(
    ! [B_132,C_133,A_134] :
      ( k1_xboole_0 = B_132
      | v1_funct_2(C_133,A_134,B_132)
      | k1_relset_1(A_134,B_132,C_133) != A_134
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_134,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1404,plain,(
    ! [B_141] :
      ( k1_xboole_0 = B_141
      | v1_funct_2('#skF_4','#skF_1',B_141)
      | k1_relset_1('#skF_1',B_141,'#skF_4') != '#skF_1'
      | ~ r1_tarski('#skF_2',B_141) ) ),
    inference(resolution,[status(thm)],[c_1088,c_1258])).

tff(c_1407,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1404,c_58])).

tff(c_1410,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1234,c_1407])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( v5_relat_1(B_11,A_10)
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1052,plain,(
    ! [A_10] :
      ( v5_relat_1('#skF_4',A_10)
      | ~ r1_tarski('#skF_2',A_10)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1016,c_14])).

tff(c_1089,plain,(
    ! [A_122] :
      ( v5_relat_1('#skF_4',A_122)
      | ~ r1_tarski('#skF_2',A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1052])).

tff(c_1108,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1089,c_151])).

tff(c_1124,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_1016,c_1108])).

tff(c_1125,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_1124])).

tff(c_1414,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_1125])).

tff(c_1432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1414])).

tff(c_1433,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1830,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1809,c_1433])).

tff(c_1843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1739,c_1830])).

tff(c_1844,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1846,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1844,c_10])).

tff(c_1845,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1851,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1844,c_1845])).

tff(c_1860,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1851,c_46])).

tff(c_1884,plain,(
    ! [B_211,A_212] :
      ( v1_relat_1(B_211)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(A_212))
      | ~ v1_relat_1(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1887,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1860,c_1884])).

tff(c_1890,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1887])).

tff(c_2230,plain,(
    ! [C_263,B_264,A_265] :
      ( v5_relat_1(C_263,B_264)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_265,B_264))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2234,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1860,c_2230])).

tff(c_2260,plain,(
    ! [B_274,A_275] :
      ( r1_tarski(k2_relat_1(B_274),A_275)
      | ~ v5_relat_1(B_274,A_275)
      | ~ v1_relat_1(B_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1861,plain,(
    ! [B_208,A_209] :
      ( B_208 = A_209
      | ~ r1_tarski(B_208,A_209)
      | ~ r1_tarski(A_209,B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1866,plain,(
    ! [A_6] :
      ( A_6 = '#skF_1'
      | ~ r1_tarski(A_6,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1846,c_1861])).

tff(c_2280,plain,(
    ! [B_276] :
      ( k2_relat_1(B_276) = '#skF_1'
      | ~ v5_relat_1(B_276,'#skF_1')
      | ~ v1_relat_1(B_276) ) ),
    inference(resolution,[status(thm)],[c_2260,c_1866])).

tff(c_2283,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2234,c_2280])).

tff(c_2286,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1890,c_2283])).

tff(c_2529,plain,(
    ! [D_312,C_313,B_314,A_315] :
      ( m1_subset_1(D_312,k1_zfmisc_1(k2_zfmisc_1(C_313,B_314)))
      | ~ r1_tarski(k2_relat_1(D_312),B_314)
      | ~ m1_subset_1(D_312,k1_zfmisc_1(k2_zfmisc_1(C_313,A_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2531,plain,(
    ! [B_314] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_314)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_314) ) ),
    inference(resolution,[status(thm)],[c_1860,c_2529])).

tff(c_2534,plain,(
    ! [B_314] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_314))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1846,c_2286,c_2531])).

tff(c_1852,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1851,c_48])).

tff(c_2007,plain,(
    ! [A_233,B_234,C_235] :
      ( k1_relset_1(A_233,B_234,C_235) = k1_relat_1(C_235)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2011,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1860,c_2007])).

tff(c_36,plain,(
    ! [B_25,C_26] :
      ( k1_relset_1(k1_xboole_0,B_25,C_26) = k1_xboole_0
      | ~ v1_funct_2(C_26,k1_xboole_0,B_25)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2140,plain,(
    ! [B_253,C_254] :
      ( k1_relset_1('#skF_1',B_253,C_254) = '#skF_1'
      | ~ v1_funct_2(C_254,'#skF_1',B_253)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_253))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1844,c_1844,c_1844,c_1844,c_36])).

tff(c_2143,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_1860,c_2140])).

tff(c_2146,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1852,c_2011,c_2143])).

tff(c_1943,plain,(
    ! [C_227,B_228,A_229] :
      ( v5_relat_1(C_227,B_228)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_229,B_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1947,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1860,c_1943])).

tff(c_1899,plain,(
    ! [B_216,A_217] :
      ( r1_tarski(k2_relat_1(B_216),A_217)
      | ~ v5_relat_1(B_216,A_217)
      | ~ v1_relat_1(B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1910,plain,(
    ! [B_216] :
      ( k2_relat_1(B_216) = '#skF_1'
      | ~ v5_relat_1(B_216,'#skF_1')
      | ~ v1_relat_1(B_216) ) ),
    inference(resolution,[status(thm)],[c_1899,c_1866])).

tff(c_1950,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1947,c_1910])).

tff(c_1953,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1890,c_1950])).

tff(c_2164,plain,(
    ! [D_257,C_258,B_259,A_260] :
      ( m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(C_258,B_259)))
      | ~ r1_tarski(k2_relat_1(D_257),B_259)
      | ~ m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(C_258,A_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2166,plain,(
    ! [B_259] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_259)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_259) ) ),
    inference(resolution,[status(thm)],[c_1860,c_2164])).

tff(c_2171,plain,(
    ! [B_261] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_261))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1846,c_1953,c_2166])).

tff(c_2186,plain,(
    ! [B_261] : k1_relset_1('#skF_1',B_261,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2171,c_24])).

tff(c_2206,plain,(
    ! [B_261] : k1_relset_1('#skF_1',B_261,'#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2146,c_2186])).

tff(c_32,plain,(
    ! [C_26,B_25] :
      ( v1_funct_2(C_26,k1_xboole_0,B_25)
      | k1_relset_1(k1_xboole_0,B_25,C_26) != k1_xboole_0
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2156,plain,(
    ! [C_26,B_25] :
      ( v1_funct_2(C_26,'#skF_1',B_25)
      | k1_relset_1('#skF_1',B_25,C_26) != '#skF_1'
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_25))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1844,c_1844,c_1844,c_1844,c_32])).

tff(c_2199,plain,(
    ! [B_261] :
      ( v1_funct_2('#skF_4','#skF_1',B_261)
      | k1_relset_1('#skF_1',B_261,'#skF_4') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_2171,c_2156])).

tff(c_2223,plain,(
    ! [B_261] : v1_funct_2('#skF_4','#skF_1',B_261) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2206,c_2199])).

tff(c_1891,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_2227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2223,c_1891])).

tff(c_2228,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2534,c_2228])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.90/1.68  
% 3.90/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.68  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.16/1.68  
% 4.16/1.68  %Foreground sorts:
% 4.16/1.68  
% 4.16/1.68  
% 4.16/1.68  %Background operators:
% 4.16/1.68  
% 4.16/1.68  
% 4.16/1.68  %Foreground operators:
% 4.16/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.16/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.16/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.16/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.16/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.16/1.68  tff('#skF_2', type, '#skF_2': $i).
% 4.16/1.68  tff('#skF_3', type, '#skF_3': $i).
% 4.16/1.68  tff('#skF_1', type, '#skF_1': $i).
% 4.16/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.16/1.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.16/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.16/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.16/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.16/1.68  tff('#skF_4', type, '#skF_4': $i).
% 4.16/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.16/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.16/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.16/1.68  
% 4.16/1.72  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.16/1.72  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 4.16/1.72  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.16/1.72  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.16/1.72  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.16/1.72  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.16/1.72  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.16/1.72  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 4.16/1.72  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.16/1.72  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.16/1.72  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.16/1.72  tff(c_18, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.16/1.72  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.16/1.72  tff(c_1461, plain, (![B_145, A_146]: (v1_relat_1(B_145) | ~m1_subset_1(B_145, k1_zfmisc_1(A_146)) | ~v1_relat_1(A_146))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.16/1.72  tff(c_1464, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_1461])).
% 4.16/1.72  tff(c_1467, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1464])).
% 4.16/1.72  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.16/1.72  tff(c_1474, plain, (![B_150, A_151]: (v5_relat_1(B_150, A_151) | ~r1_tarski(k2_relat_1(B_150), A_151) | ~v1_relat_1(B_150))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.16/1.72  tff(c_1479, plain, (![B_150]: (v5_relat_1(B_150, k2_relat_1(B_150)) | ~v1_relat_1(B_150))), inference(resolution, [status(thm)], [c_6, c_1474])).
% 4.16/1.72  tff(c_1469, plain, (![C_147, B_148, A_149]: (v5_relat_1(C_147, B_148) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_149, B_148))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.16/1.72  tff(c_1473, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_1469])).
% 4.16/1.72  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.16/1.72  tff(c_1520, plain, (![B_162, A_163]: (r1_tarski(k2_relat_1(B_162), A_163) | ~v5_relat_1(B_162, A_163) | ~v1_relat_1(B_162))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.16/1.72  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.16/1.72  tff(c_1623, plain, (![A_178, A_179, B_180]: (r1_tarski(A_178, A_179) | ~r1_tarski(A_178, k2_relat_1(B_180)) | ~v5_relat_1(B_180, A_179) | ~v1_relat_1(B_180))), inference(resolution, [status(thm)], [c_1520, c_8])).
% 4.16/1.72  tff(c_1707, plain, (![B_196, A_197, B_198]: (r1_tarski(k2_relat_1(B_196), A_197) | ~v5_relat_1(B_198, A_197) | ~v1_relat_1(B_198) | ~v5_relat_1(B_196, k2_relat_1(B_198)) | ~v1_relat_1(B_196))), inference(resolution, [status(thm)], [c_16, c_1623])).
% 4.16/1.72  tff(c_1713, plain, (![B_196]: (r1_tarski(k2_relat_1(B_196), '#skF_2') | ~v1_relat_1('#skF_4') | ~v5_relat_1(B_196, k2_relat_1('#skF_4')) | ~v1_relat_1(B_196))), inference(resolution, [status(thm)], [c_1473, c_1707])).
% 4.16/1.72  tff(c_1721, plain, (![B_199]: (r1_tarski(k2_relat_1(B_199), '#skF_2') | ~v5_relat_1(B_199, k2_relat_1('#skF_4')) | ~v1_relat_1(B_199))), inference(demodulation, [status(thm), theory('equality')], [c_1467, c_1713])).
% 4.16/1.72  tff(c_1725, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1479, c_1721])).
% 4.16/1.72  tff(c_1728, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1467, c_1725])).
% 4.16/1.72  tff(c_44, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.16/1.72  tff(c_1486, plain, (![A_156, C_157, B_158]: (r1_tarski(A_156, C_157) | ~r1_tarski(B_158, C_157) | ~r1_tarski(A_156, B_158))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.16/1.72  tff(c_1495, plain, (![A_156]: (r1_tarski(A_156, '#skF_3') | ~r1_tarski(A_156, '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_1486])).
% 4.16/1.72  tff(c_1739, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1728, c_1495])).
% 4.16/1.72  tff(c_1781, plain, (![D_201, C_202, B_203, A_204]: (m1_subset_1(D_201, k1_zfmisc_1(k2_zfmisc_1(C_202, B_203))) | ~r1_tarski(k2_relat_1(D_201), B_203) | ~m1_subset_1(D_201, k1_zfmisc_1(k2_zfmisc_1(C_202, A_204))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.16/1.72  tff(c_1809, plain, (![B_206]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_206))) | ~r1_tarski(k2_relat_1('#skF_4'), B_206))), inference(resolution, [status(thm)], [c_46, c_1781])).
% 4.16/1.72  tff(c_42, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.16/1.72  tff(c_57, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_42])).
% 4.16/1.72  tff(c_48, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.16/1.72  tff(c_214, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.16/1.72  tff(c_218, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_214])).
% 4.16/1.72  tff(c_1179, plain, (![B_125, A_126, C_127]: (k1_xboole_0=B_125 | k1_relset_1(A_126, B_125, C_127)=A_126 | ~v1_funct_2(C_127, A_126, B_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.16/1.72  tff(c_1185, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_1179])).
% 4.16/1.72  tff(c_1189, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_218, c_1185])).
% 4.16/1.72  tff(c_1190, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_57, c_1189])).
% 4.16/1.72  tff(c_893, plain, (![B_109, A_110, C_111]: (k1_xboole_0=B_109 | k1_relset_1(A_110, B_109, C_111)=A_110 | ~v1_funct_2(C_111, A_110, B_109) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_110, B_109))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.16/1.72  tff(c_896, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_893])).
% 4.16/1.72  tff(c_899, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_218, c_896])).
% 4.16/1.72  tff(c_900, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_57, c_899])).
% 4.16/1.72  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.16/1.72  tff(c_86, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.16/1.72  tff(c_89, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_86])).
% 4.16/1.72  tff(c_92, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_89])).
% 4.16/1.72  tff(c_132, plain, (![B_45, A_46]: (r1_tarski(k2_relat_1(B_45), A_46) | ~v5_relat_1(B_45, A_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.16/1.72  tff(c_93, plain, (![A_36, C_37, B_38]: (r1_tarski(A_36, C_37) | ~r1_tarski(B_38, C_37) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.16/1.72  tff(c_101, plain, (![A_36, A_6]: (r1_tarski(A_36, A_6) | ~r1_tarski(A_36, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_93])).
% 4.16/1.72  tff(c_149, plain, (![B_45, A_6]: (r1_tarski(k2_relat_1(B_45), A_6) | ~v5_relat_1(B_45, k1_xboole_0) | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_132, c_101])).
% 4.16/1.72  tff(c_406, plain, (![D_90, C_91, B_92, A_93]: (m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(C_91, B_92))) | ~r1_tarski(k2_relat_1(D_90), B_92) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(C_91, A_93))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.16/1.72  tff(c_433, plain, (![B_95]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_95))) | ~r1_tarski(k2_relat_1('#skF_4'), B_95))), inference(resolution, [status(thm)], [c_46, c_406])).
% 4.16/1.72  tff(c_20, plain, (![C_16, B_15, A_14]: (v5_relat_1(C_16, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.16/1.72  tff(c_461, plain, (![B_96]: (v5_relat_1('#skF_4', B_96) | ~r1_tarski(k2_relat_1('#skF_4'), B_96))), inference(resolution, [status(thm)], [c_433, c_20])).
% 4.16/1.72  tff(c_471, plain, (![A_6]: (v5_relat_1('#skF_4', A_6) | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_149, c_461])).
% 4.16/1.72  tff(c_490, plain, (![A_6]: (v5_relat_1('#skF_4', A_6) | ~v5_relat_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_471])).
% 4.16/1.72  tff(c_545, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_490])).
% 4.16/1.72  tff(c_159, plain, (![B_51, A_52]: (v5_relat_1(B_51, A_52) | ~r1_tarski(k2_relat_1(B_51), A_52) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.16/1.72  tff(c_168, plain, (![B_51]: (v5_relat_1(B_51, k2_relat_1(B_51)) | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_6, c_159])).
% 4.16/1.72  tff(c_127, plain, (![C_42, B_43, A_44]: (v5_relat_1(C_42, B_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_43))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.16/1.72  tff(c_131, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_127])).
% 4.16/1.72  tff(c_224, plain, (![A_64, A_65, B_66]: (r1_tarski(A_64, A_65) | ~r1_tarski(A_64, k2_relat_1(B_66)) | ~v5_relat_1(B_66, A_65) | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_132, c_8])).
% 4.16/1.72  tff(c_331, plain, (![B_85, A_86, B_87]: (r1_tarski(k2_relat_1(B_85), A_86) | ~v5_relat_1(B_87, A_86) | ~v1_relat_1(B_87) | ~v5_relat_1(B_85, k2_relat_1(B_87)) | ~v1_relat_1(B_85))), inference(resolution, [status(thm)], [c_16, c_224])).
% 4.16/1.72  tff(c_337, plain, (![B_85]: (r1_tarski(k2_relat_1(B_85), '#skF_2') | ~v1_relat_1('#skF_4') | ~v5_relat_1(B_85, k2_relat_1('#skF_4')) | ~v1_relat_1(B_85))), inference(resolution, [status(thm)], [c_131, c_331])).
% 4.16/1.72  tff(c_345, plain, (![B_88]: (r1_tarski(k2_relat_1(B_88), '#skF_2') | ~v5_relat_1(B_88, k2_relat_1('#skF_4')) | ~v1_relat_1(B_88))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_337])).
% 4.16/1.72  tff(c_349, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_168, c_345])).
% 4.16/1.72  tff(c_352, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_349])).
% 4.16/1.72  tff(c_102, plain, (![A_36]: (r1_tarski(A_36, '#skF_3') | ~r1_tarski(A_36, '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_93])).
% 4.16/1.72  tff(c_366, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_352, c_102])).
% 4.16/1.72  tff(c_658, plain, (![B_104, A_105, C_106]: (k1_xboole_0=B_104 | k1_relset_1(A_105, B_104, C_106)=A_105 | ~v1_funct_2(C_106, A_105, B_104) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_105, B_104))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.16/1.72  tff(c_664, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_658])).
% 4.16/1.72  tff(c_668, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_218, c_664])).
% 4.16/1.72  tff(c_669, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_57, c_668])).
% 4.16/1.72  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.16/1.72  tff(c_40, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.16/1.72  tff(c_52, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_40])).
% 4.16/1.72  tff(c_58, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 4.16/1.72  tff(c_148, plain, (![B_45]: (r1_tarski(k2_relat_1(B_45), '#skF_3') | ~v5_relat_1(B_45, '#skF_2') | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_132, c_102])).
% 4.16/1.72  tff(c_24, plain, (![A_17, B_18, C_19]: (k1_relset_1(A_17, B_18, C_19)=k1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.16/1.72  tff(c_498, plain, (![B_97]: (k1_relset_1('#skF_1', B_97, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), B_97))), inference(resolution, [status(thm)], [c_433, c_24])).
% 4.16/1.72  tff(c_512, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_148, c_498])).
% 4.16/1.72  tff(c_529, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_131, c_512])).
% 4.16/1.72  tff(c_409, plain, (![B_92]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_92))) | ~r1_tarski(k2_relat_1('#skF_4'), B_92))), inference(resolution, [status(thm)], [c_46, c_406])).
% 4.16/1.72  tff(c_551, plain, (![B_98, C_99, A_100]: (k1_xboole_0=B_98 | v1_funct_2(C_99, A_100, B_98) | k1_relset_1(A_100, B_98, C_99)!=A_100 | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_98))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.16/1.72  tff(c_616, plain, (![B_103]: (k1_xboole_0=B_103 | v1_funct_2('#skF_4', '#skF_1', B_103) | k1_relset_1('#skF_1', B_103, '#skF_4')!='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), B_103))), inference(resolution, [status(thm)], [c_409, c_551])).
% 4.16/1.72  tff(c_630, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_148, c_616])).
% 4.16/1.72  tff(c_650, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_131, c_529, c_630])).
% 4.16/1.72  tff(c_651, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_650])).
% 4.16/1.72  tff(c_657, plain, (k1_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_651])).
% 4.16/1.72  tff(c_680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_669, c_657])).
% 4.16/1.72  tff(c_681, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_651])).
% 4.16/1.72  tff(c_30, plain, (![C_26, A_24]: (k1_xboole_0=C_26 | ~v1_funct_2(C_26, A_24, k1_xboole_0) | k1_xboole_0=A_24 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.16/1.72  tff(c_453, plain, (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', '#skF_1', k1_xboole_0) | k1_xboole_0='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), k1_xboole_0)), inference(resolution, [status(thm)], [c_433, c_30])).
% 4.16/1.72  tff(c_589, plain, (~r1_tarski(k2_relat_1('#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_453])).
% 4.16/1.72  tff(c_684, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_681, c_589])).
% 4.16/1.72  tff(c_703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_366, c_684])).
% 4.16/1.72  tff(c_705, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_453])).
% 4.16/1.72  tff(c_457, plain, (![B_95]: (v5_relat_1('#skF_4', B_95) | ~r1_tarski(k2_relat_1('#skF_4'), B_95))), inference(resolution, [status(thm)], [c_433, c_20])).
% 4.16/1.72  tff(c_755, plain, (v5_relat_1('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_705, c_457])).
% 4.16/1.72  tff(c_774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_545, c_755])).
% 4.16/1.72  tff(c_781, plain, (![A_108]: (v5_relat_1('#skF_4', A_108))), inference(splitRight, [status(thm)], [c_490])).
% 4.16/1.72  tff(c_59, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.16/1.72  tff(c_70, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_59])).
% 4.16/1.72  tff(c_151, plain, (![B_45]: (k2_relat_1(B_45)=k1_xboole_0 | ~v5_relat_1(B_45, k1_xboole_0) | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_132, c_70])).
% 4.16/1.72  tff(c_801, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_781, c_151])).
% 4.16/1.72  tff(c_819, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_92, c_801])).
% 4.16/1.72  tff(c_822, plain, (![B_92]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_92))) | ~r1_tarski(k1_xboole_0, B_92))), inference(demodulation, [status(thm), theory('equality')], [c_819, c_409])).
% 4.16/1.72  tff(c_919, plain, (![B_112]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_112))))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_822])).
% 4.16/1.72  tff(c_931, plain, (![B_112]: (k1_relset_1('#skF_1', B_112, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_919, c_24])).
% 4.16/1.72  tff(c_947, plain, (![B_112]: (k1_relset_1('#skF_1', B_112, '#skF_4')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_900, c_931])).
% 4.16/1.72  tff(c_833, plain, (![B_92]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_92))))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_822])).
% 4.16/1.72  tff(c_965, plain, (![B_114, C_115, A_116]: (k1_xboole_0=B_114 | v1_funct_2(C_115, A_116, B_114) | k1_relset_1(A_116, B_114, C_115)!=A_116 | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_116, B_114))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.16/1.72  tff(c_968, plain, (![B_92]: (k1_xboole_0=B_92 | v1_funct_2('#skF_4', '#skF_1', B_92) | k1_relset_1('#skF_1', B_92, '#skF_4')!='#skF_1')), inference(resolution, [status(thm)], [c_833, c_965])).
% 4.16/1.72  tff(c_972, plain, (![B_117]: (k1_xboole_0=B_117 | v1_funct_2('#skF_4', '#skF_1', B_117))), inference(demodulation, [status(thm), theory('equality')], [c_947, c_968])).
% 4.16/1.72  tff(c_981, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_972, c_58])).
% 4.16/1.72  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.16/1.72  tff(c_380, plain, (k2_relat_1('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_366, c_2])).
% 4.16/1.72  tff(c_405, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_380])).
% 4.16/1.72  tff(c_824, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_819, c_405])).
% 4.16/1.72  tff(c_985, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_981, c_824])).
% 4.16/1.72  tff(c_1005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_985])).
% 4.16/1.72  tff(c_1006, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_380])).
% 4.16/1.72  tff(c_368, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_352, c_2])).
% 4.16/1.72  tff(c_381, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_368])).
% 4.16/1.72  tff(c_1009, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1006, c_381])).
% 4.16/1.72  tff(c_1015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1009])).
% 4.16/1.72  tff(c_1016, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_368])).
% 4.16/1.72  tff(c_1084, plain, (![D_118, C_119, B_120, A_121]: (m1_subset_1(D_118, k1_zfmisc_1(k2_zfmisc_1(C_119, B_120))) | ~r1_tarski(k2_relat_1(D_118), B_120) | ~m1_subset_1(D_118, k1_zfmisc_1(k2_zfmisc_1(C_119, A_121))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.16/1.72  tff(c_1086, plain, (![B_120]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_120))) | ~r1_tarski(k2_relat_1('#skF_4'), B_120))), inference(resolution, [status(thm)], [c_46, c_1084])).
% 4.16/1.72  tff(c_1126, plain, (![B_123]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_123))) | ~r1_tarski('#skF_2', B_123))), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_1086])).
% 4.16/1.72  tff(c_1148, plain, (![B_123]: (k1_relset_1('#skF_1', B_123, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_123))), inference(resolution, [status(thm)], [c_1126, c_24])).
% 4.16/1.72  tff(c_1224, plain, (![B_129]: (k1_relset_1('#skF_1', B_129, '#skF_4')='#skF_1' | ~r1_tarski('#skF_2', B_129))), inference(demodulation, [status(thm), theory('equality')], [c_1190, c_1148])).
% 4.16/1.72  tff(c_1234, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_44, c_1224])).
% 4.16/1.72  tff(c_1088, plain, (![B_120]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_120))) | ~r1_tarski('#skF_2', B_120))), inference(demodulation, [status(thm), theory('equality')], [c_1016, c_1086])).
% 4.16/1.72  tff(c_1258, plain, (![B_132, C_133, A_134]: (k1_xboole_0=B_132 | v1_funct_2(C_133, A_134, B_132) | k1_relset_1(A_134, B_132, C_133)!=A_134 | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_134, B_132))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.16/1.72  tff(c_1404, plain, (![B_141]: (k1_xboole_0=B_141 | v1_funct_2('#skF_4', '#skF_1', B_141) | k1_relset_1('#skF_1', B_141, '#skF_4')!='#skF_1' | ~r1_tarski('#skF_2', B_141))), inference(resolution, [status(thm)], [c_1088, c_1258])).
% 4.16/1.72  tff(c_1407, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1404, c_58])).
% 4.16/1.72  tff(c_1410, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1234, c_1407])).
% 4.16/1.72  tff(c_14, plain, (![B_11, A_10]: (v5_relat_1(B_11, A_10) | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.16/1.72  tff(c_1052, plain, (![A_10]: (v5_relat_1('#skF_4', A_10) | ~r1_tarski('#skF_2', A_10) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1016, c_14])).
% 4.16/1.72  tff(c_1089, plain, (![A_122]: (v5_relat_1('#skF_4', A_122) | ~r1_tarski('#skF_2', A_122))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1052])).
% 4.16/1.72  tff(c_1108, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_1089, c_151])).
% 4.16/1.72  tff(c_1124, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_1016, c_1108])).
% 4.16/1.72  tff(c_1125, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_57, c_1124])).
% 4.16/1.72  tff(c_1414, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1410, c_1125])).
% 4.16/1.72  tff(c_1432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_1414])).
% 4.16/1.72  tff(c_1433, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_52])).
% 4.16/1.72  tff(c_1830, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1809, c_1433])).
% 4.16/1.72  tff(c_1843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1739, c_1830])).
% 4.16/1.72  tff(c_1844, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_42])).
% 4.16/1.72  tff(c_1846, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1844, c_10])).
% 4.16/1.72  tff(c_1845, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_42])).
% 4.16/1.72  tff(c_1851, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1844, c_1845])).
% 4.16/1.72  tff(c_1860, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1851, c_46])).
% 4.16/1.72  tff(c_1884, plain, (![B_211, A_212]: (v1_relat_1(B_211) | ~m1_subset_1(B_211, k1_zfmisc_1(A_212)) | ~v1_relat_1(A_212))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.16/1.72  tff(c_1887, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1860, c_1884])).
% 4.16/1.72  tff(c_1890, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1887])).
% 4.16/1.72  tff(c_2230, plain, (![C_263, B_264, A_265]: (v5_relat_1(C_263, B_264) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_265, B_264))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.16/1.72  tff(c_2234, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1860, c_2230])).
% 4.16/1.72  tff(c_2260, plain, (![B_274, A_275]: (r1_tarski(k2_relat_1(B_274), A_275) | ~v5_relat_1(B_274, A_275) | ~v1_relat_1(B_274))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.16/1.72  tff(c_1861, plain, (![B_208, A_209]: (B_208=A_209 | ~r1_tarski(B_208, A_209) | ~r1_tarski(A_209, B_208))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.16/1.72  tff(c_1866, plain, (![A_6]: (A_6='#skF_1' | ~r1_tarski(A_6, '#skF_1'))), inference(resolution, [status(thm)], [c_1846, c_1861])).
% 4.16/1.72  tff(c_2280, plain, (![B_276]: (k2_relat_1(B_276)='#skF_1' | ~v5_relat_1(B_276, '#skF_1') | ~v1_relat_1(B_276))), inference(resolution, [status(thm)], [c_2260, c_1866])).
% 4.16/1.72  tff(c_2283, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2234, c_2280])).
% 4.16/1.72  tff(c_2286, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1890, c_2283])).
% 4.16/1.72  tff(c_2529, plain, (![D_312, C_313, B_314, A_315]: (m1_subset_1(D_312, k1_zfmisc_1(k2_zfmisc_1(C_313, B_314))) | ~r1_tarski(k2_relat_1(D_312), B_314) | ~m1_subset_1(D_312, k1_zfmisc_1(k2_zfmisc_1(C_313, A_315))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.16/1.72  tff(c_2531, plain, (![B_314]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_314))) | ~r1_tarski(k2_relat_1('#skF_4'), B_314))), inference(resolution, [status(thm)], [c_1860, c_2529])).
% 4.16/1.72  tff(c_2534, plain, (![B_314]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_314))))), inference(demodulation, [status(thm), theory('equality')], [c_1846, c_2286, c_2531])).
% 4.16/1.72  tff(c_1852, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1851, c_48])).
% 4.16/1.72  tff(c_2007, plain, (![A_233, B_234, C_235]: (k1_relset_1(A_233, B_234, C_235)=k1_relat_1(C_235) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.16/1.72  tff(c_2011, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1860, c_2007])).
% 4.16/1.72  tff(c_36, plain, (![B_25, C_26]: (k1_relset_1(k1_xboole_0, B_25, C_26)=k1_xboole_0 | ~v1_funct_2(C_26, k1_xboole_0, B_25) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_25))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.16/1.72  tff(c_2140, plain, (![B_253, C_254]: (k1_relset_1('#skF_1', B_253, C_254)='#skF_1' | ~v1_funct_2(C_254, '#skF_1', B_253) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_253))))), inference(demodulation, [status(thm), theory('equality')], [c_1844, c_1844, c_1844, c_1844, c_36])).
% 4.16/1.72  tff(c_2143, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_1860, c_2140])).
% 4.16/1.72  tff(c_2146, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1852, c_2011, c_2143])).
% 4.16/1.72  tff(c_1943, plain, (![C_227, B_228, A_229]: (v5_relat_1(C_227, B_228) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_229, B_228))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.16/1.72  tff(c_1947, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1860, c_1943])).
% 4.16/1.72  tff(c_1899, plain, (![B_216, A_217]: (r1_tarski(k2_relat_1(B_216), A_217) | ~v5_relat_1(B_216, A_217) | ~v1_relat_1(B_216))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.16/1.72  tff(c_1910, plain, (![B_216]: (k2_relat_1(B_216)='#skF_1' | ~v5_relat_1(B_216, '#skF_1') | ~v1_relat_1(B_216))), inference(resolution, [status(thm)], [c_1899, c_1866])).
% 4.16/1.72  tff(c_1950, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1947, c_1910])).
% 4.16/1.72  tff(c_1953, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1890, c_1950])).
% 4.16/1.72  tff(c_2164, plain, (![D_257, C_258, B_259, A_260]: (m1_subset_1(D_257, k1_zfmisc_1(k2_zfmisc_1(C_258, B_259))) | ~r1_tarski(k2_relat_1(D_257), B_259) | ~m1_subset_1(D_257, k1_zfmisc_1(k2_zfmisc_1(C_258, A_260))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.16/1.72  tff(c_2166, plain, (![B_259]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_259))) | ~r1_tarski(k2_relat_1('#skF_4'), B_259))), inference(resolution, [status(thm)], [c_1860, c_2164])).
% 4.16/1.72  tff(c_2171, plain, (![B_261]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_261))))), inference(demodulation, [status(thm), theory('equality')], [c_1846, c_1953, c_2166])).
% 4.16/1.72  tff(c_2186, plain, (![B_261]: (k1_relset_1('#skF_1', B_261, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2171, c_24])).
% 4.16/1.72  tff(c_2206, plain, (![B_261]: (k1_relset_1('#skF_1', B_261, '#skF_4')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2146, c_2186])).
% 4.16/1.72  tff(c_32, plain, (![C_26, B_25]: (v1_funct_2(C_26, k1_xboole_0, B_25) | k1_relset_1(k1_xboole_0, B_25, C_26)!=k1_xboole_0 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_25))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.16/1.72  tff(c_2156, plain, (![C_26, B_25]: (v1_funct_2(C_26, '#skF_1', B_25) | k1_relset_1('#skF_1', B_25, C_26)!='#skF_1' | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_25))))), inference(demodulation, [status(thm), theory('equality')], [c_1844, c_1844, c_1844, c_1844, c_32])).
% 4.16/1.72  tff(c_2199, plain, (![B_261]: (v1_funct_2('#skF_4', '#skF_1', B_261) | k1_relset_1('#skF_1', B_261, '#skF_4')!='#skF_1')), inference(resolution, [status(thm)], [c_2171, c_2156])).
% 4.16/1.72  tff(c_2223, plain, (![B_261]: (v1_funct_2('#skF_4', '#skF_1', B_261))), inference(demodulation, [status(thm), theory('equality')], [c_2206, c_2199])).
% 4.16/1.72  tff(c_1891, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 4.16/1.72  tff(c_2227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2223, c_1891])).
% 4.16/1.72  tff(c_2228, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_52])).
% 4.16/1.72  tff(c_2538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2534, c_2228])).
% 4.16/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.72  
% 4.16/1.72  Inference rules
% 4.16/1.72  ----------------------
% 4.16/1.72  #Ref     : 0
% 4.16/1.72  #Sup     : 472
% 4.16/1.72  #Fact    : 0
% 4.16/1.72  #Define  : 0
% 4.16/1.72  #Split   : 15
% 4.16/1.72  #Chain   : 0
% 4.16/1.72  #Close   : 0
% 4.16/1.72  
% 4.16/1.72  Ordering : KBO
% 4.16/1.72  
% 4.16/1.72  Simplification rules
% 4.16/1.72  ----------------------
% 4.16/1.72  #Subsume      : 110
% 4.16/1.72  #Demod        : 516
% 4.16/1.72  #Tautology    : 201
% 4.16/1.72  #SimpNegUnit  : 13
% 4.16/1.72  #BackRed      : 89
% 4.16/1.72  
% 4.16/1.72  #Partial instantiations: 0
% 4.16/1.72  #Strategies tried      : 1
% 4.16/1.72  
% 4.16/1.72  Timing (in seconds)
% 4.16/1.72  ----------------------
% 4.16/1.73  Preprocessing        : 0.32
% 4.16/1.73  Parsing              : 0.17
% 4.16/1.73  CNF conversion       : 0.02
% 4.16/1.73  Main loop            : 0.58
% 4.16/1.73  Inferencing          : 0.20
% 4.16/1.73  Reduction            : 0.19
% 4.16/1.73  Demodulation         : 0.13
% 4.16/1.73  BG Simplification    : 0.02
% 4.16/1.73  Subsumption          : 0.11
% 4.16/1.73  Abstraction          : 0.03
% 4.16/1.73  MUC search           : 0.00
% 4.16/1.73  Cooper               : 0.00
% 4.16/1.73  Total                : 0.98
% 4.16/1.73  Index Insertion      : 0.00
% 4.16/1.73  Index Deletion       : 0.00
% 4.16/1.73  Index Matching       : 0.00
% 4.16/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
