%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:50 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 556 expanded)
%              Number of leaves         :   23 ( 191 expanded)
%              Depth                    :   16
%              Number of atoms          :  191 (1353 expanded)
%              Number of equality atoms :   61 ( 488 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_69,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_14,plain,(
    ! [A_6] :
      ( r1_tarski(A_6,k2_zfmisc_1(k1_relat_1(A_6),k2_relat_1(A_6)))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_601,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_relset_1(A_106,B_107,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_837,plain,(
    ! [A_138,B_139,A_140] :
      ( k1_relset_1(A_138,B_139,A_140) = k1_relat_1(A_140)
      | ~ r1_tarski(A_140,k2_zfmisc_1(A_138,B_139)) ) ),
    inference(resolution,[status(thm)],[c_12,c_601])).

tff(c_853,plain,(
    ! [A_6] :
      ( k1_relset_1(k1_relat_1(A_6),k2_relat_1(A_6),A_6) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_837])).

tff(c_854,plain,(
    ! [B_141,C_142,A_143] :
      ( k1_xboole_0 = B_141
      | v1_funct_2(C_142,A_143,B_141)
      | k1_relset_1(A_143,B_141,C_142) != A_143
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_143,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1206,plain,(
    ! [B_178,A_179,A_180] :
      ( k1_xboole_0 = B_178
      | v1_funct_2(A_179,A_180,B_178)
      | k1_relset_1(A_180,B_178,A_179) != A_180
      | ~ r1_tarski(A_179,k2_zfmisc_1(A_180,B_178)) ) ),
    inference(resolution,[status(thm)],[c_12,c_854])).

tff(c_1669,plain,(
    ! [A_211] :
      ( k2_relat_1(A_211) = k1_xboole_0
      | v1_funct_2(A_211,k1_relat_1(A_211),k2_relat_1(A_211))
      | k1_relset_1(k1_relat_1(A_211),k2_relat_1(A_211),A_211) != k1_relat_1(A_211)
      | ~ v1_relat_1(A_211) ) ),
    inference(resolution,[status(thm)],[c_14,c_1206])).

tff(c_34,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32])).

tff(c_84,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_1676,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1669,c_84])).

tff(c_1688,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1676])).

tff(c_1691,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1688])).

tff(c_1694,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_1691])).

tff(c_1698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1694])).

tff(c_1699,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1688])).

tff(c_1711,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1699,c_14])).

tff(c_1719,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6,c_1711])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1733,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1719,c_2])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_114,plain,(
    ! [A_37,B_38,C_39] :
      ( m1_subset_1(k1_relset_1(A_37,B_38,C_39),k1_zfmisc_1(A_37))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_158,plain,(
    ! [A_46,B_47,C_48] :
      ( r1_tarski(k1_relset_1(A_46,B_47,C_48),A_46)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(resolution,[status(thm)],[c_114,c_10])).

tff(c_168,plain,(
    ! [B_3,C_48] :
      ( r1_tarski(k1_relset_1(k1_xboole_0,B_3,C_48),k1_xboole_0)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_158])).

tff(c_16,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k1_relset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_166,plain,(
    ! [A_2,C_48] :
      ( r1_tarski(k1_relset_1(A_2,k1_xboole_0,C_48),A_2)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_158])).

tff(c_20,plain,(
    ! [A_13] :
      ( v1_funct_2(k1_xboole_0,A_13,k1_xboole_0)
      | k1_xboole_0 = A_13
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_13,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_41,plain,(
    ! [A_13] :
      ( v1_funct_2(k1_xboole_0,A_13,k1_xboole_0)
      | k1_xboole_0 = A_13
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20])).

tff(c_85,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_89,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_85])).

tff(c_269,plain,(
    ! [A_64,B_65,A_66] :
      ( r1_tarski(k1_relset_1(A_64,B_65,A_66),A_64)
      | ~ r1_tarski(A_66,k2_zfmisc_1(A_64,B_65)) ) ),
    inference(resolution,[status(thm)],[c_12,c_158])).

tff(c_218,plain,(
    ! [B_55,C_56] :
      ( r1_tarski(k1_relset_1(k1_xboole_0,B_55,C_56),k1_xboole_0)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_158])).

tff(c_251,plain,(
    ! [B_60,C_61] :
      ( k1_relset_1(k1_xboole_0,B_60,C_61) = k1_xboole_0
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_218,c_2])).

tff(c_260,plain,(
    ! [B_60,A_4] :
      ( k1_relset_1(k1_xboole_0,B_60,A_4) = k1_xboole_0
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_251])).

tff(c_272,plain,(
    ! [B_60,B_65,A_66] :
      ( k1_relset_1(k1_xboole_0,B_60,k1_relset_1(k1_xboole_0,B_65,A_66)) = k1_xboole_0
      | ~ r1_tarski(A_66,k2_zfmisc_1(k1_xboole_0,B_65)) ) ),
    inference(resolution,[status(thm)],[c_269,c_260])).

tff(c_299,plain,(
    ! [B_67,B_68,A_69] :
      ( k1_relset_1(k1_xboole_0,B_67,k1_relset_1(k1_xboole_0,B_68,A_69)) = k1_xboole_0
      | ~ r1_tarski(A_69,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_272])).

tff(c_170,plain,(
    ! [A_46,B_47,A_4] :
      ( r1_tarski(k1_relset_1(A_46,B_47,A_4),A_46)
      | ~ r1_tarski(A_4,k2_zfmisc_1(A_46,B_47)) ) ),
    inference(resolution,[status(thm)],[c_12,c_158])).

tff(c_308,plain,(
    ! [B_68,A_69,B_67] :
      ( r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relset_1(k1_xboole_0,B_68,A_69),k2_zfmisc_1(k1_xboole_0,B_67))
      | ~ r1_tarski(A_69,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_170])).

tff(c_326,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_relset_1(k1_xboole_0,B_68,A_69),k1_xboole_0)
      | ~ r1_tarski(A_69,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_308])).

tff(c_333,plain,(
    ! [B_70,A_71] :
      ( ~ r1_tarski(k1_relset_1(k1_xboole_0,B_70,A_71),k1_xboole_0)
      | ~ r1_tarski(A_71,k1_xboole_0) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_326])).

tff(c_365,plain,(
    ! [C_73] :
      ( ~ r1_tarski(C_73,k1_xboole_0)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_166,c_333])).

tff(c_369,plain,(
    ! [B_8,C_9] :
      ( ~ r1_tarski(k1_relset_1(k1_xboole_0,B_8,C_9),k1_xboole_0)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_8))) ) ),
    inference(resolution,[status(thm)],[c_16,c_365])).

tff(c_409,plain,(
    ! [B_79,C_80] :
      ( ~ r1_tarski(k1_relset_1(k1_xboole_0,B_79,C_80),k1_xboole_0)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_369])).

tff(c_428,plain,(
    ! [C_81] : ~ m1_subset_1(C_81,k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_168,c_409])).

tff(c_439,plain,(
    ! [A_4] : ~ r1_tarski(A_4,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_428])).

tff(c_90,plain,(
    ! [A_26,B_27,C_28] :
      ( k1_relset_1(A_26,B_27,C_28) = k1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_135,plain,(
    ! [A_42,B_43,A_44] :
      ( k1_relset_1(A_42,B_43,A_44) = k1_relat_1(A_44)
      | ~ r1_tarski(A_44,k2_zfmisc_1(A_42,B_43)) ) ),
    inference(resolution,[status(thm)],[c_12,c_90])).

tff(c_145,plain,(
    ! [A_6] :
      ( k1_relset_1(k1_relat_1(A_6),k2_relat_1(A_6),A_6) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_14,c_135])).

tff(c_377,plain,(
    ! [B_74,C_75,A_76] :
      ( k1_xboole_0 = B_74
      | v1_funct_2(C_75,A_76,B_74)
      | k1_relset_1(A_76,B_74,C_75) != A_76
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_448,plain,(
    ! [B_85,A_86,A_87] :
      ( k1_xboole_0 = B_85
      | v1_funct_2(A_86,A_87,B_85)
      | k1_relset_1(A_87,B_85,A_86) != A_87
      | ~ r1_tarski(A_86,k2_zfmisc_1(A_87,B_85)) ) ),
    inference(resolution,[status(thm)],[c_12,c_377])).

tff(c_551,plain,(
    ! [A_104] :
      ( k2_relat_1(A_104) = k1_xboole_0
      | v1_funct_2(A_104,k1_relat_1(A_104),k2_relat_1(A_104))
      | k1_relset_1(k1_relat_1(A_104),k2_relat_1(A_104),A_104) != k1_relat_1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(resolution,[status(thm)],[c_14,c_448])).

tff(c_554,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_551,c_84])).

tff(c_557,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_554])).

tff(c_558,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_557])).

tff(c_561,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_558])).

tff(c_565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_561])).

tff(c_566,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_557])).

tff(c_578,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_14])).

tff(c_586,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6,c_578])).

tff(c_588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_586])).

tff(c_590,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_620,plain,(
    ! [A_111,C_112] :
      ( k1_relset_1(A_111,k1_xboole_0,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_601])).

tff(c_626,plain,(
    ! [A_111] : k1_relset_1(A_111,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_590,c_620])).

tff(c_640,plain,(
    ! [A_116,B_117,C_118] :
      ( m1_subset_1(k1_relset_1(A_116,B_117,C_118),k1_zfmisc_1(A_116))
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_653,plain,(
    ! [A_111] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_111))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_111,k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_640])).

tff(c_660,plain,(
    ! [A_119] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_119)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_6,c_653])).

tff(c_674,plain,(
    ! [A_120] : r1_tarski(k1_relat_1(k1_xboole_0),A_120) ),
    inference(resolution,[status(thm)],[c_660,c_10])).

tff(c_683,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_674,c_2])).

tff(c_659,plain,(
    ! [A_111] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_111)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_6,c_653])).

tff(c_709,plain,(
    ! [A_122] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_122)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_659])).

tff(c_18,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_relset_1(A_10,B_11,C_12) = k1_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_716,plain,(
    ! [A_10,B_11] : k1_relset_1(A_10,B_11,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_709,c_18])).

tff(c_723,plain,(
    ! [A_10,B_11] : k1_relset_1(A_10,B_11,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_716])).

tff(c_685,plain,(
    ! [A_111] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_111)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_659])).

tff(c_24,plain,(
    ! [C_15,B_14] :
      ( v1_funct_2(C_15,k1_xboole_0,B_14)
      | k1_relset_1(k1_xboole_0,B_14,C_15) != k1_xboole_0
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_726,plain,(
    ! [C_123,B_124] :
      ( v1_funct_2(C_123,k1_xboole_0,B_124)
      | k1_relset_1(k1_xboole_0,B_124,C_123) != k1_xboole_0
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_24])).

tff(c_736,plain,(
    ! [B_124] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_124)
      | k1_relset_1(k1_xboole_0,B_124,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_685,c_726])).

tff(c_794,plain,(
    ! [B_124] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_736])).

tff(c_1758,plain,(
    ! [B_124] : v1_funct_2('#skF_1','#skF_1',B_124) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1733,c_1733,c_794])).

tff(c_1764,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1733,c_1733,c_683])).

tff(c_1701,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1699,c_84])).

tff(c_1829,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1764,c_1733,c_1701])).

tff(c_1927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1758,c_1829])).

tff(c_1928,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1933,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_12,c_1928])).

tff(c_1936,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_1933])).

tff(c_1940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1936])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:13:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.67  
% 3.53/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.67  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.53/1.67  
% 3.53/1.67  %Foreground sorts:
% 3.53/1.67  
% 3.53/1.67  
% 3.53/1.67  %Background operators:
% 3.53/1.67  
% 3.53/1.67  
% 3.53/1.67  %Foreground operators:
% 3.53/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.53/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.53/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.53/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.67  
% 3.80/1.69  tff(f_80, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.80/1.69  tff(f_43, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.80/1.69  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.80/1.69  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.80/1.69  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.80/1.69  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.80/1.69  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 3.80/1.69  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.80/1.69  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.80/1.69  tff(c_14, plain, (![A_6]: (r1_tarski(A_6, k2_zfmisc_1(k1_relat_1(A_6), k2_relat_1(A_6))) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.80/1.69  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.80/1.69  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.80/1.69  tff(c_601, plain, (![A_106, B_107, C_108]: (k1_relset_1(A_106, B_107, C_108)=k1_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.80/1.69  tff(c_837, plain, (![A_138, B_139, A_140]: (k1_relset_1(A_138, B_139, A_140)=k1_relat_1(A_140) | ~r1_tarski(A_140, k2_zfmisc_1(A_138, B_139)))), inference(resolution, [status(thm)], [c_12, c_601])).
% 3.80/1.69  tff(c_853, plain, (![A_6]: (k1_relset_1(k1_relat_1(A_6), k2_relat_1(A_6), A_6)=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_14, c_837])).
% 3.80/1.69  tff(c_854, plain, (![B_141, C_142, A_143]: (k1_xboole_0=B_141 | v1_funct_2(C_142, A_143, B_141) | k1_relset_1(A_143, B_141, C_142)!=A_143 | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_143, B_141))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.80/1.69  tff(c_1206, plain, (![B_178, A_179, A_180]: (k1_xboole_0=B_178 | v1_funct_2(A_179, A_180, B_178) | k1_relset_1(A_180, B_178, A_179)!=A_180 | ~r1_tarski(A_179, k2_zfmisc_1(A_180, B_178)))), inference(resolution, [status(thm)], [c_12, c_854])).
% 3.80/1.69  tff(c_1669, plain, (![A_211]: (k2_relat_1(A_211)=k1_xboole_0 | v1_funct_2(A_211, k1_relat_1(A_211), k2_relat_1(A_211)) | k1_relset_1(k1_relat_1(A_211), k2_relat_1(A_211), A_211)!=k1_relat_1(A_211) | ~v1_relat_1(A_211))), inference(resolution, [status(thm)], [c_14, c_1206])).
% 3.80/1.69  tff(c_34, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.80/1.69  tff(c_32, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.80/1.69  tff(c_38, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32])).
% 3.80/1.69  tff(c_84, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_38])).
% 3.80/1.69  tff(c_1676, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1669, c_84])).
% 3.80/1.69  tff(c_1688, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1676])).
% 3.80/1.69  tff(c_1691, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1688])).
% 3.80/1.69  tff(c_1694, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_853, c_1691])).
% 3.80/1.69  tff(c_1698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1694])).
% 3.80/1.69  tff(c_1699, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1688])).
% 3.80/1.69  tff(c_1711, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1699, c_14])).
% 3.80/1.69  tff(c_1719, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6, c_1711])).
% 3.80/1.69  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.80/1.69  tff(c_1733, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1719, c_2])).
% 3.80/1.69  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.80/1.69  tff(c_114, plain, (![A_37, B_38, C_39]: (m1_subset_1(k1_relset_1(A_37, B_38, C_39), k1_zfmisc_1(A_37)) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.80/1.69  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.80/1.69  tff(c_158, plain, (![A_46, B_47, C_48]: (r1_tarski(k1_relset_1(A_46, B_47, C_48), A_46) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(resolution, [status(thm)], [c_114, c_10])).
% 3.80/1.69  tff(c_168, plain, (![B_3, C_48]: (r1_tarski(k1_relset_1(k1_xboole_0, B_3, C_48), k1_xboole_0) | ~m1_subset_1(C_48, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_158])).
% 3.80/1.69  tff(c_16, plain, (![A_7, B_8, C_9]: (m1_subset_1(k1_relset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.80/1.69  tff(c_166, plain, (![A_2, C_48]: (r1_tarski(k1_relset_1(A_2, k1_xboole_0, C_48), A_2) | ~m1_subset_1(C_48, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_158])).
% 3.80/1.69  tff(c_20, plain, (![A_13]: (v1_funct_2(k1_xboole_0, A_13, k1_xboole_0) | k1_xboole_0=A_13 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_13, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.80/1.69  tff(c_41, plain, (![A_13]: (v1_funct_2(k1_xboole_0, A_13, k1_xboole_0) | k1_xboole_0=A_13 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_20])).
% 3.80/1.69  tff(c_85, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_41])).
% 3.80/1.69  tff(c_89, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_85])).
% 3.80/1.69  tff(c_269, plain, (![A_64, B_65, A_66]: (r1_tarski(k1_relset_1(A_64, B_65, A_66), A_64) | ~r1_tarski(A_66, k2_zfmisc_1(A_64, B_65)))), inference(resolution, [status(thm)], [c_12, c_158])).
% 3.80/1.69  tff(c_218, plain, (![B_55, C_56]: (r1_tarski(k1_relset_1(k1_xboole_0, B_55, C_56), k1_xboole_0) | ~m1_subset_1(C_56, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_158])).
% 3.80/1.69  tff(c_251, plain, (![B_60, C_61]: (k1_relset_1(k1_xboole_0, B_60, C_61)=k1_xboole_0 | ~m1_subset_1(C_61, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_218, c_2])).
% 3.80/1.69  tff(c_260, plain, (![B_60, A_4]: (k1_relset_1(k1_xboole_0, B_60, A_4)=k1_xboole_0 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_251])).
% 3.80/1.69  tff(c_272, plain, (![B_60, B_65, A_66]: (k1_relset_1(k1_xboole_0, B_60, k1_relset_1(k1_xboole_0, B_65, A_66))=k1_xboole_0 | ~r1_tarski(A_66, k2_zfmisc_1(k1_xboole_0, B_65)))), inference(resolution, [status(thm)], [c_269, c_260])).
% 3.80/1.69  tff(c_299, plain, (![B_67, B_68, A_69]: (k1_relset_1(k1_xboole_0, B_67, k1_relset_1(k1_xboole_0, B_68, A_69))=k1_xboole_0 | ~r1_tarski(A_69, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_272])).
% 3.80/1.69  tff(c_170, plain, (![A_46, B_47, A_4]: (r1_tarski(k1_relset_1(A_46, B_47, A_4), A_46) | ~r1_tarski(A_4, k2_zfmisc_1(A_46, B_47)))), inference(resolution, [status(thm)], [c_12, c_158])).
% 3.80/1.69  tff(c_308, plain, (![B_68, A_69, B_67]: (r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relset_1(k1_xboole_0, B_68, A_69), k2_zfmisc_1(k1_xboole_0, B_67)) | ~r1_tarski(A_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_299, c_170])).
% 3.80/1.69  tff(c_326, plain, (![B_68, A_69]: (r1_tarski(k1_xboole_0, k1_xboole_0) | ~r1_tarski(k1_relset_1(k1_xboole_0, B_68, A_69), k1_xboole_0) | ~r1_tarski(A_69, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_308])).
% 3.80/1.69  tff(c_333, plain, (![B_70, A_71]: (~r1_tarski(k1_relset_1(k1_xboole_0, B_70, A_71), k1_xboole_0) | ~r1_tarski(A_71, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_89, c_326])).
% 3.80/1.69  tff(c_365, plain, (![C_73]: (~r1_tarski(C_73, k1_xboole_0) | ~m1_subset_1(C_73, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_166, c_333])).
% 3.80/1.69  tff(c_369, plain, (![B_8, C_9]: (~r1_tarski(k1_relset_1(k1_xboole_0, B_8, C_9), k1_xboole_0) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_8))))), inference(resolution, [status(thm)], [c_16, c_365])).
% 3.80/1.69  tff(c_409, plain, (![B_79, C_80]: (~r1_tarski(k1_relset_1(k1_xboole_0, B_79, C_80), k1_xboole_0) | ~m1_subset_1(C_80, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_369])).
% 3.80/1.69  tff(c_428, plain, (![C_81]: (~m1_subset_1(C_81, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_168, c_409])).
% 3.80/1.69  tff(c_439, plain, (![A_4]: (~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_428])).
% 3.80/1.69  tff(c_90, plain, (![A_26, B_27, C_28]: (k1_relset_1(A_26, B_27, C_28)=k1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.80/1.69  tff(c_135, plain, (![A_42, B_43, A_44]: (k1_relset_1(A_42, B_43, A_44)=k1_relat_1(A_44) | ~r1_tarski(A_44, k2_zfmisc_1(A_42, B_43)))), inference(resolution, [status(thm)], [c_12, c_90])).
% 3.80/1.69  tff(c_145, plain, (![A_6]: (k1_relset_1(k1_relat_1(A_6), k2_relat_1(A_6), A_6)=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_14, c_135])).
% 3.80/1.69  tff(c_377, plain, (![B_74, C_75, A_76]: (k1_xboole_0=B_74 | v1_funct_2(C_75, A_76, B_74) | k1_relset_1(A_76, B_74, C_75)!=A_76 | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_74))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.80/1.69  tff(c_448, plain, (![B_85, A_86, A_87]: (k1_xboole_0=B_85 | v1_funct_2(A_86, A_87, B_85) | k1_relset_1(A_87, B_85, A_86)!=A_87 | ~r1_tarski(A_86, k2_zfmisc_1(A_87, B_85)))), inference(resolution, [status(thm)], [c_12, c_377])).
% 3.80/1.69  tff(c_551, plain, (![A_104]: (k2_relat_1(A_104)=k1_xboole_0 | v1_funct_2(A_104, k1_relat_1(A_104), k2_relat_1(A_104)) | k1_relset_1(k1_relat_1(A_104), k2_relat_1(A_104), A_104)!=k1_relat_1(A_104) | ~v1_relat_1(A_104))), inference(resolution, [status(thm)], [c_14, c_448])).
% 3.80/1.69  tff(c_554, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_551, c_84])).
% 3.80/1.69  tff(c_557, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_554])).
% 3.80/1.69  tff(c_558, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_557])).
% 3.80/1.69  tff(c_561, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_145, c_558])).
% 3.80/1.69  tff(c_565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_561])).
% 3.80/1.69  tff(c_566, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_557])).
% 3.80/1.69  tff(c_578, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_566, c_14])).
% 3.80/1.69  tff(c_586, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6, c_578])).
% 3.80/1.69  tff(c_588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_439, c_586])).
% 3.80/1.69  tff(c_590, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_41])).
% 3.80/1.69  tff(c_620, plain, (![A_111, C_112]: (k1_relset_1(A_111, k1_xboole_0, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_601])).
% 3.80/1.69  tff(c_626, plain, (![A_111]: (k1_relset_1(A_111, k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_590, c_620])).
% 3.80/1.69  tff(c_640, plain, (![A_116, B_117, C_118]: (m1_subset_1(k1_relset_1(A_116, B_117, C_118), k1_zfmisc_1(A_116)) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.80/1.69  tff(c_653, plain, (![A_111]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_111)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_111, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_626, c_640])).
% 3.80/1.69  tff(c_660, plain, (![A_119]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_119)))), inference(demodulation, [status(thm), theory('equality')], [c_590, c_6, c_653])).
% 3.80/1.69  tff(c_674, plain, (![A_120]: (r1_tarski(k1_relat_1(k1_xboole_0), A_120))), inference(resolution, [status(thm)], [c_660, c_10])).
% 3.80/1.69  tff(c_683, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_674, c_2])).
% 3.80/1.69  tff(c_659, plain, (![A_111]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_111)))), inference(demodulation, [status(thm), theory('equality')], [c_590, c_6, c_653])).
% 3.80/1.69  tff(c_709, plain, (![A_122]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_122)))), inference(demodulation, [status(thm), theory('equality')], [c_683, c_659])).
% 3.80/1.69  tff(c_18, plain, (![A_10, B_11, C_12]: (k1_relset_1(A_10, B_11, C_12)=k1_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.80/1.69  tff(c_716, plain, (![A_10, B_11]: (k1_relset_1(A_10, B_11, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_709, c_18])).
% 3.80/1.69  tff(c_723, plain, (![A_10, B_11]: (k1_relset_1(A_10, B_11, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_683, c_716])).
% 3.80/1.69  tff(c_685, plain, (![A_111]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_111)))), inference(demodulation, [status(thm), theory('equality')], [c_683, c_659])).
% 3.80/1.69  tff(c_24, plain, (![C_15, B_14]: (v1_funct_2(C_15, k1_xboole_0, B_14) | k1_relset_1(k1_xboole_0, B_14, C_15)!=k1_xboole_0 | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_14))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.80/1.69  tff(c_726, plain, (![C_123, B_124]: (v1_funct_2(C_123, k1_xboole_0, B_124) | k1_relset_1(k1_xboole_0, B_124, C_123)!=k1_xboole_0 | ~m1_subset_1(C_123, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_24])).
% 3.80/1.69  tff(c_736, plain, (![B_124]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_124) | k1_relset_1(k1_xboole_0, B_124, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_685, c_726])).
% 3.80/1.69  tff(c_794, plain, (![B_124]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_124))), inference(demodulation, [status(thm), theory('equality')], [c_723, c_736])).
% 3.80/1.69  tff(c_1758, plain, (![B_124]: (v1_funct_2('#skF_1', '#skF_1', B_124))), inference(demodulation, [status(thm), theory('equality')], [c_1733, c_1733, c_794])).
% 3.80/1.69  tff(c_1764, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1733, c_1733, c_683])).
% 3.80/1.69  tff(c_1701, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1699, c_84])).
% 3.80/1.69  tff(c_1829, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1764, c_1733, c_1701])).
% 3.80/1.69  tff(c_1927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1758, c_1829])).
% 3.80/1.69  tff(c_1928, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_38])).
% 3.80/1.69  tff(c_1933, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_1928])).
% 3.80/1.69  tff(c_1936, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_1933])).
% 3.80/1.69  tff(c_1940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1936])).
% 3.80/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.69  
% 3.80/1.69  Inference rules
% 3.80/1.69  ----------------------
% 3.80/1.69  #Ref     : 0
% 3.80/1.69  #Sup     : 408
% 3.80/1.69  #Fact    : 0
% 3.80/1.69  #Define  : 0
% 3.80/1.69  #Split   : 4
% 3.80/1.69  #Chain   : 0
% 3.80/1.69  #Close   : 0
% 3.80/1.69  
% 3.80/1.69  Ordering : KBO
% 3.80/1.69  
% 3.80/1.69  Simplification rules
% 3.80/1.69  ----------------------
% 3.80/1.69  #Subsume      : 111
% 3.80/1.69  #Demod        : 402
% 3.80/1.69  #Tautology    : 152
% 3.80/1.69  #SimpNegUnit  : 6
% 3.80/1.69  #BackRed      : 45
% 3.80/1.69  
% 3.80/1.69  #Partial instantiations: 0
% 3.80/1.69  #Strategies tried      : 1
% 3.80/1.69  
% 3.80/1.69  Timing (in seconds)
% 3.80/1.69  ----------------------
% 3.80/1.69  Preprocessing        : 0.32
% 3.80/1.69  Parsing              : 0.17
% 3.80/1.69  CNF conversion       : 0.02
% 3.80/1.69  Main loop            : 0.53
% 3.80/1.69  Inferencing          : 0.19
% 3.80/1.69  Reduction            : 0.15
% 3.80/1.69  Demodulation         : 0.11
% 3.80/1.69  BG Simplification    : 0.03
% 3.80/1.69  Subsumption          : 0.10
% 3.80/1.69  Abstraction          : 0.04
% 3.80/1.69  MUC search           : 0.00
% 3.80/1.69  Cooper               : 0.00
% 3.80/1.69  Total                : 0.89
% 3.80/1.69  Index Insertion      : 0.00
% 3.80/1.69  Index Deletion       : 0.00
% 3.80/1.69  Index Matching       : 0.00
% 3.80/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
