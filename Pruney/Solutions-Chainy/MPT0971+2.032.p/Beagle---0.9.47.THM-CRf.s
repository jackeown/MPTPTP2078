%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:33 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  101 (1124 expanded)
%              Number of leaves         :   38 ( 406 expanded)
%              Depth                    :   12
%              Number of atoms          :  168 (3429 expanded)
%              Number of equality atoms :   57 (1450 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_16,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_116,plain,(
    ! [B_74,A_75] :
      ( v1_relat_1(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_119,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_62,c_116])).

tff(c_122,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_119])).

tff(c_66,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_152,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_relset_1(A_85,B_86,C_87) = k2_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_162,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_152])).

tff(c_60,plain,(
    r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_164,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_60])).

tff(c_243,plain,(
    ! [A_116,C_117] :
      ( r2_hidden('#skF_5'(A_116,k2_relat_1(A_116),C_117),k1_relat_1(A_116))
      | ~ r2_hidden(C_117,k2_relat_1(A_116))
      | ~ v1_funct_1(A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_192,plain,(
    ! [A_109,C_110] :
      ( r2_hidden(k4_tarski(A_109,k1_funct_1(C_110,A_109)),C_110)
      | ~ r2_hidden(A_109,k1_relat_1(C_110))
      | ~ v1_funct_1(C_110)
      | ~ v1_relat_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    ! [C_110,A_109] :
      ( ~ v1_xboole_0(C_110)
      | ~ r2_hidden(A_109,k1_relat_1(C_110))
      | ~ v1_funct_1(C_110)
      | ~ v1_relat_1(C_110) ) ),
    inference(resolution,[status(thm)],[c_192,c_2])).

tff(c_256,plain,(
    ! [A_118,C_119] :
      ( ~ v1_xboole_0(A_118)
      | ~ r2_hidden(C_119,k2_relat_1(A_118))
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(resolution,[status(thm)],[c_243,c_215])).

tff(c_266,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_164,c_256])).

tff(c_275,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_66,c_266])).

tff(c_20,plain,(
    ! [A_12,C_48] :
      ( k1_funct_1(A_12,'#skF_5'(A_12,k2_relat_1(A_12),C_48)) = C_48
      | ~ r2_hidden(C_48,k2_relat_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_64,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_134,plain,(
    ! [A_78,B_79,C_80] :
      ( k1_relset_1(A_78,B_79,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_144,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_134])).

tff(c_723,plain,(
    ! [B_167,A_168,C_169] :
      ( k1_xboole_0 = B_167
      | k1_relset_1(A_168,B_167,C_169) = A_168
      | ~ v1_funct_2(C_169,A_168,B_167)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_168,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_726,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_723])).

tff(c_735,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_144,c_726])).

tff(c_737,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_735])).

tff(c_22,plain,(
    ! [A_12,C_48] :
      ( r2_hidden('#skF_5'(A_12,k2_relat_1(A_12),C_48),k1_relat_1(A_12))
      | ~ r2_hidden(C_48,k2_relat_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_743,plain,(
    ! [C_48] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_48),'#skF_6')
      | ~ r2_hidden(C_48,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_737,c_22])).

tff(c_768,plain,(
    ! [C_170] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_170),'#skF_6')
      | ~ r2_hidden(C_170,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_66,c_743])).

tff(c_58,plain,(
    ! [E_65] :
      ( k1_funct_1('#skF_9',E_65) != '#skF_8'
      | ~ r2_hidden(E_65,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_777,plain,(
    ! [C_171] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_171)) != '#skF_8'
      | ~ r2_hidden(C_171,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_768,c_58])).

tff(c_781,plain,(
    ! [C_48] :
      ( C_48 != '#skF_8'
      | ~ r2_hidden(C_48,k2_relat_1('#skF_9'))
      | ~ r2_hidden(C_48,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_777])).

tff(c_828,plain,(
    ~ r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_66,c_781])).

tff(c_830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_828,c_164])).

tff(c_832,plain,(
    k1_relat_1('#skF_9') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_735])).

tff(c_831,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_735])).

tff(c_10,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_845,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_831,c_10])).

tff(c_852,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_62])).

tff(c_48,plain,(
    ! [C_63,A_61] :
      ( k1_xboole_0 = C_63
      | ~ v1_funct_2(C_63,A_61,k1_xboole_0)
      | k1_xboole_0 = A_61
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_69,plain,(
    ! [C_63,A_61] :
      ( k1_xboole_0 = C_63
      | ~ v1_funct_2(C_63,A_61,k1_xboole_0)
      | k1_xboole_0 = A_61
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_48])).

tff(c_1057,plain,(
    ! [C_198,A_199] :
      ( C_198 = '#skF_7'
      | ~ v1_funct_2(C_198,A_199,'#skF_7')
      | A_199 = '#skF_7'
      | ~ m1_subset_1(C_198,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_831,c_831,c_831,c_69])).

tff(c_1059,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_64,c_1057])).

tff(c_1062,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_1059])).

tff(c_1063,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1062])).

tff(c_1075,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_852])).

tff(c_12,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_143,plain,(
    ! [B_6,C_80] :
      ( k1_relset_1(k1_xboole_0,B_6,C_80) = k1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_134])).

tff(c_1036,plain,(
    ! [B_191,C_192] :
      ( k1_relset_1('#skF_7',B_191,C_192) = k1_relat_1(C_192)
      | ~ m1_subset_1(C_192,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_831,c_143])).

tff(c_1039,plain,(
    ! [B_191] : k1_relset_1('#skF_7',B_191,'#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_852,c_1036])).

tff(c_1065,plain,(
    ! [B_191] : k1_relset_1('#skF_6',B_191,'#skF_9') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1039])).

tff(c_1081,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_64])).

tff(c_54,plain,(
    ! [B_62,C_63] :
      ( k1_relset_1(k1_xboole_0,B_62,C_63) = k1_xboole_0
      | ~ v1_funct_2(C_63,k1_xboole_0,B_62)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_68,plain,(
    ! [B_62,C_63] :
      ( k1_relset_1(k1_xboole_0,B_62,C_63) = k1_xboole_0
      | ~ v1_funct_2(C_63,k1_xboole_0,B_62)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_54])).

tff(c_835,plain,(
    ! [B_62,C_63] :
      ( k1_relset_1('#skF_7',B_62,C_63) = '#skF_7'
      | ~ v1_funct_2(C_63,'#skF_7',B_62)
      | ~ m1_subset_1(C_63,k1_zfmisc_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_831,c_831,c_831,c_68])).

tff(c_1223,plain,(
    ! [B_222,C_223] :
      ( k1_relset_1('#skF_6',B_222,C_223) = '#skF_6'
      | ~ v1_funct_2(C_223,'#skF_6',B_222)
      | ~ m1_subset_1(C_223,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1063,c_1063,c_1063,c_835])).

tff(c_1225,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_9') = '#skF_6'
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1081,c_1223])).

tff(c_1228,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_1065,c_1225])).

tff(c_1230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_832,c_1228])).

tff(c_1231,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1062])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_847,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_6])).

tff(c_1247,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1231,c_847])).

tff(c_1252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_1247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:09:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.59  
% 3.39/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.59  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 3.39/1.59  
% 3.39/1.59  %Foreground sorts:
% 3.39/1.59  
% 3.39/1.59  
% 3.39/1.59  %Background operators:
% 3.39/1.59  
% 3.39/1.59  
% 3.39/1.59  %Foreground operators:
% 3.39/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.39/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.39/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.39/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.39/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.39/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.39/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.39/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.39/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.39/1.59  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.39/1.59  tff('#skF_9', type, '#skF_9': $i).
% 3.39/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.39/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.39/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.39/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.39/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.39/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.39/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.39/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.39/1.59  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.39/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.59  
% 3.39/1.61  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.39/1.61  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 3.39/1.61  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.39/1.61  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.39/1.61  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.39/1.61  tff(f_72, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.39/1.61  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.39/1.61  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.39/1.61  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.39/1.61  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.39/1.61  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.39/1.61  tff(c_16, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.39/1.61  tff(c_62, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.39/1.61  tff(c_116, plain, (![B_74, A_75]: (v1_relat_1(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.39/1.61  tff(c_119, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_62, c_116])).
% 3.39/1.61  tff(c_122, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_119])).
% 3.39/1.61  tff(c_66, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.39/1.61  tff(c_152, plain, (![A_85, B_86, C_87]: (k2_relset_1(A_85, B_86, C_87)=k2_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.39/1.61  tff(c_162, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_62, c_152])).
% 3.39/1.61  tff(c_60, plain, (r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.39/1.61  tff(c_164, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_60])).
% 3.39/1.61  tff(c_243, plain, (![A_116, C_117]: (r2_hidden('#skF_5'(A_116, k2_relat_1(A_116), C_117), k1_relat_1(A_116)) | ~r2_hidden(C_117, k2_relat_1(A_116)) | ~v1_funct_1(A_116) | ~v1_relat_1(A_116))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.39/1.61  tff(c_192, plain, (![A_109, C_110]: (r2_hidden(k4_tarski(A_109, k1_funct_1(C_110, A_109)), C_110) | ~r2_hidden(A_109, k1_relat_1(C_110)) | ~v1_funct_1(C_110) | ~v1_relat_1(C_110))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.39/1.61  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.61  tff(c_215, plain, (![C_110, A_109]: (~v1_xboole_0(C_110) | ~r2_hidden(A_109, k1_relat_1(C_110)) | ~v1_funct_1(C_110) | ~v1_relat_1(C_110))), inference(resolution, [status(thm)], [c_192, c_2])).
% 3.39/1.61  tff(c_256, plain, (![A_118, C_119]: (~v1_xboole_0(A_118) | ~r2_hidden(C_119, k2_relat_1(A_118)) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(resolution, [status(thm)], [c_243, c_215])).
% 3.39/1.61  tff(c_266, plain, (~v1_xboole_0('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_164, c_256])).
% 3.39/1.61  tff(c_275, plain, (~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_66, c_266])).
% 3.39/1.61  tff(c_20, plain, (![A_12, C_48]: (k1_funct_1(A_12, '#skF_5'(A_12, k2_relat_1(A_12), C_48))=C_48 | ~r2_hidden(C_48, k2_relat_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.39/1.61  tff(c_64, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.39/1.61  tff(c_134, plain, (![A_78, B_79, C_80]: (k1_relset_1(A_78, B_79, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.39/1.61  tff(c_144, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_62, c_134])).
% 3.39/1.61  tff(c_723, plain, (![B_167, A_168, C_169]: (k1_xboole_0=B_167 | k1_relset_1(A_168, B_167, C_169)=A_168 | ~v1_funct_2(C_169, A_168, B_167) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_168, B_167))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.39/1.61  tff(c_726, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_62, c_723])).
% 3.39/1.61  tff(c_735, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_144, c_726])).
% 3.39/1.61  tff(c_737, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_735])).
% 3.39/1.61  tff(c_22, plain, (![A_12, C_48]: (r2_hidden('#skF_5'(A_12, k2_relat_1(A_12), C_48), k1_relat_1(A_12)) | ~r2_hidden(C_48, k2_relat_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.39/1.61  tff(c_743, plain, (![C_48]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_48), '#skF_6') | ~r2_hidden(C_48, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_737, c_22])).
% 3.39/1.61  tff(c_768, plain, (![C_170]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_170), '#skF_6') | ~r2_hidden(C_170, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_66, c_743])).
% 3.39/1.61  tff(c_58, plain, (![E_65]: (k1_funct_1('#skF_9', E_65)!='#skF_8' | ~r2_hidden(E_65, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.39/1.61  tff(c_777, plain, (![C_171]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_171))!='#skF_8' | ~r2_hidden(C_171, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_768, c_58])).
% 3.39/1.61  tff(c_781, plain, (![C_48]: (C_48!='#skF_8' | ~r2_hidden(C_48, k2_relat_1('#skF_9')) | ~r2_hidden(C_48, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_777])).
% 3.39/1.61  tff(c_828, plain, (~r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_66, c_781])).
% 3.39/1.61  tff(c_830, plain, $false, inference(negUnitSimplification, [status(thm)], [c_828, c_164])).
% 3.39/1.61  tff(c_832, plain, (k1_relat_1('#skF_9')!='#skF_6'), inference(splitRight, [status(thm)], [c_735])).
% 3.39/1.61  tff(c_831, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_735])).
% 3.39/1.61  tff(c_10, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.39/1.61  tff(c_845, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_7')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_831, c_831, c_10])).
% 3.39/1.61  tff(c_852, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_845, c_62])).
% 3.39/1.61  tff(c_48, plain, (![C_63, A_61]: (k1_xboole_0=C_63 | ~v1_funct_2(C_63, A_61, k1_xboole_0) | k1_xboole_0=A_61 | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.39/1.61  tff(c_69, plain, (![C_63, A_61]: (k1_xboole_0=C_63 | ~v1_funct_2(C_63, A_61, k1_xboole_0) | k1_xboole_0=A_61 | ~m1_subset_1(C_63, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_48])).
% 3.39/1.61  tff(c_1057, plain, (![C_198, A_199]: (C_198='#skF_7' | ~v1_funct_2(C_198, A_199, '#skF_7') | A_199='#skF_7' | ~m1_subset_1(C_198, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_831, c_831, c_831, c_831, c_69])).
% 3.39/1.61  tff(c_1059, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_6' | ~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_64, c_1057])).
% 3.39/1.61  tff(c_1062, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_852, c_1059])).
% 3.39/1.61  tff(c_1063, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_1062])).
% 3.39/1.61  tff(c_1075, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_852])).
% 3.39/1.61  tff(c_12, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.39/1.61  tff(c_143, plain, (![B_6, C_80]: (k1_relset_1(k1_xboole_0, B_6, C_80)=k1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_134])).
% 3.39/1.61  tff(c_1036, plain, (![B_191, C_192]: (k1_relset_1('#skF_7', B_191, C_192)=k1_relat_1(C_192) | ~m1_subset_1(C_192, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_831, c_831, c_143])).
% 3.39/1.61  tff(c_1039, plain, (![B_191]: (k1_relset_1('#skF_7', B_191, '#skF_9')=k1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_852, c_1036])).
% 3.39/1.61  tff(c_1065, plain, (![B_191]: (k1_relset_1('#skF_6', B_191, '#skF_9')=k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_1039])).
% 3.39/1.61  tff(c_1081, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_64])).
% 3.39/1.61  tff(c_54, plain, (![B_62, C_63]: (k1_relset_1(k1_xboole_0, B_62, C_63)=k1_xboole_0 | ~v1_funct_2(C_63, k1_xboole_0, B_62) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_62))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.39/1.61  tff(c_68, plain, (![B_62, C_63]: (k1_relset_1(k1_xboole_0, B_62, C_63)=k1_xboole_0 | ~v1_funct_2(C_63, k1_xboole_0, B_62) | ~m1_subset_1(C_63, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_54])).
% 3.39/1.61  tff(c_835, plain, (![B_62, C_63]: (k1_relset_1('#skF_7', B_62, C_63)='#skF_7' | ~v1_funct_2(C_63, '#skF_7', B_62) | ~m1_subset_1(C_63, k1_zfmisc_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_831, c_831, c_831, c_831, c_68])).
% 3.39/1.61  tff(c_1223, plain, (![B_222, C_223]: (k1_relset_1('#skF_6', B_222, C_223)='#skF_6' | ~v1_funct_2(C_223, '#skF_6', B_222) | ~m1_subset_1(C_223, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_1063, c_1063, c_1063, c_835])).
% 3.39/1.61  tff(c_1225, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_9')='#skF_6' | ~m1_subset_1('#skF_9', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_1081, c_1223])).
% 3.39/1.61  tff(c_1228, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1075, c_1065, c_1225])).
% 3.39/1.61  tff(c_1230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_832, c_1228])).
% 3.39/1.61  tff(c_1231, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_1062])).
% 3.39/1.61  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.39/1.61  tff(c_847, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_831, c_6])).
% 3.39/1.61  tff(c_1247, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1231, c_847])).
% 3.39/1.61  tff(c_1252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_275, c_1247])).
% 3.39/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.61  
% 3.39/1.61  Inference rules
% 3.39/1.61  ----------------------
% 3.39/1.61  #Ref     : 0
% 3.39/1.61  #Sup     : 247
% 3.39/1.61  #Fact    : 0
% 3.39/1.61  #Define  : 0
% 3.39/1.61  #Split   : 8
% 3.39/1.61  #Chain   : 0
% 3.39/1.61  #Close   : 0
% 3.39/1.61  
% 3.39/1.61  Ordering : KBO
% 3.39/1.61  
% 3.39/1.61  Simplification rules
% 3.39/1.61  ----------------------
% 3.39/1.61  #Subsume      : 32
% 3.39/1.61  #Demod        : 275
% 3.39/1.61  #Tautology    : 125
% 3.39/1.61  #SimpNegUnit  : 6
% 3.39/1.61  #BackRed      : 112
% 3.39/1.61  
% 3.39/1.61  #Partial instantiations: 0
% 3.39/1.61  #Strategies tried      : 1
% 3.39/1.61  
% 3.39/1.61  Timing (in seconds)
% 3.39/1.61  ----------------------
% 3.39/1.61  Preprocessing        : 0.35
% 3.39/1.61  Parsing              : 0.18
% 3.39/1.61  CNF conversion       : 0.03
% 3.39/1.61  Main loop            : 0.46
% 3.39/1.61  Inferencing          : 0.16
% 3.39/1.61  Reduction            : 0.14
% 3.39/1.61  Demodulation         : 0.10
% 3.39/1.61  BG Simplification    : 0.03
% 3.39/1.61  Subsumption          : 0.09
% 3.39/1.61  Abstraction          : 0.03
% 3.39/1.61  MUC search           : 0.00
% 3.39/1.61  Cooper               : 0.00
% 3.39/1.61  Total                : 0.85
% 3.39/1.61  Index Insertion      : 0.00
% 3.39/1.61  Index Deletion       : 0.00
% 3.39/1.61  Index Matching       : 0.00
% 3.39/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
