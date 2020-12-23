%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:25 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 210 expanded)
%              Number of leaves         :   43 (  91 expanded)
%              Depth                    :   11
%              Number of atoms          :  158 ( 509 expanded)
%              Number of equality atoms :   40 ( 115 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_75,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_66,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_68,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_430,plain,(
    ! [A_156,B_157,C_158] :
      ( k2_relset_1(A_156,B_157,C_158) = k2_relat_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_434,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_430])).

tff(c_435,plain,(
    k2_relat_1('#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_66])).

tff(c_26,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_144,plain,(
    ! [B_97,A_98] :
      ( v1_relat_1(B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_98))
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_147,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_68,c_144])).

tff(c_150,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_147])).

tff(c_186,plain,(
    ! [C_109,B_110,A_111] :
      ( v5_relat_1(C_109,B_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_111,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_190,plain,(
    v5_relat_1('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_186])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_164,plain,(
    ! [B_104,A_105] :
      ( r1_tarski(k2_relat_1(B_104),A_105)
      | ~ v5_relat_1(B_104,A_105)
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_99,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_2'(A_85,B_86),A_85)
      | r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_87,B_88] :
      ( ~ v1_xboole_0(A_87)
      | r1_tarski(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_107,plain,(
    ! [B_88,A_87] :
      ( B_88 = A_87
      | ~ r1_tarski(B_88,A_87)
      | ~ v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_104,c_14])).

tff(c_362,plain,(
    ! [B_137,A_138] :
      ( k2_relat_1(B_137) = A_138
      | ~ v1_xboole_0(A_138)
      | ~ v5_relat_1(B_137,A_138)
      | ~ v1_relat_1(B_137) ) ),
    inference(resolution,[status(thm)],[c_164,c_107])).

tff(c_365,plain,
    ( k2_relat_1('#skF_9') = '#skF_8'
    | ~ v1_xboole_0('#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_190,c_362])).

tff(c_371,plain,
    ( k2_relat_1('#skF_9') = '#skF_8'
    | ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_365])).

tff(c_374,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_371])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_70,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_375,plain,(
    ! [A_139,B_140,C_141] :
      ( k1_relset_1(A_139,B_140,C_141) = k1_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_379,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_375])).

tff(c_938,plain,(
    ! [B_223,A_224,C_225] :
      ( k1_xboole_0 = B_223
      | k1_relset_1(A_224,B_223,C_225) = A_224
      | ~ v1_funct_2(C_225,A_224,B_223)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_224,B_223))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_941,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_938])).

tff(c_944,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_379,c_941])).

tff(c_945,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_944])).

tff(c_76,plain,(
    ! [D_74] :
      ( r2_hidden('#skF_10'(D_74),'#skF_7')
      | ~ r2_hidden(D_74,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_176,plain,(
    ! [C_106,B_107,A_108] :
      ( r2_hidden(C_106,B_107)
      | ~ r2_hidden(C_106,A_108)
      | ~ r1_tarski(A_108,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_184,plain,(
    ! [D_74,B_107] :
      ( r2_hidden('#skF_10'(D_74),B_107)
      | ~ r1_tarski('#skF_7',B_107)
      | ~ r2_hidden(D_74,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_76,c_176])).

tff(c_72,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_74,plain,(
    ! [D_74] :
      ( k1_funct_1('#skF_9','#skF_10'(D_74)) = D_74
      | ~ r2_hidden(D_74,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_468,plain,(
    ! [A_165,D_166] :
      ( r2_hidden(k1_funct_1(A_165,D_166),k2_relat_1(A_165))
      | ~ r2_hidden(D_166,k1_relat_1(A_165))
      | ~ v1_funct_1(A_165)
      | ~ v1_relat_1(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_476,plain,(
    ! [D_74] :
      ( r2_hidden(D_74,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_74),k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_74,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_468])).

tff(c_481,plain,(
    ! [D_167] :
      ( r2_hidden(D_167,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_10'(D_167),k1_relat_1('#skF_9'))
      | ~ r2_hidden(D_167,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_72,c_476])).

tff(c_486,plain,(
    ! [D_74] :
      ( r2_hidden(D_74,k2_relat_1('#skF_9'))
      | ~ r1_tarski('#skF_7',k1_relat_1('#skF_9'))
      | ~ r2_hidden(D_74,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_184,c_481])).

tff(c_514,plain,(
    ~ r1_tarski('#skF_7',k1_relat_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_486])).

tff(c_946,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_514])).

tff(c_951,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_946])).

tff(c_952,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_944])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_962,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_952,c_12])).

tff(c_964,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_962])).

tff(c_1022,plain,(
    ! [D_229] :
      ( r2_hidden(D_229,k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_229,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_486])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1067,plain,(
    ! [A_234] :
      ( r1_tarski(A_234,k2_relat_1('#skF_9'))
      | ~ r2_hidden('#skF_2'(A_234,k2_relat_1('#skF_9')),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1022,c_8])).

tff(c_1077,plain,(
    r1_tarski('#skF_8',k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_10,c_1067])).

tff(c_175,plain,(
    ! [B_104,A_105] :
      ( k2_relat_1(B_104) = A_105
      | ~ r1_tarski(A_105,k2_relat_1(B_104))
      | ~ v5_relat_1(B_104,A_105)
      | ~ v1_relat_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_164,c_14])).

tff(c_1082,plain,
    ( k2_relat_1('#skF_9') = '#skF_8'
    | ~ v5_relat_1('#skF_9','#skF_8')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1077,c_175])).

tff(c_1098,plain,(
    k2_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_190,c_1082])).

tff(c_1100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_435,c_1098])).

tff(c_1101,plain,(
    k2_relat_1('#skF_9') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_371])).

tff(c_1163,plain,(
    ! [A_240,B_241,C_242] :
      ( k2_relset_1(A_240,B_241,C_242) = k2_relat_1(C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1166,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_1163])).

tff(c_1168,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1101,c_1166])).

tff(c_1170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.52  
% 3.35/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 3.35/1.52  
% 3.35/1.52  %Foreground sorts:
% 3.35/1.52  
% 3.35/1.52  
% 3.35/1.52  %Background operators:
% 3.35/1.52  
% 3.35/1.52  
% 3.35/1.52  %Foreground operators:
% 3.35/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.35/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.35/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.35/1.52  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.35/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.35/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.35/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.35/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.35/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.35/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.35/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.35/1.52  tff('#skF_10', type, '#skF_10': $i > $i).
% 3.35/1.52  tff('#skF_9', type, '#skF_9': $i).
% 3.35/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.35/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.35/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.35/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.35/1.52  tff('#skF_8', type, '#skF_8': $i).
% 3.35/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.35/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.35/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.35/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.35/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.35/1.52  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.35/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.35/1.52  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.35/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.52  
% 3.53/1.54  tff(f_126, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 3.53/1.54  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.53/1.54  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.53/1.54  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.53/1.54  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.53/1.54  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.53/1.54  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.53/1.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.53/1.54  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.53/1.54  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.53/1.54  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.53/1.54  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.53/1.54  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.53/1.54  tff(c_66, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.53/1.54  tff(c_68, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.53/1.54  tff(c_430, plain, (![A_156, B_157, C_158]: (k2_relset_1(A_156, B_157, C_158)=k2_relat_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.53/1.54  tff(c_434, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_68, c_430])).
% 3.53/1.54  tff(c_435, plain, (k2_relat_1('#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_434, c_66])).
% 3.53/1.54  tff(c_26, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.53/1.54  tff(c_144, plain, (![B_97, A_98]: (v1_relat_1(B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(A_98)) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.53/1.54  tff(c_147, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_68, c_144])).
% 3.53/1.54  tff(c_150, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_147])).
% 3.53/1.54  tff(c_186, plain, (![C_109, B_110, A_111]: (v5_relat_1(C_109, B_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_110))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.53/1.54  tff(c_190, plain, (v5_relat_1('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_68, c_186])).
% 3.53/1.54  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.53/1.54  tff(c_164, plain, (![B_104, A_105]: (r1_tarski(k2_relat_1(B_104), A_105) | ~v5_relat_1(B_104, A_105) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.53/1.54  tff(c_99, plain, (![A_85, B_86]: (r2_hidden('#skF_2'(A_85, B_86), A_85) | r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.53/1.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.54  tff(c_104, plain, (![A_87, B_88]: (~v1_xboole_0(A_87) | r1_tarski(A_87, B_88))), inference(resolution, [status(thm)], [c_99, c_2])).
% 3.53/1.54  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.53/1.54  tff(c_107, plain, (![B_88, A_87]: (B_88=A_87 | ~r1_tarski(B_88, A_87) | ~v1_xboole_0(A_87))), inference(resolution, [status(thm)], [c_104, c_14])).
% 3.53/1.54  tff(c_362, plain, (![B_137, A_138]: (k2_relat_1(B_137)=A_138 | ~v1_xboole_0(A_138) | ~v5_relat_1(B_137, A_138) | ~v1_relat_1(B_137))), inference(resolution, [status(thm)], [c_164, c_107])).
% 3.53/1.54  tff(c_365, plain, (k2_relat_1('#skF_9')='#skF_8' | ~v1_xboole_0('#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_190, c_362])).
% 3.53/1.54  tff(c_371, plain, (k2_relat_1('#skF_9')='#skF_8' | ~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_365])).
% 3.53/1.54  tff(c_374, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_371])).
% 3.53/1.54  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.53/1.54  tff(c_70, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.53/1.54  tff(c_375, plain, (![A_139, B_140, C_141]: (k1_relset_1(A_139, B_140, C_141)=k1_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.53/1.54  tff(c_379, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_68, c_375])).
% 3.53/1.54  tff(c_938, plain, (![B_223, A_224, C_225]: (k1_xboole_0=B_223 | k1_relset_1(A_224, B_223, C_225)=A_224 | ~v1_funct_2(C_225, A_224, B_223) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_224, B_223))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.53/1.54  tff(c_941, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_68, c_938])).
% 3.53/1.54  tff(c_944, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_379, c_941])).
% 3.53/1.54  tff(c_945, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_944])).
% 3.53/1.54  tff(c_76, plain, (![D_74]: (r2_hidden('#skF_10'(D_74), '#skF_7') | ~r2_hidden(D_74, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.53/1.54  tff(c_176, plain, (![C_106, B_107, A_108]: (r2_hidden(C_106, B_107) | ~r2_hidden(C_106, A_108) | ~r1_tarski(A_108, B_107))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.53/1.54  tff(c_184, plain, (![D_74, B_107]: (r2_hidden('#skF_10'(D_74), B_107) | ~r1_tarski('#skF_7', B_107) | ~r2_hidden(D_74, '#skF_8'))), inference(resolution, [status(thm)], [c_76, c_176])).
% 3.53/1.54  tff(c_72, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.53/1.54  tff(c_74, plain, (![D_74]: (k1_funct_1('#skF_9', '#skF_10'(D_74))=D_74 | ~r2_hidden(D_74, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.53/1.54  tff(c_468, plain, (![A_165, D_166]: (r2_hidden(k1_funct_1(A_165, D_166), k2_relat_1(A_165)) | ~r2_hidden(D_166, k1_relat_1(A_165)) | ~v1_funct_1(A_165) | ~v1_relat_1(A_165))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.53/1.54  tff(c_476, plain, (![D_74]: (r2_hidden(D_74, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_74), k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_74, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_468])).
% 3.53/1.54  tff(c_481, plain, (![D_167]: (r2_hidden(D_167, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_10'(D_167), k1_relat_1('#skF_9')) | ~r2_hidden(D_167, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_72, c_476])).
% 3.53/1.54  tff(c_486, plain, (![D_74]: (r2_hidden(D_74, k2_relat_1('#skF_9')) | ~r1_tarski('#skF_7', k1_relat_1('#skF_9')) | ~r2_hidden(D_74, '#skF_8'))), inference(resolution, [status(thm)], [c_184, c_481])).
% 3.53/1.54  tff(c_514, plain, (~r1_tarski('#skF_7', k1_relat_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_486])).
% 3.53/1.54  tff(c_946, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_945, c_514])).
% 3.53/1.54  tff(c_951, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_946])).
% 3.53/1.54  tff(c_952, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_944])).
% 3.53/1.54  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.53/1.54  tff(c_962, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_952, c_12])).
% 3.53/1.54  tff(c_964, plain, $false, inference(negUnitSimplification, [status(thm)], [c_374, c_962])).
% 3.53/1.54  tff(c_1022, plain, (![D_229]: (r2_hidden(D_229, k2_relat_1('#skF_9')) | ~r2_hidden(D_229, '#skF_8'))), inference(splitRight, [status(thm)], [c_486])).
% 3.53/1.54  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.53/1.54  tff(c_1067, plain, (![A_234]: (r1_tarski(A_234, k2_relat_1('#skF_9')) | ~r2_hidden('#skF_2'(A_234, k2_relat_1('#skF_9')), '#skF_8'))), inference(resolution, [status(thm)], [c_1022, c_8])).
% 3.53/1.54  tff(c_1077, plain, (r1_tarski('#skF_8', k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_10, c_1067])).
% 3.53/1.54  tff(c_175, plain, (![B_104, A_105]: (k2_relat_1(B_104)=A_105 | ~r1_tarski(A_105, k2_relat_1(B_104)) | ~v5_relat_1(B_104, A_105) | ~v1_relat_1(B_104))), inference(resolution, [status(thm)], [c_164, c_14])).
% 3.53/1.54  tff(c_1082, plain, (k2_relat_1('#skF_9')='#skF_8' | ~v5_relat_1('#skF_9', '#skF_8') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1077, c_175])).
% 3.53/1.54  tff(c_1098, plain, (k2_relat_1('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_190, c_1082])).
% 3.53/1.54  tff(c_1100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_435, c_1098])).
% 3.53/1.54  tff(c_1101, plain, (k2_relat_1('#skF_9')='#skF_8'), inference(splitRight, [status(thm)], [c_371])).
% 3.53/1.54  tff(c_1163, plain, (![A_240, B_241, C_242]: (k2_relset_1(A_240, B_241, C_242)=k2_relat_1(C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.53/1.54  tff(c_1166, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_68, c_1163])).
% 3.53/1.54  tff(c_1168, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1101, c_1166])).
% 3.53/1.54  tff(c_1170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1168])).
% 3.53/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.54  
% 3.53/1.54  Inference rules
% 3.53/1.54  ----------------------
% 3.53/1.54  #Ref     : 0
% 3.53/1.54  #Sup     : 229
% 3.53/1.54  #Fact    : 0
% 3.53/1.54  #Define  : 0
% 3.53/1.54  #Split   : 10
% 3.53/1.54  #Chain   : 0
% 3.53/1.54  #Close   : 0
% 3.53/1.54  
% 3.53/1.54  Ordering : KBO
% 3.53/1.54  
% 3.53/1.54  Simplification rules
% 3.53/1.54  ----------------------
% 3.53/1.54  #Subsume      : 84
% 3.53/1.54  #Demod        : 75
% 3.53/1.54  #Tautology    : 48
% 3.53/1.54  #SimpNegUnit  : 8
% 3.53/1.54  #BackRed      : 17
% 3.53/1.54  
% 3.53/1.54  #Partial instantiations: 0
% 3.53/1.54  #Strategies tried      : 1
% 3.53/1.54  
% 3.53/1.54  Timing (in seconds)
% 3.53/1.54  ----------------------
% 3.53/1.54  Preprocessing        : 0.35
% 3.53/1.54  Parsing              : 0.17
% 3.53/1.54  CNF conversion       : 0.03
% 3.53/1.54  Main loop            : 0.43
% 3.53/1.54  Inferencing          : 0.15
% 3.53/1.54  Reduction            : 0.12
% 3.53/1.54  Demodulation         : 0.08
% 3.53/1.54  BG Simplification    : 0.02
% 3.53/1.54  Subsumption          : 0.11
% 3.53/1.54  Abstraction          : 0.02
% 3.53/1.54  MUC search           : 0.00
% 3.53/1.54  Cooper               : 0.00
% 3.53/1.54  Total                : 0.81
% 3.53/1.54  Index Insertion      : 0.00
% 3.53/1.54  Index Deletion       : 0.00
% 3.53/1.54  Index Matching       : 0.00
% 3.53/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
