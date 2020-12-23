%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:26 EST 2020

% Result     : Theorem 10.37s
% Output     : CNFRefutation 11.12s
% Verified   : 
% Statistics : Number of formulae       :  682 (17724 expanded)
%              Number of leaves         :   40 (6022 expanded)
%              Depth                    :   47
%              Number of atoms          : 1992 (55900 expanded)
%              Number of equality atoms :  480 (15659 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_104,axiom,(
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

tff(f_64,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_139,plain,(
    ! [A_105,B_106,C_107] :
      ( k2_relset_1(A_105,B_106,C_107) = k2_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_143,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_139])).

tff(c_58,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_149,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_58])).

tff(c_16,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_82,plain,(
    ! [B_80,A_81] :
      ( v1_relat_1(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_85,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_60,c_82])).

tff(c_88,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_85])).

tff(c_64,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [A_82,B_83] :
      ( ~ r2_hidden('#skF_1'(A_82,B_83),B_83)
      | r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_62,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_144,plain,(
    ! [A_108,B_109,C_110] :
      ( k1_relset_1(A_108,B_109,C_110) = k1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_148,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_144])).

tff(c_17799,plain,(
    ! [B_1829,A_1830,C_1831] :
      ( k1_xboole_0 = B_1829
      | k1_relset_1(A_1830,B_1829,C_1831) = A_1830
      | ~ v1_funct_2(C_1831,A_1830,B_1829)
      | ~ m1_subset_1(C_1831,k1_zfmisc_1(k2_zfmisc_1(A_1830,B_1829))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_17802,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_17799])).

tff(c_17805,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_148,c_17802])).

tff(c_17806,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_17805])).

tff(c_17963,plain,(
    ! [A_1841,B_1842] :
      ( r2_hidden('#skF_3'(A_1841,B_1842),k1_relat_1(A_1841))
      | r2_hidden('#skF_4'(A_1841,B_1842),B_1842)
      | k2_relat_1(A_1841) = B_1842
      | ~ v1_funct_1(A_1841)
      | ~ v1_relat_1(A_1841) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_17972,plain,(
    ! [A_1841,B_1842,B_2] :
      ( r2_hidden('#skF_3'(A_1841,B_1842),B_2)
      | ~ r1_tarski(k1_relat_1(A_1841),B_2)
      | r2_hidden('#skF_4'(A_1841,B_1842),B_1842)
      | k2_relat_1(A_1841) = B_1842
      | ~ v1_funct_1(A_1841)
      | ~ v1_relat_1(A_1841) ) ),
    inference(resolution,[status(thm)],[c_17963,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_115,plain,(
    ! [C_93,B_94,A_95] :
      ( v5_relat_1(C_93,B_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_119,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_115])).

tff(c_66,plain,(
    ! [D_71] :
      ( k1_funct_1('#skF_8','#skF_9'(D_71)) = D_71
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_68,plain,(
    ! [D_71] :
      ( r2_hidden('#skF_9'(D_71),'#skF_6')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_107,plain,(
    ! [C_89,B_90,A_91] :
      ( r2_hidden(C_89,B_90)
      | ~ r2_hidden(C_89,A_91)
      | ~ r1_tarski(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_113,plain,(
    ! [D_71,B_90] :
      ( r2_hidden('#skF_9'(D_71),B_90)
      | ~ r1_tarski('#skF_6',B_90)
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_107])).

tff(c_129,plain,(
    ! [A_101,B_102,B_103] :
      ( r2_hidden('#skF_1'(A_101,B_102),B_103)
      | ~ r1_tarski(A_101,B_103)
      | r1_tarski(A_101,B_102) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_5318,plain,(
    ! [A_649,B_650,B_651,B_652] :
      ( r2_hidden('#skF_1'(A_649,B_650),B_651)
      | ~ r1_tarski(B_652,B_651)
      | ~ r1_tarski(A_649,B_652)
      | r1_tarski(A_649,B_650) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_6370,plain,(
    ! [A_768,B_769,A_770,B_771] :
      ( r2_hidden('#skF_1'(A_768,B_769),A_770)
      | ~ r1_tarski(A_768,k2_relat_1(B_771))
      | r1_tarski(A_768,B_769)
      | ~ v5_relat_1(B_771,A_770)
      | ~ v1_relat_1(B_771) ) ),
    inference(resolution,[status(thm)],[c_14,c_5318])).

tff(c_6398,plain,(
    ! [B_772,B_773,A_774] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_772),B_773),A_774)
      | r1_tarski(k2_relat_1(B_772),B_773)
      | ~ v5_relat_1(B_772,A_774)
      | ~ v1_relat_1(B_772) ) ),
    inference(resolution,[status(thm)],[c_94,c_6370])).

tff(c_258,plain,(
    ! [B_146,A_147,C_148] :
      ( k1_xboole_0 = B_146
      | k1_relset_1(A_147,B_146,C_148) = A_147
      | ~ v1_funct_2(C_148,A_147,B_146)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_261,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_258])).

tff(c_264,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_148,c_261])).

tff(c_265,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_264])).

tff(c_169,plain,(
    ! [B_114,A_115] :
      ( r2_hidden(k1_funct_1(B_114,A_115),k2_relat_1(B_114))
      | ~ r2_hidden(A_115,k1_relat_1(B_114))
      | ~ v1_funct_1(B_114)
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_174,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_169])).

tff(c_178,plain,(
    ! [D_116] :
      ( r2_hidden(D_116,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_116),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_116,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_174])).

tff(c_183,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_113,c_178])).

tff(c_184,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_266,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_184])).

tff(c_271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_266])).

tff(c_272,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_264])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_186,plain,(
    ! [A_119,B_120,B_121,B_122] :
      ( r2_hidden('#skF_1'(A_119,B_120),B_121)
      | ~ r1_tarski(B_122,B_121)
      | ~ r1_tarski(A_119,B_122)
      | r1_tarski(A_119,B_120) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_196,plain,(
    ! [A_123,B_124,A_125] :
      ( r2_hidden('#skF_1'(A_123,B_124),A_125)
      | ~ r1_tarski(A_123,k1_xboole_0)
      | r1_tarski(A_123,B_124) ) ),
    inference(resolution,[status(thm)],[c_8,c_186])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_206,plain,(
    ! [A_129,A_130] :
      ( ~ r1_tarski(A_129,k1_xboole_0)
      | r1_tarski(A_129,A_130) ) ),
    inference(resolution,[status(thm)],[c_196,c_4])).

tff(c_221,plain,(
    ! [B_131,A_132] :
      ( r1_tarski(k2_relat_1(B_131),A_132)
      | ~ v5_relat_1(B_131,k1_xboole_0)
      | ~ v1_relat_1(B_131) ) ),
    inference(resolution,[status(thm)],[c_14,c_206])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( v5_relat_1(B_11,A_10)
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_235,plain,(
    ! [B_131,A_132] :
      ( v5_relat_1(B_131,A_132)
      | ~ v5_relat_1(B_131,k1_xboole_0)
      | ~ v1_relat_1(B_131) ) ),
    inference(resolution,[status(thm)],[c_221,c_12])).

tff(c_318,plain,(
    ! [B_155,A_156] :
      ( v5_relat_1(B_155,A_156)
      | ~ v5_relat_1(B_155,'#skF_7')
      | ~ v1_relat_1(B_155) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_235])).

tff(c_320,plain,(
    ! [A_156] :
      ( v5_relat_1('#skF_8',A_156)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_119,c_318])).

tff(c_323,plain,(
    ! [A_156] : v5_relat_1('#skF_8',A_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_320])).

tff(c_48,plain,(
    ! [C_67,A_65] :
      ( k1_xboole_0 = C_67
      | ~ v1_funct_2(C_67,A_65,k1_xboole_0)
      | k1_xboole_0 = A_65
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_356,plain,(
    ! [C_164,A_165] :
      ( C_164 = '#skF_7'
      | ~ v1_funct_2(C_164,A_165,'#skF_7')
      | A_165 = '#skF_7'
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_165,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_272,c_272,c_272,c_48])).

tff(c_359,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_60,c_356])).

tff(c_362,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_359])).

tff(c_363,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_362])).

tff(c_120,plain,(
    ! [D_96,B_97] :
      ( r2_hidden('#skF_9'(D_96),B_97)
      | ~ r1_tarski('#skF_6',B_97)
      | ~ r2_hidden(D_96,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_107])).

tff(c_158,plain,(
    ! [D_111,B_112,B_113] :
      ( r2_hidden('#skF_9'(D_111),B_112)
      | ~ r1_tarski(B_113,B_112)
      | ~ r1_tarski('#skF_6',B_113)
      | ~ r2_hidden(D_111,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_120,c_2])).

tff(c_167,plain,(
    ! [D_111,A_6] :
      ( r2_hidden('#skF_9'(D_111),A_6)
      | ~ r1_tarski('#skF_6',k1_xboole_0)
      | ~ r2_hidden(D_111,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_8,c_158])).

tff(c_168,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_282,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_168])).

tff(c_370,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_282])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_370])).

tff(c_388,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_362])).

tff(c_404,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_149])).

tff(c_284,plain,(
    ! [A_6] : r1_tarski('#skF_7',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_8])).

tff(c_397,plain,(
    ! [A_6] : r1_tarski('#skF_8',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_284])).

tff(c_348,plain,(
    ! [A_161,B_162] :
      ( r2_hidden('#skF_3'(A_161,B_162),k1_relat_1(A_161))
      | r2_hidden('#skF_4'(A_161,B_162),B_162)
      | k2_relat_1(A_161) = B_162
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_353,plain,(
    ! [A_161,B_162,B_2] :
      ( r2_hidden('#skF_3'(A_161,B_162),B_2)
      | ~ r1_tarski(k1_relat_1(A_161),B_2)
      | r2_hidden('#skF_4'(A_161,B_162),B_162)
      | k2_relat_1(A_161) = B_162
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(resolution,[status(thm)],[c_348,c_2])).

tff(c_424,plain,(
    ! [A_167,B_168] :
      ( k1_funct_1(A_167,'#skF_3'(A_167,B_168)) = '#skF_2'(A_167,B_168)
      | r2_hidden('#skF_4'(A_167,B_168),B_168)
      | k2_relat_1(A_167) = B_168
      | ~ v1_funct_1(A_167)
      | ~ v1_relat_1(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_36,plain,(
    ! [B_55,A_54] :
      ( r2_hidden(k1_funct_1(B_55,A_54),k2_relat_1(B_55))
      | ~ r2_hidden(A_54,k1_relat_1(B_55))
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1028,plain,(
    ! [A_282,B_283] :
      ( r2_hidden('#skF_2'(A_282,B_283),k2_relat_1(A_282))
      | ~ r2_hidden('#skF_3'(A_282,B_283),k1_relat_1(A_282))
      | ~ v1_funct_1(A_282)
      | ~ v1_relat_1(A_282)
      | r2_hidden('#skF_4'(A_282,B_283),B_283)
      | k2_relat_1(A_282) = B_283
      | ~ v1_funct_1(A_282)
      | ~ v1_relat_1(A_282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_36])).

tff(c_1031,plain,(
    ! [A_161,B_162] :
      ( r2_hidden('#skF_2'(A_161,B_162),k2_relat_1(A_161))
      | ~ r1_tarski(k1_relat_1(A_161),k1_relat_1(A_161))
      | r2_hidden('#skF_4'(A_161,B_162),B_162)
      | k2_relat_1(A_161) = B_162
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(resolution,[status(thm)],[c_353,c_1028])).

tff(c_1054,plain,(
    ! [A_287,B_288] :
      ( r2_hidden('#skF_2'(A_287,B_288),k2_relat_1(A_287))
      | r2_hidden('#skF_4'(A_287,B_288),B_288)
      | k2_relat_1(A_287) = B_288
      | ~ v1_funct_1(A_287)
      | ~ v1_relat_1(A_287) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1031])).

tff(c_239,plain,(
    ! [A_139,C_140] :
      ( r2_hidden('#skF_5'(A_139,k2_relat_1(A_139),C_140),k1_relat_1(A_139))
      | ~ r2_hidden(C_140,k2_relat_1(A_139))
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_242,plain,(
    ! [A_139,C_140,B_2] :
      ( r2_hidden('#skF_5'(A_139,k2_relat_1(A_139),C_140),B_2)
      | ~ r1_tarski(k1_relat_1(A_139),B_2)
      | ~ r2_hidden(C_140,k2_relat_1(A_139))
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(resolution,[status(thm)],[c_239,c_2])).

tff(c_20,plain,(
    ! [A_14,C_50] :
      ( k1_funct_1(A_14,'#skF_5'(A_14,k2_relat_1(A_14),C_50)) = C_50
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_643,plain,(
    ! [A_216,B_217,A_218,B_219] :
      ( r2_hidden('#skF_1'(A_216,B_217),A_218)
      | ~ r1_tarski(A_216,k2_relat_1(B_219))
      | r1_tarski(A_216,B_217)
      | ~ v5_relat_1(B_219,A_218)
      | ~ v1_relat_1(B_219) ) ),
    inference(resolution,[status(thm)],[c_14,c_186])).

tff(c_754,plain,(
    ! [B_249,B_250,A_251,B_252] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_249),B_250),A_251)
      | r1_tarski(k2_relat_1(B_249),B_250)
      | ~ v5_relat_1(B_252,A_251)
      | ~ v1_relat_1(B_252)
      | ~ v5_relat_1(B_249,k2_relat_1(B_252))
      | ~ v1_relat_1(B_249) ) ),
    inference(resolution,[status(thm)],[c_14,c_643])).

tff(c_756,plain,(
    ! [B_249,B_250,A_156] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_249),B_250),A_156)
      | r1_tarski(k2_relat_1(B_249),B_250)
      | ~ v1_relat_1('#skF_8')
      | ~ v5_relat_1(B_249,k2_relat_1('#skF_8'))
      | ~ v1_relat_1(B_249) ) ),
    inference(resolution,[status(thm)],[c_323,c_754])).

tff(c_763,plain,(
    ! [B_253,B_254,A_255] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_253),B_254),A_255)
      | r1_tarski(k2_relat_1(B_253),B_254)
      | ~ v5_relat_1(B_253,k2_relat_1('#skF_8'))
      | ~ v1_relat_1(B_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_756])).

tff(c_772,plain,(
    ! [B_256,A_257] :
      ( r1_tarski(k2_relat_1(B_256),A_257)
      | ~ v5_relat_1(B_256,k2_relat_1('#skF_8'))
      | ~ v1_relat_1(B_256) ) ),
    inference(resolution,[status(thm)],[c_763,c_4])).

tff(c_775,plain,(
    ! [A_257] :
      ( r1_tarski(k2_relat_1('#skF_8'),A_257)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_323,c_772])).

tff(c_781,plain,(
    ! [A_257] : r1_tarski(k2_relat_1('#skF_8'),A_257) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_775])).

tff(c_790,plain,(
    ! [A_260] : r1_tarski(k2_relat_1('#skF_8'),A_260) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_775])).

tff(c_590,plain,(
    ! [B_203,A_204,B_205] :
      ( r2_hidden(k1_funct_1(B_203,A_204),B_205)
      | ~ r1_tarski(k2_relat_1(B_203),B_205)
      | ~ r2_hidden(A_204,k1_relat_1(B_203))
      | ~ v1_funct_1(B_203)
      | ~ v1_relat_1(B_203) ) ),
    inference(resolution,[status(thm)],[c_169,c_2])).

tff(c_602,plain,(
    ! [B_203,A_204,B_2,B_205] :
      ( r2_hidden(k1_funct_1(B_203,A_204),B_2)
      | ~ r1_tarski(B_205,B_2)
      | ~ r1_tarski(k2_relat_1(B_203),B_205)
      | ~ r2_hidden(A_204,k1_relat_1(B_203))
      | ~ v1_funct_1(B_203)
      | ~ v1_relat_1(B_203) ) ),
    inference(resolution,[status(thm)],[c_590,c_2])).

tff(c_892,plain,(
    ! [B_269,A_270,A_271] :
      ( r2_hidden(k1_funct_1(B_269,A_270),A_271)
      | ~ r1_tarski(k2_relat_1(B_269),k2_relat_1('#skF_8'))
      | ~ r2_hidden(A_270,k1_relat_1(B_269))
      | ~ v1_funct_1(B_269)
      | ~ v1_relat_1(B_269) ) ),
    inference(resolution,[status(thm)],[c_790,c_602])).

tff(c_895,plain,(
    ! [A_270,A_271] :
      ( r2_hidden(k1_funct_1('#skF_8',A_270),A_271)
      | ~ r2_hidden(A_270,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_781,c_892])).

tff(c_913,plain,(
    ! [A_272,A_273] :
      ( r2_hidden(k1_funct_1('#skF_8',A_272),A_273)
      | ~ r2_hidden(A_272,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_895])).

tff(c_926,plain,(
    ! [C_50,A_273] :
      ( r2_hidden(C_50,A_273)
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_50),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_50,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_913])).

tff(c_935,plain,(
    ! [C_275,A_276] :
      ( r2_hidden(C_275,A_276)
      | ~ r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_275),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_275,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_926])).

tff(c_938,plain,(
    ! [C_140,A_276] :
      ( r2_hidden(C_140,A_276)
      | ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8'))
      | ~ r2_hidden(C_140,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_242,c_935])).

tff(c_944,plain,(
    ! [C_140,A_276] :
      ( r2_hidden(C_140,A_276)
      | ~ r2_hidden(C_140,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_94,c_938])).

tff(c_1057,plain,(
    ! [B_288,A_276] :
      ( r2_hidden('#skF_2'('#skF_8',B_288),A_276)
      | r2_hidden('#skF_4'('#skF_8',B_288),B_288)
      | k2_relat_1('#skF_8') = B_288
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1054,c_944])).

tff(c_1079,plain,(
    ! [B_289,A_290] :
      ( r2_hidden('#skF_2'('#skF_8',B_289),A_290)
      | r2_hidden('#skF_4'('#skF_8',B_289),B_289)
      | k2_relat_1('#skF_8') = B_289 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_1057])).

tff(c_30,plain,(
    ! [A_14,B_36] :
      ( ~ r2_hidden('#skF_2'(A_14,B_36),B_36)
      | r2_hidden('#skF_4'(A_14,B_36),B_36)
      | k2_relat_1(A_14) = B_36
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1089,plain,(
    ! [A_290] :
      ( ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | r2_hidden('#skF_4'('#skF_8',A_290),A_290)
      | k2_relat_1('#skF_8') = A_290 ) ),
    inference(resolution,[status(thm)],[c_1079,c_30])).

tff(c_1113,plain,(
    ! [A_292] :
      ( r2_hidden('#skF_4'('#skF_8',A_292),A_292)
      | k2_relat_1('#skF_8') = A_292 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_1089])).

tff(c_1122,plain,(
    ! [A_293,B_294] :
      ( r2_hidden('#skF_4'('#skF_8',A_293),B_294)
      | ~ r1_tarski(A_293,B_294)
      | k2_relat_1('#skF_8') = A_293 ) ),
    inference(resolution,[status(thm)],[c_1113,c_2])).

tff(c_1138,plain,(
    ! [A_297,B_298,B_299] :
      ( r2_hidden('#skF_4'('#skF_8',A_297),B_298)
      | ~ r1_tarski(B_299,B_298)
      | ~ r1_tarski(A_297,B_299)
      | k2_relat_1('#skF_8') = A_297 ) ),
    inference(resolution,[status(thm)],[c_1122,c_2])).

tff(c_1167,plain,(
    ! [A_305,A_306,B_307] :
      ( r2_hidden('#skF_4'('#skF_8',A_305),A_306)
      | ~ r1_tarski(A_305,k2_relat_1(B_307))
      | k2_relat_1('#skF_8') = A_305
      | ~ v5_relat_1(B_307,A_306)
      | ~ v1_relat_1(B_307) ) ),
    inference(resolution,[status(thm)],[c_14,c_1138])).

tff(c_1176,plain,(
    ! [A_306,B_307] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_8'),A_306)
      | k2_relat_1('#skF_8') = '#skF_8'
      | ~ v5_relat_1(B_307,A_306)
      | ~ v1_relat_1(B_307) ) ),
    inference(resolution,[status(thm)],[c_397,c_1167])).

tff(c_1191,plain,(
    ! [A_308,B_309] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_8'),A_308)
      | ~ v5_relat_1(B_309,A_308)
      | ~ v1_relat_1(B_309) ) ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_1176])).

tff(c_1193,plain,(
    ! [A_156] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_8'),A_156)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_323,c_1191])).

tff(c_1198,plain,(
    ! [A_156] : r2_hidden('#skF_4'('#skF_8','#skF_8'),A_156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1193])).

tff(c_22,plain,(
    ! [A_14,C_50] :
      ( r2_hidden('#skF_5'(A_14,k2_relat_1(A_14),C_50),k1_relat_1(A_14))
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1038,plain,(
    ! [A_161,B_162] :
      ( r2_hidden('#skF_2'(A_161,B_162),k2_relat_1(A_161))
      | r2_hidden('#skF_4'(A_161,B_162),B_162)
      | k2_relat_1(A_161) = B_162
      | ~ v1_funct_1(A_161)
      | ~ v1_relat_1(A_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1031])).

tff(c_204,plain,(
    ! [A_123,A_125] :
      ( ~ r1_tarski(A_123,k1_xboole_0)
      | r1_tarski(A_123,A_125) ) ),
    inference(resolution,[status(thm)],[c_196,c_4])).

tff(c_280,plain,(
    ! [A_123,A_125] :
      ( ~ r1_tarski(A_123,'#skF_7')
      | r1_tarski(A_123,A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_204])).

tff(c_473,plain,(
    ! [A_169,A_170] :
      ( ~ r1_tarski(A_169,'#skF_8')
      | r1_tarski(A_169,A_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_280])).

tff(c_485,plain,(
    ! [B_11,A_170] :
      ( r1_tarski(k2_relat_1(B_11),A_170)
      | ~ v5_relat_1(B_11,'#skF_8')
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_473])).

tff(c_1006,plain,(
    ! [B_279,A_280,A_281] :
      ( r2_hidden(k1_funct_1(B_279,A_280),A_281)
      | ~ r2_hidden(A_280,k1_relat_1(B_279))
      | ~ v1_funct_1(B_279)
      | ~ v5_relat_1(B_279,'#skF_8')
      | ~ v1_relat_1(B_279) ) ),
    inference(resolution,[status(thm)],[c_485,c_892])).

tff(c_1277,plain,(
    ! [C_324,A_325,A_326] :
      ( r2_hidden(C_324,A_325)
      | ~ r2_hidden('#skF_5'(A_326,k2_relat_1(A_326),C_324),k1_relat_1(A_326))
      | ~ v1_funct_1(A_326)
      | ~ v5_relat_1(A_326,'#skF_8')
      | ~ v1_relat_1(A_326)
      | ~ r2_hidden(C_324,k2_relat_1(A_326))
      | ~ v1_funct_1(A_326)
      | ~ v1_relat_1(A_326) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1006])).

tff(c_1280,plain,(
    ! [C_140,A_325,A_139] :
      ( r2_hidden(C_140,A_325)
      | ~ v5_relat_1(A_139,'#skF_8')
      | ~ r1_tarski(k1_relat_1(A_139),k1_relat_1(A_139))
      | ~ r2_hidden(C_140,k2_relat_1(A_139))
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(resolution,[status(thm)],[c_242,c_1277])).

tff(c_1287,plain,(
    ! [C_327,A_328,A_329] :
      ( r2_hidden(C_327,A_328)
      | ~ v5_relat_1(A_329,'#skF_8')
      | ~ r2_hidden(C_327,k2_relat_1(A_329))
      | ~ v1_funct_1(A_329)
      | ~ v1_relat_1(A_329) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1280])).

tff(c_1420,plain,(
    ! [A_339,B_340,A_341] :
      ( r2_hidden('#skF_2'(A_339,B_340),A_341)
      | ~ v5_relat_1(A_339,'#skF_8')
      | r2_hidden('#skF_4'(A_339,B_340),B_340)
      | k2_relat_1(A_339) = B_340
      | ~ v1_funct_1(A_339)
      | ~ v1_relat_1(A_339) ) ),
    inference(resolution,[status(thm)],[c_1038,c_1287])).

tff(c_1452,plain,(
    ! [A_342,A_343] :
      ( ~ v5_relat_1(A_342,'#skF_8')
      | r2_hidden('#skF_4'(A_342,A_343),A_343)
      | k2_relat_1(A_342) = A_343
      | ~ v1_funct_1(A_342)
      | ~ v1_relat_1(A_342) ) ),
    inference(resolution,[status(thm)],[c_1420,c_30])).

tff(c_1476,plain,(
    ! [A_346,A_347,B_348] :
      ( r2_hidden('#skF_4'(A_346,A_347),B_348)
      | ~ r1_tarski(A_347,B_348)
      | ~ v5_relat_1(A_346,'#skF_8')
      | k2_relat_1(A_346) = A_347
      | ~ v1_funct_1(A_346)
      | ~ v1_relat_1(A_346) ) ),
    inference(resolution,[status(thm)],[c_1452,c_2])).

tff(c_1651,plain,(
    ! [A_382,A_383,B_384,B_385] :
      ( r2_hidden('#skF_4'(A_382,A_383),B_384)
      | ~ r1_tarski(B_385,B_384)
      | ~ r1_tarski(A_383,B_385)
      | ~ v5_relat_1(A_382,'#skF_8')
      | k2_relat_1(A_382) = A_383
      | ~ v1_funct_1(A_382)
      | ~ v1_relat_1(A_382) ) ),
    inference(resolution,[status(thm)],[c_1476,c_2])).

tff(c_2885,plain,(
    ! [A_567,A_568,A_569,B_570] :
      ( r2_hidden('#skF_4'(A_567,A_568),A_569)
      | ~ r1_tarski(A_568,k2_relat_1(B_570))
      | ~ v5_relat_1(A_567,'#skF_8')
      | k2_relat_1(A_567) = A_568
      | ~ v1_funct_1(A_567)
      | ~ v1_relat_1(A_567)
      | ~ v5_relat_1(B_570,A_569)
      | ~ v1_relat_1(B_570) ) ),
    inference(resolution,[status(thm)],[c_14,c_1651])).

tff(c_2906,plain,(
    ! [A_571,A_572,B_573] :
      ( r2_hidden('#skF_4'(A_571,'#skF_8'),A_572)
      | ~ v5_relat_1(A_571,'#skF_8')
      | k2_relat_1(A_571) = '#skF_8'
      | ~ v1_funct_1(A_571)
      | ~ v1_relat_1(A_571)
      | ~ v5_relat_1(B_573,A_572)
      | ~ v1_relat_1(B_573) ) ),
    inference(resolution,[status(thm)],[c_397,c_2885])).

tff(c_2908,plain,(
    ! [A_571,A_156] :
      ( r2_hidden('#skF_4'(A_571,'#skF_8'),A_156)
      | ~ v5_relat_1(A_571,'#skF_8')
      | k2_relat_1(A_571) = '#skF_8'
      | ~ v1_funct_1(A_571)
      | ~ v1_relat_1(A_571)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_323,c_2906])).

tff(c_2913,plain,(
    ! [A_571,A_156] :
      ( r2_hidden('#skF_4'(A_571,'#skF_8'),A_156)
      | ~ v5_relat_1(A_571,'#skF_8')
      | k2_relat_1(A_571) = '#skF_8'
      | ~ v1_funct_1(A_571)
      | ~ v1_relat_1(A_571) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2908])).

tff(c_531,plain,(
    ! [A_183,B_184,D_185] :
      ( r2_hidden('#skF_3'(A_183,B_184),k1_relat_1(A_183))
      | k1_funct_1(A_183,D_185) != '#skF_4'(A_183,B_184)
      | ~ r2_hidden(D_185,k1_relat_1(A_183))
      | k2_relat_1(A_183) = B_184
      | ~ v1_funct_1(A_183)
      | ~ v1_relat_1(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_537,plain,(
    ! [A_14,B_184,C_50] :
      ( r2_hidden('#skF_3'(A_14,B_184),k1_relat_1(A_14))
      | C_50 != '#skF_4'(A_14,B_184)
      | ~ r2_hidden('#skF_5'(A_14,k2_relat_1(A_14),C_50),k1_relat_1(A_14))
      | k2_relat_1(A_14) = B_184
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14)
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_531])).

tff(c_2927,plain,(
    ! [A_576,B_577] :
      ( r2_hidden('#skF_3'(A_576,B_577),k1_relat_1(A_576))
      | ~ r2_hidden('#skF_5'(A_576,k2_relat_1(A_576),'#skF_4'(A_576,B_577)),k1_relat_1(A_576))
      | k2_relat_1(A_576) = B_577
      | ~ v1_funct_1(A_576)
      | ~ v1_relat_1(A_576)
      | ~ r2_hidden('#skF_4'(A_576,B_577),k2_relat_1(A_576))
      | ~ v1_funct_1(A_576)
      | ~ v1_relat_1(A_576) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_537])).

tff(c_2939,plain,(
    ! [A_139,B_577] :
      ( r2_hidden('#skF_3'(A_139,B_577),k1_relat_1(A_139))
      | k2_relat_1(A_139) = B_577
      | ~ r1_tarski(k1_relat_1(A_139),k1_relat_1(A_139))
      | ~ r2_hidden('#skF_4'(A_139,B_577),k2_relat_1(A_139))
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(resolution,[status(thm)],[c_242,c_2927])).

tff(c_2950,plain,(
    ! [A_578,B_579] :
      ( r2_hidden('#skF_3'(A_578,B_579),k1_relat_1(A_578))
      | k2_relat_1(A_578) = B_579
      | ~ r2_hidden('#skF_4'(A_578,B_579),k2_relat_1(A_578))
      | ~ v1_funct_1(A_578)
      | ~ v1_relat_1(A_578) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2939])).

tff(c_2954,plain,(
    ! [A_580,B_581,B_582] :
      ( r2_hidden('#skF_3'(A_580,B_581),B_582)
      | ~ r1_tarski(k1_relat_1(A_580),B_582)
      | k2_relat_1(A_580) = B_581
      | ~ r2_hidden('#skF_4'(A_580,B_581),k2_relat_1(A_580))
      | ~ v1_funct_1(A_580)
      | ~ v1_relat_1(A_580) ) ),
    inference(resolution,[status(thm)],[c_2950,c_2])).

tff(c_3101,plain,(
    ! [A_571,B_582] :
      ( r2_hidden('#skF_3'(A_571,'#skF_8'),B_582)
      | ~ r1_tarski(k1_relat_1(A_571),B_582)
      | ~ v5_relat_1(A_571,'#skF_8')
      | k2_relat_1(A_571) = '#skF_8'
      | ~ v1_funct_1(A_571)
      | ~ v1_relat_1(A_571) ) ),
    inference(resolution,[status(thm)],[c_2913,c_2954])).

tff(c_580,plain,(
    ! [A_200,B_201,D_202] :
      ( k1_funct_1(A_200,'#skF_3'(A_200,B_201)) = '#skF_2'(A_200,B_201)
      | k1_funct_1(A_200,D_202) != '#skF_4'(A_200,B_201)
      | ~ r2_hidden(D_202,k1_relat_1(A_200))
      | k2_relat_1(A_200) = B_201
      | ~ v1_funct_1(A_200)
      | ~ v1_relat_1(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_586,plain,(
    ! [A_14,B_201,C_50] :
      ( k1_funct_1(A_14,'#skF_3'(A_14,B_201)) = '#skF_2'(A_14,B_201)
      | C_50 != '#skF_4'(A_14,B_201)
      | ~ r2_hidden('#skF_5'(A_14,k2_relat_1(A_14),C_50),k1_relat_1(A_14))
      | k2_relat_1(A_14) = B_201
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14)
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_580])).

tff(c_3248,plain,(
    ! [A_596,B_597] :
      ( k1_funct_1(A_596,'#skF_3'(A_596,B_597)) = '#skF_2'(A_596,B_597)
      | ~ r2_hidden('#skF_5'(A_596,k2_relat_1(A_596),'#skF_4'(A_596,B_597)),k1_relat_1(A_596))
      | k2_relat_1(A_596) = B_597
      | ~ v1_funct_1(A_596)
      | ~ v1_relat_1(A_596)
      | ~ r2_hidden('#skF_4'(A_596,B_597),k2_relat_1(A_596))
      | ~ v1_funct_1(A_596)
      | ~ v1_relat_1(A_596) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_586])).

tff(c_3324,plain,(
    ! [A_609,B_610] :
      ( k1_funct_1(A_609,'#skF_3'(A_609,B_610)) = '#skF_2'(A_609,B_610)
      | k2_relat_1(A_609) = B_610
      | ~ r2_hidden('#skF_4'(A_609,B_610),k2_relat_1(A_609))
      | ~ v1_funct_1(A_609)
      | ~ v1_relat_1(A_609) ) ),
    inference(resolution,[status(thm)],[c_22,c_3248])).

tff(c_3490,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1198,c_3324])).

tff(c_3578,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_3490])).

tff(c_3579,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_3578])).

tff(c_712,plain,(
    ! [B_236,A_237,B_238,B_239] :
      ( r2_hidden(k1_funct_1(B_236,A_237),B_238)
      | ~ r1_tarski(B_239,B_238)
      | ~ r1_tarski(k2_relat_1(B_236),B_239)
      | ~ r2_hidden(A_237,k1_relat_1(B_236))
      | ~ v1_funct_1(B_236)
      | ~ v1_relat_1(B_236) ) ),
    inference(resolution,[status(thm)],[c_590,c_2])).

tff(c_1785,plain,(
    ! [B_415,A_416,A_417,B_418] :
      ( r2_hidden(k1_funct_1(B_415,A_416),A_417)
      | ~ r1_tarski(k2_relat_1(B_415),k2_relat_1(B_418))
      | ~ r2_hidden(A_416,k1_relat_1(B_415))
      | ~ v1_funct_1(B_415)
      | ~ v1_relat_1(B_415)
      | ~ v5_relat_1(B_418,A_417)
      | ~ v1_relat_1(B_418) ) ),
    inference(resolution,[status(thm)],[c_14,c_712])).

tff(c_1803,plain,(
    ! [B_415,A_416,A_417] :
      ( r2_hidden(k1_funct_1(B_415,A_416),A_417)
      | ~ r2_hidden(A_416,k1_relat_1(B_415))
      | ~ v1_funct_1(B_415)
      | ~ v5_relat_1(B_415,A_417)
      | ~ v1_relat_1(B_415) ) ),
    inference(resolution,[status(thm)],[c_94,c_1785])).

tff(c_3603,plain,(
    ! [A_417] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_8'),A_417)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_417)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3579,c_1803])).

tff(c_3632,plain,(
    ! [A_417] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_8'),A_417)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_323,c_64,c_3603])).

tff(c_3646,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_3632])).

tff(c_3650,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8'))
    | ~ v5_relat_1('#skF_8','#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_3101,c_3646])).

tff(c_3695,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_323,c_94,c_3650])).

tff(c_3697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_3695])).

tff(c_3700,plain,(
    ! [A_615] : r2_hidden('#skF_2'('#skF_8','#skF_8'),A_615) ),
    inference(splitRight,[status(thm)],[c_3632])).

tff(c_24,plain,(
    ! [A_14,B_36,D_49] :
      ( ~ r2_hidden('#skF_2'(A_14,B_36),B_36)
      | k1_funct_1(A_14,D_49) != '#skF_4'(A_14,B_36)
      | ~ r2_hidden(D_49,k1_relat_1(A_14))
      | k2_relat_1(A_14) = B_36
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3709,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_8'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3700,c_24])).

tff(c_3722,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_3709])).

tff(c_3733,plain,(
    ! [D_616] :
      ( k1_funct_1('#skF_8',D_616) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_616,k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_404,c_3722])).

tff(c_4084,plain,(
    ! [C_50] :
      ( k1_funct_1('#skF_8','#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_50)) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(C_50,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_22,c_3733])).

tff(c_4759,plain,(
    ! [C_628] :
      ( k1_funct_1('#skF_8','#skF_5'('#skF_8',k2_relat_1('#skF_8'),C_628)) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(C_628,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_4084])).

tff(c_4763,plain,(
    ! [C_50] :
      ( C_50 != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(C_50,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_50,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_4759])).

tff(c_4768,plain,(
    ! [C_630] :
      ( C_630 != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(C_630,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_4763])).

tff(c_5192,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_1198,c_4768])).

tff(c_5200,plain,(
    ! [D_631] :
      ( r2_hidden(D_631,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_631,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_5213,plain,(
    ! [D_633,B_634] :
      ( r2_hidden(D_633,B_634)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_634)
      | ~ r2_hidden(D_633,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5200,c_2])).

tff(c_5216,plain,(
    ! [D_633,A_10] :
      ( r2_hidden(D_633,A_10)
      | ~ r2_hidden(D_633,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_10)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14,c_5213])).

tff(c_5222,plain,(
    ! [D_633,A_10] :
      ( r2_hidden(D_633,A_10)
      | ~ r2_hidden(D_633,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5216])).

tff(c_6757,plain,(
    ! [B_811,B_812,A_813] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_811),B_812),A_813)
      | ~ v5_relat_1('#skF_8',A_813)
      | r1_tarski(k2_relat_1(B_811),B_812)
      | ~ v5_relat_1(B_811,'#skF_7')
      | ~ v1_relat_1(B_811) ) ),
    inference(resolution,[status(thm)],[c_6398,c_5222])).

tff(c_6782,plain,(
    ! [A_813,B_811] :
      ( ~ v5_relat_1('#skF_8',A_813)
      | r1_tarski(k2_relat_1(B_811),A_813)
      | ~ v5_relat_1(B_811,'#skF_7')
      | ~ v1_relat_1(B_811) ) ),
    inference(resolution,[status(thm)],[c_6757,c_4])).

tff(c_6171,plain,(
    ! [B_742,A_743,C_744] :
      ( k1_xboole_0 = B_742
      | k1_relset_1(A_743,B_742,C_744) = A_743
      | ~ v1_funct_2(C_744,A_743,B_742)
      | ~ m1_subset_1(C_744,k1_zfmisc_1(k2_zfmisc_1(A_743,B_742))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6174,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_6171])).

tff(c_6177,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_148,c_6174])).

tff(c_6178,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6177])).

tff(c_6256,plain,(
    ! [A_751,B_752] :
      ( r2_hidden('#skF_3'(A_751,B_752),k1_relat_1(A_751))
      | r2_hidden('#skF_4'(A_751,B_752),B_752)
      | k2_relat_1(A_751) = B_752
      | ~ v1_funct_1(A_751)
      | ~ v1_relat_1(A_751) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6265,plain,(
    ! [A_751,B_752,B_2] :
      ( r2_hidden('#skF_3'(A_751,B_752),B_2)
      | ~ r1_tarski(k1_relat_1(A_751),B_2)
      | r2_hidden('#skF_4'(A_751,B_752),B_752)
      | k2_relat_1(A_751) = B_752
      | ~ v1_funct_1(A_751)
      | ~ v1_relat_1(A_751) ) ),
    inference(resolution,[status(thm)],[c_6256,c_2])).

tff(c_32,plain,(
    ! [A_14,B_36] :
      ( k1_funct_1(A_14,'#skF_3'(A_14,B_36)) = '#skF_2'(A_14,B_36)
      | r2_hidden('#skF_4'(A_14,B_36),B_36)
      | k2_relat_1(A_14) = B_36
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6948,plain,(
    ! [A_827,B_828,D_829] :
      ( k1_funct_1(A_827,'#skF_3'(A_827,B_828)) = '#skF_2'(A_827,B_828)
      | k1_funct_1(A_827,D_829) != '#skF_4'(A_827,B_828)
      | ~ r2_hidden(D_829,k1_relat_1(A_827))
      | k2_relat_1(A_827) = B_828
      | ~ v1_funct_1(A_827)
      | ~ v1_relat_1(A_827) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6954,plain,(
    ! [B_828,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_828)) = '#skF_2'('#skF_8',B_828)
      | D_71 != '#skF_4'('#skF_8',B_828)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_828
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6948])).

tff(c_6956,plain,(
    ! [B_828,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_828)) = '#skF_2'('#skF_8',B_828)
      | D_71 != '#skF_4'('#skF_8',B_828)
      | ~ r2_hidden('#skF_9'(D_71),'#skF_6')
      | k2_relat_1('#skF_8') = B_828
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_6178,c_6954])).

tff(c_7293,plain,(
    ! [B_875] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_875)) = '#skF_2'('#skF_8',B_875)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_875)),'#skF_6')
      | k2_relat_1('#skF_8') = B_875
      | ~ r2_hidden('#skF_4'('#skF_8',B_875),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6956])).

tff(c_7296,plain,(
    ! [B_875] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_875)) = '#skF_2'('#skF_8',B_875)
      | k2_relat_1('#skF_8') = B_875
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden('#skF_4'('#skF_8',B_875),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_113,c_7293])).

tff(c_7337,plain,(
    ! [B_878] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_878)) = '#skF_2'('#skF_8',B_878)
      | k2_relat_1('#skF_8') = B_878
      | ~ r2_hidden('#skF_4'('#skF_8',B_878),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_7296])).

tff(c_7351,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_7337])).

tff(c_7362,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_7351])).

tff(c_7363,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_7362])).

tff(c_7375,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_7363,c_36])).

tff(c_7386,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_6178,c_7375])).

tff(c_7388,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_7386])).

tff(c_7394,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
    | r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_6265,c_7388])).

tff(c_7422,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_94,c_6178,c_7394])).

tff(c_7423,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_7422])).

tff(c_6725,plain,(
    ! [A_804,B_805,D_806] :
      ( r2_hidden('#skF_3'(A_804,B_805),k1_relat_1(A_804))
      | k1_funct_1(A_804,D_806) != '#skF_4'(A_804,B_805)
      | ~ r2_hidden(D_806,k1_relat_1(A_804))
      | k2_relat_1(A_804) = B_805
      | ~ v1_funct_1(A_804)
      | ~ v1_relat_1(A_804) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6731,plain,(
    ! [B_805,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_805),k1_relat_1('#skF_8'))
      | D_71 != '#skF_4'('#skF_8',B_805)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_805
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6725])).

tff(c_6733,plain,(
    ! [B_805,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_805),'#skF_6')
      | D_71 != '#skF_4'('#skF_8',B_805)
      | ~ r2_hidden('#skF_9'(D_71),'#skF_6')
      | k2_relat_1('#skF_8') = B_805
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_6178,c_6178,c_6731])).

tff(c_7051,plain,(
    ! [B_839] :
      ( r2_hidden('#skF_3'('#skF_8',B_839),'#skF_6')
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_839)),'#skF_6')
      | k2_relat_1('#skF_8') = B_839
      | ~ r2_hidden('#skF_4'('#skF_8',B_839),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_6733])).

tff(c_7054,plain,(
    ! [B_839] :
      ( r2_hidden('#skF_3'('#skF_8',B_839),'#skF_6')
      | k2_relat_1('#skF_8') = B_839
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden('#skF_4'('#skF_8',B_839),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_113,c_7051])).

tff(c_7060,plain,(
    ! [B_839] :
      ( r2_hidden('#skF_3'('#skF_8',B_839),'#skF_6')
      | k2_relat_1('#skF_8') = B_839
      | ~ r2_hidden('#skF_4'('#skF_8',B_839),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_7054])).

tff(c_7406,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_7060,c_7388])).

tff(c_7437,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_7406])).

tff(c_7510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7423,c_7437])).

tff(c_7511,plain,(
    r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_7386])).

tff(c_7531,plain,(
    ! [B_883] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_883)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_883) ) ),
    inference(resolution,[status(thm)],[c_7511,c_2])).

tff(c_7541,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_7531,c_30])).

tff(c_7554,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_7541])).

tff(c_7555,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_7554])).

tff(c_7605,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_7555])).

tff(c_7608,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_6782,c_7605])).

tff(c_7618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_119,c_7608])).

tff(c_7620,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_7555])).

tff(c_7537,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_7531,c_24])).

tff(c_7550,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_49,'#skF_6')
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_6178,c_7537])).

tff(c_7551,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_49,'#skF_6')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_7550])).

tff(c_7857,plain,(
    ! [D_895] :
      ( k1_funct_1('#skF_8',D_895) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_895,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7620,c_7551])).

tff(c_7985,plain,(
    ! [D_71] :
      ( k1_funct_1('#skF_8','#skF_9'(D_71)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_113,c_7857])).

tff(c_8075,plain,(
    ! [D_900] :
      ( k1_funct_1('#skF_8','#skF_9'(D_900)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_900,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_7985])).

tff(c_8079,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_8075])).

tff(c_7619,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_7555])).

tff(c_8081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8079,c_7619])).

tff(c_8082,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6177])).

tff(c_5350,plain,(
    ! [A_654,B_655,A_656] :
      ( r2_hidden('#skF_1'(A_654,B_655),A_656)
      | ~ r1_tarski(A_654,k1_xboole_0)
      | r1_tarski(A_654,B_655) ) ),
    inference(resolution,[status(thm)],[c_8,c_5318])).

tff(c_5368,plain,(
    ! [A_657,A_658] :
      ( ~ r1_tarski(A_657,k1_xboole_0)
      | r1_tarski(A_657,A_658) ) ),
    inference(resolution,[status(thm)],[c_5350,c_4])).

tff(c_5384,plain,(
    ! [B_661,A_662] :
      ( r1_tarski(k2_relat_1(B_661),A_662)
      | ~ v5_relat_1(B_661,k1_xboole_0)
      | ~ v1_relat_1(B_661) ) ),
    inference(resolution,[status(thm)],[c_14,c_5368])).

tff(c_5207,plain,(
    ! [D_631,B_2] :
      ( r2_hidden(D_631,B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r2_hidden(D_631,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5200,c_2])).

tff(c_5392,plain,(
    ! [D_631,A_662] :
      ( r2_hidden(D_631,A_662)
      | ~ r2_hidden(D_631,'#skF_7')
      | ~ v5_relat_1('#skF_8',k1_xboole_0)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_5384,c_5207])).

tff(c_5402,plain,(
    ! [D_631,A_662] :
      ( r2_hidden(D_631,A_662)
      | ~ r2_hidden(D_631,'#skF_7')
      | ~ v5_relat_1('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5392])).

tff(c_5406,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_5402])).

tff(c_8088,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8082,c_5406])).

tff(c_8100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_8088])).

tff(c_8102,plain,(
    v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5402])).

tff(c_5404,plain,(
    ! [B_661,A_662] :
      ( v5_relat_1(B_661,A_662)
      | ~ v5_relat_1(B_661,k1_xboole_0)
      | ~ v1_relat_1(B_661) ) ),
    inference(resolution,[status(thm)],[c_5384,c_12])).

tff(c_8104,plain,(
    ! [A_662] :
      ( v5_relat_1('#skF_8',A_662)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_8102,c_5404])).

tff(c_8110,plain,(
    ! [A_662] : v5_relat_1('#skF_8',A_662) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8104])).

tff(c_8389,plain,(
    ! [A_944,B_945,A_946,B_947] :
      ( r2_hidden('#skF_1'(A_944,B_945),A_946)
      | ~ r1_tarski(A_944,k2_relat_1(B_947))
      | r1_tarski(A_944,B_945)
      | ~ v5_relat_1(B_947,A_946)
      | ~ v1_relat_1(B_947) ) ),
    inference(resolution,[status(thm)],[c_14,c_5318])).

tff(c_8828,plain,(
    ! [B_1027,B_1028,A_1029,B_1030] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_1027),B_1028),A_1029)
      | r1_tarski(k2_relat_1(B_1027),B_1028)
      | ~ v5_relat_1(B_1030,A_1029)
      | ~ v1_relat_1(B_1030)
      | ~ v5_relat_1(B_1027,k2_relat_1(B_1030))
      | ~ v1_relat_1(B_1027) ) ),
    inference(resolution,[status(thm)],[c_14,c_8389])).

tff(c_8830,plain,(
    ! [B_1027,B_1028,A_662] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_1027),B_1028),A_662)
      | r1_tarski(k2_relat_1(B_1027),B_1028)
      | ~ v1_relat_1('#skF_8')
      | ~ v5_relat_1(B_1027,k2_relat_1('#skF_8'))
      | ~ v1_relat_1(B_1027) ) ),
    inference(resolution,[status(thm)],[c_8110,c_8828])).

tff(c_8840,plain,(
    ! [B_1031,B_1032,A_1033] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_1031),B_1032),A_1033)
      | r1_tarski(k2_relat_1(B_1031),B_1032)
      | ~ v5_relat_1(B_1031,k2_relat_1('#skF_8'))
      | ~ v1_relat_1(B_1031) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8830])).

tff(c_8858,plain,(
    ! [B_1034,A_1035] :
      ( r1_tarski(k2_relat_1(B_1034),A_1035)
      | ~ v5_relat_1(B_1034,k2_relat_1('#skF_8'))
      | ~ v1_relat_1(B_1034) ) ),
    inference(resolution,[status(thm)],[c_8840,c_4])).

tff(c_8861,plain,(
    ! [A_1035] :
      ( r1_tarski(k2_relat_1('#skF_8'),A_1035)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_8110,c_8858])).

tff(c_8869,plain,(
    ! [A_1035] : r1_tarski(k2_relat_1('#skF_8'),A_1035) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8861])).

tff(c_8293,plain,(
    ! [B_926,A_927,C_928] :
      ( k1_xboole_0 = B_926
      | k1_relset_1(A_927,B_926,C_928) = A_927
      | ~ v1_funct_2(C_928,A_927,B_926)
      | ~ m1_subset_1(C_928,k1_zfmisc_1(k2_zfmisc_1(A_927,B_926))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8296,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_8293])).

tff(c_8299,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_148,c_8296])).

tff(c_8300,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_8299])).

tff(c_8453,plain,(
    ! [A_954,B_955] :
      ( r2_hidden('#skF_3'(A_954,B_955),k1_relat_1(A_954))
      | r2_hidden('#skF_4'(A_954,B_955),B_955)
      | k2_relat_1(A_954) = B_955
      | ~ v1_funct_1(A_954)
      | ~ v1_relat_1(A_954) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8461,plain,(
    ! [B_955] :
      ( r2_hidden('#skF_3'('#skF_8',B_955),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_955),B_955)
      | k2_relat_1('#skF_8') = B_955
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8300,c_8453])).

tff(c_8466,plain,(
    ! [B_956] :
      ( r2_hidden('#skF_3'('#skF_8',B_956),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_956),B_956)
      | k2_relat_1('#skF_8') = B_956 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_8461])).

tff(c_8472,plain,(
    ! [B_956,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_956),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | r2_hidden('#skF_4'('#skF_8',B_956),B_956)
      | k2_relat_1('#skF_8') = B_956 ) ),
    inference(resolution,[status(thm)],[c_8466,c_2])).

tff(c_8610,plain,(
    ! [A_982,B_983] :
      ( k1_funct_1(A_982,'#skF_3'(A_982,B_983)) = '#skF_2'(A_982,B_983)
      | r2_hidden('#skF_4'(A_982,B_983),B_983)
      | k2_relat_1(A_982) = B_983
      | ~ v1_funct_1(A_982)
      | ~ v1_relat_1(A_982) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9418,plain,(
    ! [A_1085,B_1086] :
      ( r2_hidden('#skF_2'(A_1085,B_1086),k2_relat_1(A_1085))
      | ~ r2_hidden('#skF_3'(A_1085,B_1086),k1_relat_1(A_1085))
      | ~ v1_funct_1(A_1085)
      | ~ v1_relat_1(A_1085)
      | r2_hidden('#skF_4'(A_1085,B_1086),B_1086)
      | k2_relat_1(A_1085) = B_1086
      | ~ v1_funct_1(A_1085)
      | ~ v1_relat_1(A_1085) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8610,c_36])).

tff(c_9441,plain,(
    ! [B_956] :
      ( r2_hidden('#skF_2'('#skF_8',B_956),k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | r2_hidden('#skF_4'('#skF_8',B_956),B_956)
      | k2_relat_1('#skF_8') = B_956 ) ),
    inference(resolution,[status(thm)],[c_8472,c_9418])).

tff(c_9471,plain,(
    ! [B_1087] :
      ( r2_hidden('#skF_2'('#skF_8',B_1087),k2_relat_1('#skF_8'))
      | r2_hidden('#skF_4'('#skF_8',B_1087),B_1087)
      | k2_relat_1('#skF_8') = B_1087 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_8300,c_88,c_64,c_9441])).

tff(c_9482,plain,(
    ! [B_1087,B_2] :
      ( r2_hidden('#skF_2'('#skF_8',B_1087),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | r2_hidden('#skF_4'('#skF_8',B_1087),B_1087)
      | k2_relat_1('#skF_8') = B_1087 ) ),
    inference(resolution,[status(thm)],[c_9471,c_2])).

tff(c_9500,plain,(
    ! [B_1088,B_1089] :
      ( r2_hidden('#skF_2'('#skF_8',B_1088),B_1089)
      | r2_hidden('#skF_4'('#skF_8',B_1088),B_1088)
      | k2_relat_1('#skF_8') = B_1088 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8869,c_9482])).

tff(c_9510,plain,(
    ! [B_1089] :
      ( ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | r2_hidden('#skF_4'('#skF_8',B_1089),B_1089)
      | k2_relat_1('#skF_8') = B_1089 ) ),
    inference(resolution,[status(thm)],[c_9500,c_30])).

tff(c_9534,plain,(
    ! [B_1090] :
      ( r2_hidden('#skF_4'('#skF_8',B_1090),B_1090)
      | k2_relat_1('#skF_8') = B_1090 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_9510])).

tff(c_8101,plain,(
    ! [D_631,A_662] :
      ( r2_hidden(D_631,A_662)
      | ~ r2_hidden(D_631,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_5402])).

tff(c_9540,plain,(
    ! [A_662] :
      ( r2_hidden('#skF_4'('#skF_8','#skF_7'),A_662)
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_9534,c_8101])).

tff(c_9547,plain,(
    ! [A_662] : r2_hidden('#skF_4'('#skF_8','#skF_7'),A_662) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_9540])).

tff(c_8874,plain,(
    ! [A_1036,B_1037,D_1038] :
      ( r2_hidden('#skF_3'(A_1036,B_1037),k1_relat_1(A_1036))
      | k1_funct_1(A_1036,D_1038) != '#skF_4'(A_1036,B_1037)
      | ~ r2_hidden(D_1038,k1_relat_1(A_1036))
      | k2_relat_1(A_1036) = B_1037
      | ~ v1_funct_1(A_1036)
      | ~ v1_relat_1(A_1036) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8882,plain,(
    ! [B_1037,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_1037),k1_relat_1('#skF_8'))
      | D_71 != '#skF_4'('#skF_8',B_1037)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1037
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_8874])).

tff(c_8884,plain,(
    ! [B_1037,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_1037),'#skF_6')
      | D_71 != '#skF_4'('#skF_8',B_1037)
      | ~ r2_hidden('#skF_9'(D_71),'#skF_6')
      | k2_relat_1('#skF_8') = B_1037
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_8300,c_8300,c_8882])).

tff(c_9349,plain,(
    ! [B_1075] :
      ( r2_hidden('#skF_3'('#skF_8',B_1075),'#skF_6')
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1075)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1075
      | ~ r2_hidden('#skF_4'('#skF_8',B_1075),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_8884])).

tff(c_9352,plain,(
    ! [B_1075] :
      ( r2_hidden('#skF_3'('#skF_8',B_1075),'#skF_6')
      | k2_relat_1('#skF_8') = B_1075
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden('#skF_4'('#skF_8',B_1075),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_113,c_9349])).

tff(c_9360,plain,(
    ! [B_1076] :
      ( r2_hidden('#skF_3'('#skF_8',B_1076),'#skF_6')
      | k2_relat_1('#skF_8') = B_1076
      | ~ r2_hidden('#skF_4'('#skF_8',B_1076),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_9352])).

tff(c_9363,plain,(
    ! [B_1076,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_1076),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | k2_relat_1('#skF_8') = B_1076
      | ~ r2_hidden('#skF_4'('#skF_8',B_1076),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_9360,c_2])).

tff(c_9008,plain,(
    ! [A_1049,B_1050,D_1051] :
      ( k1_funct_1(A_1049,'#skF_3'(A_1049,B_1050)) = '#skF_2'(A_1049,B_1050)
      | k1_funct_1(A_1049,D_1051) != '#skF_4'(A_1049,B_1050)
      | ~ r2_hidden(D_1051,k1_relat_1(A_1049))
      | k2_relat_1(A_1049) = B_1050
      | ~ v1_funct_1(A_1049)
      | ~ v1_relat_1(A_1049) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9016,plain,(
    ! [B_1050,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1050)) = '#skF_2'('#skF_8',B_1050)
      | D_71 != '#skF_4'('#skF_8',B_1050)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1050
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_9008])).

tff(c_9018,plain,(
    ! [B_1050,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1050)) = '#skF_2'('#skF_8',B_1050)
      | D_71 != '#skF_4'('#skF_8',B_1050)
      | ~ r2_hidden('#skF_9'(D_71),'#skF_6')
      | k2_relat_1('#skF_8') = B_1050
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_8300,c_9016])).

tff(c_9639,plain,(
    ! [B_1106] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1106)) = '#skF_2'('#skF_8',B_1106)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1106)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1106
      | ~ r2_hidden('#skF_4'('#skF_8',B_1106),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_9018])).

tff(c_9642,plain,(
    ! [B_1106] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1106)) = '#skF_2'('#skF_8',B_1106)
      | k2_relat_1('#skF_8') = B_1106
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden('#skF_4'('#skF_8',B_1106),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_113,c_9639])).

tff(c_9650,plain,(
    ! [B_1107] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1107)) = '#skF_2'('#skF_8',B_1107)
      | k2_relat_1('#skF_8') = B_1107
      | ~ r2_hidden('#skF_4'('#skF_8',B_1107),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_9642])).

tff(c_9690,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_9650])).

tff(c_9712,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_9690])).

tff(c_9713,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_9712])).

tff(c_8373,plain,(
    ! [B_941,A_942,B_943] :
      ( r2_hidden(k1_funct_1(B_941,A_942),B_943)
      | ~ r1_tarski(k2_relat_1(B_941),B_943)
      | ~ r2_hidden(A_942,k1_relat_1(B_941))
      | ~ v1_funct_1(B_941)
      | ~ v1_relat_1(B_941) ) ),
    inference(resolution,[status(thm)],[c_169,c_2])).

tff(c_8727,plain,(
    ! [B_1009,A_1010,B_1011,B_1012] :
      ( r2_hidden(k1_funct_1(B_1009,A_1010),B_1011)
      | ~ r1_tarski(B_1012,B_1011)
      | ~ r1_tarski(k2_relat_1(B_1009),B_1012)
      | ~ r2_hidden(A_1010,k1_relat_1(B_1009))
      | ~ v1_funct_1(B_1009)
      | ~ v1_relat_1(B_1009) ) ),
    inference(resolution,[status(thm)],[c_8373,c_2])).

tff(c_8745,plain,(
    ! [B_1009,A_1010,A_6] :
      ( r2_hidden(k1_funct_1(B_1009,A_1010),A_6)
      | ~ r1_tarski(k2_relat_1(B_1009),k1_xboole_0)
      | ~ r2_hidden(A_1010,k1_relat_1(B_1009))
      | ~ v1_funct_1(B_1009)
      | ~ v1_relat_1(B_1009) ) ),
    inference(resolution,[status(thm)],[c_8,c_8727])).

tff(c_9732,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),A_6)
      | ~ r1_tarski(k2_relat_1('#skF_8'),k1_xboole_0)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9713,c_8745])).

tff(c_9757,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),A_6)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_8300,c_8869,c_9732])).

tff(c_9773,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_9757])).

tff(c_9776,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_9363,c_9773])).

tff(c_9785,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9547,c_94,c_9776])).

tff(c_9787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_9785])).

tff(c_9790,plain,(
    ! [A_1111] : r2_hidden('#skF_2'('#skF_8','#skF_7'),A_1111) ),
    inference(splitRight,[status(thm)],[c_9757])).

tff(c_9796,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_9790,c_24])).

tff(c_9810,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_49,'#skF_6')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_8300,c_9796])).

tff(c_9842,plain,(
    ! [D_1113] :
      ( k1_funct_1('#skF_8',D_1113) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1113,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_9810])).

tff(c_10007,plain,(
    ! [D_1117] :
      ( k1_funct_1('#skF_8','#skF_9'(D_1117)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1117,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_9842])).

tff(c_10021,plain,(
    ! [D_1121] :
      ( D_1121 != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1121,'#skF_7')
      | ~ r2_hidden(D_1121,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_10007])).

tff(c_10042,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_9547,c_10021])).

tff(c_10114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9547,c_10042])).

tff(c_10115,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_8299])).

tff(c_10136,plain,(
    ! [C_1124,A_1125] :
      ( C_1124 = '#skF_7'
      | ~ v1_funct_2(C_1124,A_1125,'#skF_7')
      | A_1125 = '#skF_7'
      | ~ m1_subset_1(C_1124,k1_zfmisc_1(k2_zfmisc_1(A_1125,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10115,c_10115,c_10115,c_10115,c_48])).

tff(c_10139,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_60,c_10136])).

tff(c_10142,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_10139])).

tff(c_10143,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_10142])).

tff(c_5225,plain,(
    ! [D_637,A_638] :
      ( r2_hidden(D_637,A_638)
      | ~ r2_hidden(D_637,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_638) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_5216])).

tff(c_5236,plain,(
    ! [D_71,A_638] :
      ( r2_hidden('#skF_9'(D_71),A_638)
      | ~ v5_relat_1('#skF_8',A_638)
      | ~ r1_tarski('#skF_6','#skF_7')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_113,c_5225])).

tff(c_5252,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_5236])).

tff(c_10166,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10143,c_5252])).

tff(c_10180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_10166])).

tff(c_10181,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_10142])).

tff(c_112,plain,(
    ! [A_1,B_2,B_90] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_90)
      | ~ r1_tarski(A_1,B_90)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_8163,plain,(
    ! [D_905,A_906] :
      ( r2_hidden(D_905,A_906)
      | ~ r2_hidden(D_905,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_5402])).

tff(c_8189,plain,(
    ! [A_910,B_911,A_912] :
      ( r2_hidden('#skF_1'(A_910,B_911),A_912)
      | ~ r1_tarski(A_910,'#skF_7')
      | r1_tarski(A_910,B_911) ) ),
    inference(resolution,[status(thm)],[c_112,c_8163])).

tff(c_8206,plain,(
    ! [A_910,A_912] :
      ( ~ r1_tarski(A_910,'#skF_7')
      | r1_tarski(A_910,A_912) ) ),
    inference(resolution,[status(thm)],[c_8189,c_4])).

tff(c_10292,plain,(
    ! [A_1137,A_1138] :
      ( ~ r1_tarski(A_1137,'#skF_8')
      | r1_tarski(A_1137,A_1138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10181,c_8206])).

tff(c_10304,plain,(
    ! [B_11,A_1138] :
      ( r1_tarski(k2_relat_1(B_11),A_1138)
      | ~ v5_relat_1(B_11,'#skF_8')
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_10292])).

tff(c_10203,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10181,c_149])).

tff(c_10366,plain,(
    ! [A_1151,B_1152] :
      ( r2_hidden('#skF_3'(A_1151,B_1152),k1_relat_1(A_1151))
      | r2_hidden('#skF_4'(A_1151,B_1152),B_1152)
      | k2_relat_1(A_1151) = B_1152
      | ~ v1_funct_1(A_1151)
      | ~ v1_relat_1(A_1151) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10372,plain,(
    ! [A_1151,B_1152,B_2] :
      ( r2_hidden('#skF_3'(A_1151,B_1152),B_2)
      | ~ r1_tarski(k1_relat_1(A_1151),B_2)
      | r2_hidden('#skF_4'(A_1151,B_1152),B_1152)
      | k2_relat_1(A_1151) = B_1152
      | ~ v1_funct_1(A_1151)
      | ~ v1_relat_1(A_1151) ) ),
    inference(resolution,[status(thm)],[c_10366,c_2])).

tff(c_5194,plain,(
    r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_123,plain,(
    ! [D_96,B_2,B_97] :
      ( r2_hidden('#skF_9'(D_96),B_2)
      | ~ r1_tarski(B_97,B_2)
      | ~ r1_tarski('#skF_6',B_97)
      | ~ r2_hidden(D_96,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_120,c_2])).

tff(c_5196,plain,(
    ! [D_96] :
      ( r2_hidden('#skF_9'(D_96),k1_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden(D_96,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5194,c_123])).

tff(c_5199,plain,(
    ! [D_96] :
      ( r2_hidden('#skF_9'(D_96),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_96,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_5196])).

tff(c_10322,plain,(
    ! [D_1142] :
      ( r2_hidden('#skF_9'(D_1142),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_1142,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10181,c_5199])).

tff(c_10325,plain,(
    ! [D_1142,B_2] :
      ( r2_hidden('#skF_9'(D_1142),B_2)
      | ~ r1_tarski(k1_relat_1('#skF_8'),B_2)
      | ~ r2_hidden(D_1142,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_10322,c_2])).

tff(c_10206,plain,(
    ! [D_71] :
      ( k1_funct_1('#skF_8','#skF_9'(D_71)) = D_71
      | ~ r2_hidden(D_71,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10181,c_66])).

tff(c_10678,plain,(
    ! [A_1221,B_1222,D_1223] :
      ( k1_funct_1(A_1221,'#skF_3'(A_1221,B_1222)) = '#skF_2'(A_1221,B_1222)
      | k1_funct_1(A_1221,D_1223) != '#skF_4'(A_1221,B_1222)
      | ~ r2_hidden(D_1223,k1_relat_1(A_1221))
      | k2_relat_1(A_1221) = B_1222
      | ~ v1_funct_1(A_1221)
      | ~ v1_relat_1(A_1221) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10682,plain,(
    ! [B_1222,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1222)) = '#skF_2'('#skF_8',B_1222)
      | D_71 != '#skF_4'('#skF_8',B_1222)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1222
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10206,c_10678])).

tff(c_10686,plain,(
    ! [B_1222,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1222)) = '#skF_2'('#skF_8',B_1222)
      | D_71 != '#skF_4'('#skF_8',B_1222)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1222
      | ~ r2_hidden(D_71,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_10682])).

tff(c_10968,plain,(
    ! [B_1259] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1259)) = '#skF_2'('#skF_8',B_1259)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1259)),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1259
      | ~ r2_hidden('#skF_4'('#skF_8',B_1259),'#skF_8') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10686])).

tff(c_10971,plain,(
    ! [B_1259] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1259)) = '#skF_2'('#skF_8',B_1259)
      | k2_relat_1('#skF_8') = B_1259
      | ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_4'('#skF_8',B_1259),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_10325,c_10968])).

tff(c_11054,plain,(
    ! [B_1263] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1263)) = '#skF_2'('#skF_8',B_1263)
      | k2_relat_1('#skF_8') = B_1263
      | ~ r2_hidden('#skF_4'('#skF_8',B_1263),'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_10971])).

tff(c_11060,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_11054])).

tff(c_11065,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_11060])).

tff(c_11066,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_10203,c_11065])).

tff(c_11081,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_8'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_11066,c_36])).

tff(c_11094,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_8'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_11081])).

tff(c_11096,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_11094])).

tff(c_11113,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8'))
    | r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_10372,c_11096])).

tff(c_11125,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_94,c_11113])).

tff(c_11126,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_10203,c_11125])).

tff(c_10200,plain,(
    ! [D_96] :
      ( r2_hidden('#skF_9'(D_96),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_96,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10181,c_5199])).

tff(c_10603,plain,(
    ! [A_1201,B_1202,D_1203] :
      ( r2_hidden('#skF_3'(A_1201,B_1202),k1_relat_1(A_1201))
      | k1_funct_1(A_1201,D_1203) != '#skF_4'(A_1201,B_1202)
      | ~ r2_hidden(D_1203,k1_relat_1(A_1201))
      | k2_relat_1(A_1201) = B_1202
      | ~ v1_funct_1(A_1201)
      | ~ v1_relat_1(A_1201) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10607,plain,(
    ! [B_1202,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_1202),k1_relat_1('#skF_8'))
      | D_71 != '#skF_4'('#skF_8',B_1202)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1202
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10206,c_10603])).

tff(c_10611,plain,(
    ! [B_1202,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_1202),k1_relat_1('#skF_8'))
      | D_71 != '#skF_4'('#skF_8',B_1202)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1202
      | ~ r2_hidden(D_71,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_10607])).

tff(c_10858,plain,(
    ! [B_1248] :
      ( r2_hidden('#skF_3'('#skF_8',B_1248),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1248)),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1248
      | ~ r2_hidden('#skF_4'('#skF_8',B_1248),'#skF_8') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_10611])).

tff(c_10874,plain,(
    ! [B_1248] :
      ( r2_hidden('#skF_3'('#skF_8',B_1248),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1248
      | ~ r2_hidden('#skF_4'('#skF_8',B_1248),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_10200,c_10858])).

tff(c_11116,plain,
    ( k2_relat_1('#skF_8') = '#skF_8'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_10874,c_11096])).

tff(c_11129,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_10203,c_11116])).

tff(c_11153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11126,c_11129])).

tff(c_11154,plain,(
    r2_hidden('#skF_2'('#skF_8','#skF_8'),k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_11094])).

tff(c_11162,plain,(
    ! [B_1267] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_8'),B_1267)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_1267) ) ),
    inference(resolution,[status(thm)],[c_11154,c_2])).

tff(c_11169,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_11162,c_30])).

tff(c_11181,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_11169])).

tff(c_11182,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_10203,c_11181])).

tff(c_11193,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_11182])).

tff(c_11213,plain,
    ( ~ v5_relat_1('#skF_8','#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_10304,c_11193])).

tff(c_11221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8110,c_11213])).

tff(c_11222,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_11182])).

tff(c_10192,plain,(
    ! [D_631,A_662] :
      ( r2_hidden(D_631,A_662)
      | ~ r2_hidden(D_631,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10181,c_8101])).

tff(c_11447,plain,(
    ! [A_662] : r2_hidden('#skF_4'('#skF_8','#skF_8'),A_662) ),
    inference(resolution,[status(thm)],[c_11222,c_10192])).

tff(c_10205,plain,(
    ! [D_71,B_90] :
      ( r2_hidden('#skF_9'(D_71),B_90)
      | ~ r1_tarski('#skF_6',B_90)
      | ~ r2_hidden(D_71,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10181,c_113])).

tff(c_11223,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_11182])).

tff(c_10190,plain,(
    ! [A_910,A_912] :
      ( ~ r1_tarski(A_910,'#skF_8')
      | r1_tarski(A_910,A_912) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10181,c_8206])).

tff(c_11253,plain,(
    ! [A_912] : r1_tarski(k2_relat_1('#skF_8'),A_912) ),
    inference(resolution,[status(thm)],[c_11223,c_10190])).

tff(c_11165,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_8'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_11162,c_24])).

tff(c_11177,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_8'
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_11165])).

tff(c_11178,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_8'))
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_10203,c_11177])).

tff(c_11323,plain,(
    ! [D_1273] :
      ( k1_funct_1('#skF_8',D_1273) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_1273,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11253,c_11178])).

tff(c_11383,plain,(
    ! [D_71] :
      ( k1_funct_1('#skF_8','#skF_9'(D_71)) != '#skF_4'('#skF_8','#skF_8')
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_71,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_10205,c_11323])).

tff(c_11530,plain,(
    ! [D_1279] :
      ( k1_funct_1('#skF_8','#skF_9'(D_1279)) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_1279,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5194,c_11383])).

tff(c_11537,plain,(
    ! [D_1280] :
      ( D_1280 != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_1280,'#skF_8')
      | ~ r2_hidden(D_1280,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10206,c_11530])).

tff(c_11544,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_11447,c_11537])).

tff(c_11587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11447,c_11544])).

tff(c_11589,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_5236])).

tff(c_5238,plain,(
    ! [A_639] :
      ( r1_tarski(A_639,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_639,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5200,c_4])).

tff(c_5247,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,'#skF_7')
      | r1_tarski(A_1,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_112,c_5238])).

tff(c_11764,plain,(
    ! [A_1308,B_1309,B_1310,B_1311] :
      ( r2_hidden('#skF_1'(A_1308,B_1309),B_1310)
      | ~ r1_tarski(B_1311,B_1310)
      | ~ r1_tarski(A_1308,B_1311)
      | r1_tarski(A_1308,B_1309) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_12498,plain,(
    ! [A_1388,B_1389,A_1390] :
      ( r2_hidden('#skF_1'(A_1388,B_1389),k2_relat_1('#skF_8'))
      | ~ r1_tarski(A_1388,A_1390)
      | r1_tarski(A_1388,B_1389)
      | ~ r1_tarski(A_1390,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5247,c_11764])).

tff(c_12508,plain,(
    ! [B_1389] :
      ( r2_hidden('#skF_1'('#skF_6',B_1389),k2_relat_1('#skF_8'))
      | r1_tarski('#skF_6',B_1389)
      | ~ r1_tarski('#skF_7','#skF_7') ) ),
    inference(resolution,[status(thm)],[c_11589,c_12498])).

tff(c_12550,plain,(
    ! [B_1393] :
      ( r2_hidden('#skF_1'('#skF_6',B_1393),k2_relat_1('#skF_8'))
      | r1_tarski('#skF_6',B_1393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_12508])).

tff(c_12596,plain,(
    ! [B_1394,B_1395] :
      ( r2_hidden('#skF_1'('#skF_6',B_1394),B_1395)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_1395)
      | r1_tarski('#skF_6',B_1394) ) ),
    inference(resolution,[status(thm)],[c_12550,c_2])).

tff(c_12612,plain,(
    ! [B_1394,A_10] :
      ( r2_hidden('#skF_1'('#skF_6',B_1394),A_10)
      | ~ v5_relat_1('#skF_8',A_10)
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7')
      | r1_tarski('#skF_6',B_1394) ) ),
    inference(resolution,[status(thm)],[c_12596,c_5222])).

tff(c_12888,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_12612])).

tff(c_12897,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_14,c_12888])).

tff(c_12905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_119,c_12897])).

tff(c_12907,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_12612])).

tff(c_12327,plain,(
    ! [B_1369,A_1370,C_1371] :
      ( k1_xboole_0 = B_1369
      | k1_relset_1(A_1370,B_1369,C_1371) = A_1370
      | ~ v1_funct_2(C_1371,A_1370,B_1369)
      | ~ m1_subset_1(C_1371,k1_zfmisc_1(k2_zfmisc_1(A_1370,B_1369))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12330,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_12327])).

tff(c_12333,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_148,c_12330])).

tff(c_12334,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_12333])).

tff(c_12417,plain,(
    ! [A_1380,B_1381] :
      ( r2_hidden('#skF_3'(A_1380,B_1381),k1_relat_1(A_1380))
      | r2_hidden('#skF_4'(A_1380,B_1381),B_1381)
      | k2_relat_1(A_1380) = B_1381
      | ~ v1_funct_1(A_1380)
      | ~ v1_relat_1(A_1380) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12426,plain,(
    ! [A_1380,B_1381,B_2] :
      ( r2_hidden('#skF_3'(A_1380,B_1381),B_2)
      | ~ r1_tarski(k1_relat_1(A_1380),B_2)
      | r2_hidden('#skF_4'(A_1380,B_1381),B_1381)
      | k2_relat_1(A_1380) = B_1381
      | ~ v1_funct_1(A_1380)
      | ~ v1_relat_1(A_1380) ) ),
    inference(resolution,[status(thm)],[c_12417,c_2])).

tff(c_13157,plain,(
    ! [A_1429,B_1430,D_1431] :
      ( k1_funct_1(A_1429,'#skF_3'(A_1429,B_1430)) = '#skF_2'(A_1429,B_1430)
      | k1_funct_1(A_1429,D_1431) != '#skF_4'(A_1429,B_1430)
      | ~ r2_hidden(D_1431,k1_relat_1(A_1429))
      | k2_relat_1(A_1429) = B_1430
      | ~ v1_funct_1(A_1429)
      | ~ v1_relat_1(A_1429) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_13163,plain,(
    ! [B_1430,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1430)) = '#skF_2'('#skF_8',B_1430)
      | D_71 != '#skF_4'('#skF_8',B_1430)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1430
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_13157])).

tff(c_13165,plain,(
    ! [B_1430,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1430)) = '#skF_2'('#skF_8',B_1430)
      | D_71 != '#skF_4'('#skF_8',B_1430)
      | ~ r2_hidden('#skF_9'(D_71),'#skF_6')
      | k2_relat_1('#skF_8') = B_1430
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_12334,c_13163])).

tff(c_13773,plain,(
    ! [B_1498] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1498)) = '#skF_2'('#skF_8',B_1498)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1498)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1498
      | ~ r2_hidden('#skF_4'('#skF_8',B_1498),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_13165])).

tff(c_13933,plain,(
    ! [B_1501] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1501)) = '#skF_2'('#skF_8',B_1501)
      | k2_relat_1('#skF_8') = B_1501
      | ~ r2_hidden('#skF_4'('#skF_8',B_1501),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_13773])).

tff(c_13945,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_13933])).

tff(c_13952,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_13945])).

tff(c_13953,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_13952])).

tff(c_13965,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_13953,c_36])).

tff(c_13976,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_12334,c_13965])).

tff(c_13978,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_13976])).

tff(c_14003,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
    | r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_12426,c_13978])).

tff(c_14027,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_94,c_12334,c_14003])).

tff(c_14028,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_14027])).

tff(c_12967,plain,(
    ! [A_1414,B_1415,D_1416] :
      ( r2_hidden('#skF_3'(A_1414,B_1415),k1_relat_1(A_1414))
      | k1_funct_1(A_1414,D_1416) != '#skF_4'(A_1414,B_1415)
      | ~ r2_hidden(D_1416,k1_relat_1(A_1414))
      | k2_relat_1(A_1414) = B_1415
      | ~ v1_funct_1(A_1414)
      | ~ v1_relat_1(A_1414) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12973,plain,(
    ! [B_1415,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_1415),k1_relat_1('#skF_8'))
      | D_71 != '#skF_4'('#skF_8',B_1415)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1415
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_12967])).

tff(c_12975,plain,(
    ! [B_1415,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_1415),'#skF_6')
      | D_71 != '#skF_4'('#skF_8',B_1415)
      | ~ r2_hidden('#skF_9'(D_71),'#skF_6')
      | k2_relat_1('#skF_8') = B_1415
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_12334,c_12334,c_12973])).

tff(c_13616,plain,(
    ! [B_1481] :
      ( r2_hidden('#skF_3'('#skF_8',B_1481),'#skF_6')
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1481)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1481
      | ~ r2_hidden('#skF_4'('#skF_8',B_1481),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_12975])).

tff(c_13628,plain,(
    ! [B_1481] :
      ( r2_hidden('#skF_3'('#skF_8',B_1481),'#skF_6')
      | k2_relat_1('#skF_8') = B_1481
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden('#skF_4'('#skF_8',B_1481),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_113,c_13616])).

tff(c_13639,plain,(
    ! [B_1482] :
      ( r2_hidden('#skF_3'('#skF_8',B_1482),'#skF_6')
      | k2_relat_1('#skF_8') = B_1482
      | ~ r2_hidden('#skF_4'('#skF_8',B_1482),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_13628])).

tff(c_13642,plain,(
    ! [B_1482,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_1482),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | k2_relat_1('#skF_8') = B_1482
      | ~ r2_hidden('#skF_4'('#skF_8',B_1482),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_13639,c_2])).

tff(c_14009,plain,
    ( ~ r1_tarski('#skF_6','#skF_6')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_13642,c_13978])).

tff(c_14033,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_14009])).

tff(c_14034,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_14033])).

tff(c_14063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14028,c_14034])).

tff(c_14064,plain,(
    r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_13976])).

tff(c_14100,plain,(
    ! [B_1507] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_1507)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_1507) ) ),
    inference(resolution,[status(thm)],[c_14064,c_2])).

tff(c_14106,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14100,c_24])).

tff(c_14119,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_49,'#skF_6')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12907,c_88,c_64,c_12334,c_14106])).

tff(c_14214,plain,(
    ! [D_1513] :
      ( k1_funct_1('#skF_8',D_1513) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1513,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_14119])).

tff(c_14375,plain,(
    ! [D_71] :
      ( k1_funct_1('#skF_8','#skF_9'(D_71)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_113,c_14214])).

tff(c_14514,plain,(
    ! [D_1518] :
      ( k1_funct_1('#skF_8','#skF_9'(D_1518)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1518,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_14375])).

tff(c_14518,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_14514])).

tff(c_14110,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_14100,c_30])).

tff(c_14123,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12907,c_88,c_64,c_14110])).

tff(c_14124,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_14123])).

tff(c_14520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14518,c_14124])).

tff(c_14521,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_12333])).

tff(c_11591,plain,(
    ! [D_96] :
      ( r2_hidden('#skF_9'(D_96),'#skF_7')
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden(D_96,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_11589,c_123])).

tff(c_11609,plain,(
    ! [D_1284] :
      ( r2_hidden('#skF_9'(D_1284),'#skF_7')
      | ~ r2_hidden(D_1284,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_11591])).

tff(c_11633,plain,(
    ! [D_1289,B_1290] :
      ( r2_hidden('#skF_9'(D_1289),B_1290)
      | ~ r1_tarski('#skF_7',B_1290)
      | ~ r2_hidden(D_1289,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_11609,c_2])).

tff(c_11727,plain,(
    ! [D_1303,B_1304,B_1305] :
      ( r2_hidden('#skF_9'(D_1303),B_1304)
      | ~ r1_tarski(B_1305,B_1304)
      | ~ r1_tarski('#skF_7',B_1305)
      | ~ r2_hidden(D_1303,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_11633,c_2])).

tff(c_11750,plain,(
    ! [D_1303,A_6] :
      ( r2_hidden('#skF_9'(D_1303),A_6)
      | ~ r1_tarski('#skF_7',k1_xboole_0)
      | ~ r2_hidden(D_1303,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_8,c_11727])).

tff(c_11751,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_11750])).

tff(c_14530,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14521,c_11751])).

tff(c_14540,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_14530])).

tff(c_14542,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_11750])).

tff(c_14578,plain,(
    ! [A_1523,B_1524,B_1525,B_1526] :
      ( r2_hidden('#skF_1'(A_1523,B_1524),B_1525)
      | ~ r1_tarski(B_1526,B_1525)
      | ~ r1_tarski(A_1523,B_1526)
      | r1_tarski(A_1523,B_1524) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_14775,plain,(
    ! [A_1552,B_1553] :
      ( r2_hidden('#skF_1'(A_1552,B_1553),k1_xboole_0)
      | ~ r1_tarski(A_1552,'#skF_7')
      | r1_tarski(A_1552,B_1553) ) ),
    inference(resolution,[status(thm)],[c_14542,c_14578])).

tff(c_14790,plain,(
    ! [A_1555] :
      ( ~ r1_tarski(A_1555,'#skF_7')
      | r1_tarski(A_1555,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14775,c_4])).

tff(c_14800,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_14790,c_168])).

tff(c_14811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11589,c_14800])).

tff(c_14813,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_14937,plain,(
    ! [A_1576,B_1577,B_1578,B_1579] :
      ( r2_hidden('#skF_1'(A_1576,B_1577),B_1578)
      | ~ r1_tarski(B_1579,B_1578)
      | ~ r1_tarski(A_1576,B_1579)
      | r1_tarski(A_1576,B_1577) ) ),
    inference(resolution,[status(thm)],[c_129,c_2])).

tff(c_14956,plain,(
    ! [A_1580,B_1581] :
      ( r2_hidden('#skF_1'(A_1580,B_1581),k1_xboole_0)
      | ~ r1_tarski(A_1580,'#skF_6')
      | r1_tarski(A_1580,B_1581) ) ),
    inference(resolution,[status(thm)],[c_14813,c_14937])).

tff(c_14967,plain,(
    ! [A_1582] :
      ( ~ r1_tarski(A_1582,'#skF_6')
      | r1_tarski(A_1582,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14956,c_4])).

tff(c_14980,plain,(
    ! [B_1583] :
      ( v5_relat_1(B_1583,k1_xboole_0)
      | ~ v1_relat_1(B_1583)
      | ~ r1_tarski(k2_relat_1(B_1583),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_14967,c_12])).

tff(c_14986,plain,(
    ! [B_1584] :
      ( v5_relat_1(B_1584,k1_xboole_0)
      | ~ v5_relat_1(B_1584,'#skF_6')
      | ~ v1_relat_1(B_1584) ) ),
    inference(resolution,[status(thm)],[c_14,c_14980])).

tff(c_14812,plain,(
    ! [D_111,A_6] :
      ( r2_hidden('#skF_9'(D_111),A_6)
      | ~ r2_hidden(D_111,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_14823,plain,(
    ! [B_1558,A_1559] :
      ( r2_hidden(k1_funct_1(B_1558,A_1559),k2_relat_1(B_1558))
      | ~ r2_hidden(A_1559,k1_relat_1(B_1558))
      | ~ v1_funct_1(B_1558)
      | ~ v1_relat_1(B_1558) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14828,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_14823])).

tff(c_14833,plain,(
    ! [D_1562] :
      ( r2_hidden(D_1562,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_1562),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_1562,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_14828])).

tff(c_14839,plain,(
    ! [D_1563] :
      ( r2_hidden(D_1563,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_1563,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14812,c_14833])).

tff(c_14848,plain,(
    ! [D_1564,B_1565] :
      ( r2_hidden(D_1564,B_1565)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_1565)
      | ~ r2_hidden(D_1564,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14839,c_2])).

tff(c_14851,plain,(
    ! [D_1564,A_10] :
      ( r2_hidden(D_1564,A_10)
      | ~ r2_hidden(D_1564,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_10)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14,c_14848])).

tff(c_14859,plain,(
    ! [D_1566,A_1567] :
      ( r2_hidden(D_1566,A_1567)
      | ~ r2_hidden(D_1566,'#skF_7')
      | ~ v5_relat_1('#skF_8',A_1567) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_14851])).

tff(c_14895,plain,(
    ! [B_1573,A_1574] :
      ( r2_hidden('#skF_1'('#skF_7',B_1573),A_1574)
      | ~ v5_relat_1('#skF_8',A_1574)
      | r1_tarski('#skF_7',B_1573) ) ),
    inference(resolution,[status(thm)],[c_6,c_14859])).

tff(c_14916,plain,(
    ! [A_1574] :
      ( ~ v5_relat_1('#skF_8',A_1574)
      | r1_tarski('#skF_7',A_1574) ) ),
    inference(resolution,[status(thm)],[c_14895,c_4])).

tff(c_14990,plain,
    ( r1_tarski('#skF_7',k1_xboole_0)
    | ~ v5_relat_1('#skF_8','#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_14986,c_14916])).

tff(c_14993,plain,
    ( r1_tarski('#skF_7',k1_xboole_0)
    | ~ v5_relat_1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_14990])).

tff(c_14994,plain,(
    ~ v5_relat_1('#skF_8','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_14993])).

tff(c_15646,plain,(
    ! [A_1667,B_1668,A_1669,B_1670] :
      ( r2_hidden('#skF_1'(A_1667,B_1668),A_1669)
      | ~ r1_tarski(A_1667,k2_relat_1(B_1670))
      | r1_tarski(A_1667,B_1668)
      | ~ v5_relat_1(B_1670,A_1669)
      | ~ v1_relat_1(B_1670) ) ),
    inference(resolution,[status(thm)],[c_14,c_14937])).

tff(c_15684,plain,(
    ! [B_1673,B_1674,A_1675] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_1673),B_1674),A_1675)
      | r1_tarski(k2_relat_1(B_1673),B_1674)
      | ~ v5_relat_1(B_1673,A_1675)
      | ~ v1_relat_1(B_1673) ) ),
    inference(resolution,[status(thm)],[c_94,c_15646])).

tff(c_14847,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14839,c_4])).

tff(c_15702,plain,(
    ! [B_1676] :
      ( r1_tarski(k2_relat_1(B_1676),k2_relat_1('#skF_8'))
      | ~ v5_relat_1(B_1676,'#skF_7')
      | ~ v1_relat_1(B_1676) ) ),
    inference(resolution,[status(thm)],[c_15684,c_14847])).

tff(c_14953,plain,(
    ! [A_1576,B_1577,A_10,B_11] :
      ( r2_hidden('#skF_1'(A_1576,B_1577),A_10)
      | ~ r1_tarski(A_1576,k2_relat_1(B_11))
      | r1_tarski(A_1576,B_1577)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_14937])).

tff(c_15704,plain,(
    ! [B_1676,B_1577,A_10] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_1676),B_1577),A_10)
      | r1_tarski(k2_relat_1(B_1676),B_1577)
      | ~ v5_relat_1('#skF_8',A_10)
      | ~ v1_relat_1('#skF_8')
      | ~ v5_relat_1(B_1676,'#skF_7')
      | ~ v1_relat_1(B_1676) ) ),
    inference(resolution,[status(thm)],[c_15702,c_14953])).

tff(c_16131,plain,(
    ! [B_1712,B_1713,A_1714] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_1712),B_1713),A_1714)
      | r1_tarski(k2_relat_1(B_1712),B_1713)
      | ~ v5_relat_1('#skF_8',A_1714)
      | ~ v5_relat_1(B_1712,'#skF_7')
      | ~ v1_relat_1(B_1712) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_15704])).

tff(c_16156,plain,(
    ! [B_1712,A_1714] :
      ( r1_tarski(k2_relat_1(B_1712),A_1714)
      | ~ v5_relat_1('#skF_8',A_1714)
      | ~ v5_relat_1(B_1712,'#skF_7')
      | ~ v1_relat_1(B_1712) ) ),
    inference(resolution,[status(thm)],[c_16131,c_4])).

tff(c_15003,plain,(
    ! [A_1587,B_1588,A_1589] :
      ( r2_hidden('#skF_1'(A_1587,B_1588),A_1589)
      | ~ r1_tarski(A_1587,k1_xboole_0)
      | r1_tarski(A_1587,B_1588) ) ),
    inference(resolution,[status(thm)],[c_8,c_14937])).

tff(c_15034,plain,(
    ! [A_1591,A_1592] :
      ( ~ r1_tarski(A_1591,k1_xboole_0)
      | r1_tarski(A_1591,A_1592) ) ),
    inference(resolution,[status(thm)],[c_15003,c_4])).

tff(c_15049,plain,(
    ! [A_1592] : r1_tarski('#skF_6',A_1592) ),
    inference(resolution,[status(thm)],[c_14813,c_15034])).

tff(c_15515,plain,(
    ! [B_1646,A_1647,C_1648] :
      ( k1_xboole_0 = B_1646
      | k1_relset_1(A_1647,B_1646,C_1648) = A_1647
      | ~ v1_funct_2(C_1648,A_1647,B_1646)
      | ~ m1_subset_1(C_1648,k1_zfmisc_1(k2_zfmisc_1(A_1647,B_1646))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_15518,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_15515])).

tff(c_15521,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_148,c_15518])).

tff(c_15530,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_15521])).

tff(c_16080,plain,(
    ! [A_1706,B_1707,D_1708] :
      ( r2_hidden('#skF_3'(A_1706,B_1707),k1_relat_1(A_1706))
      | k1_funct_1(A_1706,D_1708) != '#skF_4'(A_1706,B_1707)
      | ~ r2_hidden(D_1708,k1_relat_1(A_1706))
      | k2_relat_1(A_1706) = B_1707
      | ~ v1_funct_1(A_1706)
      | ~ v1_relat_1(A_1706) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16086,plain,(
    ! [B_1707,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_1707),k1_relat_1('#skF_8'))
      | D_71 != '#skF_4'('#skF_8',B_1707)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1707
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_16080])).

tff(c_16088,plain,(
    ! [B_1707,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_1707),'#skF_6')
      | D_71 != '#skF_4'('#skF_8',B_1707)
      | ~ r2_hidden('#skF_9'(D_71),'#skF_6')
      | k2_relat_1('#skF_8') = B_1707
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_15530,c_15530,c_16086])).

tff(c_16492,plain,(
    ! [B_1741] :
      ( r2_hidden('#skF_3'('#skF_8',B_1741),'#skF_6')
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1741)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1741
      | ~ r2_hidden('#skF_4'('#skF_8',B_1741),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_16088])).

tff(c_16517,plain,(
    ! [B_1745] :
      ( r2_hidden('#skF_3'('#skF_8',B_1745),'#skF_6')
      | k2_relat_1('#skF_8') = B_1745
      | ~ r2_hidden('#skF_4'('#skF_8',B_1745),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14812,c_16492])).

tff(c_16519,plain,(
    ! [B_1745,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_1745),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | k2_relat_1('#skF_8') = B_1745
      | ~ r2_hidden('#skF_4'('#skF_8',B_1745),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_16517,c_2])).

tff(c_16522,plain,(
    ! [B_1745,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_1745),B_2)
      | k2_relat_1('#skF_8') = B_1745
      | ~ r2_hidden('#skF_4'('#skF_8',B_1745),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15049,c_16519])).

tff(c_16298,plain,(
    ! [A_1724,B_1725,D_1726] :
      ( k1_funct_1(A_1724,'#skF_3'(A_1724,B_1725)) = '#skF_2'(A_1724,B_1725)
      | k1_funct_1(A_1724,D_1726) != '#skF_4'(A_1724,B_1725)
      | ~ r2_hidden(D_1726,k1_relat_1(A_1724))
      | k2_relat_1(A_1724) = B_1725
      | ~ v1_funct_1(A_1724)
      | ~ v1_relat_1(A_1724) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16304,plain,(
    ! [B_1725,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1725)) = '#skF_2'('#skF_8',B_1725)
      | D_71 != '#skF_4'('#skF_8',B_1725)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1725
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_16298])).

tff(c_16306,plain,(
    ! [B_1725,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1725)) = '#skF_2'('#skF_8',B_1725)
      | D_71 != '#skF_4'('#skF_8',B_1725)
      | ~ r2_hidden('#skF_9'(D_71),'#skF_6')
      | k2_relat_1('#skF_8') = B_1725
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_15530,c_16304])).

tff(c_16566,plain,(
    ! [B_1751] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1751)) = '#skF_2'('#skF_8',B_1751)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1751)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1751
      | ~ r2_hidden('#skF_4'('#skF_8',B_1751),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_16306])).

tff(c_16571,plain,(
    ! [B_1752] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1752)) = '#skF_2'('#skF_8',B_1752)
      | k2_relat_1('#skF_8') = B_1752
      | ~ r2_hidden('#skF_4'('#skF_8',B_1752),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14812,c_16566])).

tff(c_16577,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_16571])).

tff(c_16586,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_16577])).

tff(c_16587,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_16586])).

tff(c_16599,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_16587,c_36])).

tff(c_16610,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_15530,c_16599])).

tff(c_16612,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_16610])).

tff(c_16615,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_16522,c_16612])).

tff(c_16627,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_16615])).

tff(c_15522,plain,(
    ! [A_1649,B_1650] :
      ( r2_hidden('#skF_3'(A_1649,B_1650),k1_relat_1(A_1649))
      | r2_hidden('#skF_4'(A_1649,B_1650),B_1650)
      | k2_relat_1(A_1649) = B_1650
      | ~ v1_funct_1(A_1649)
      | ~ v1_relat_1(A_1649) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_15528,plain,(
    ! [A_1649,B_1650,B_2] :
      ( r2_hidden('#skF_3'(A_1649,B_1650),B_2)
      | ~ r1_tarski(k1_relat_1(A_1649),B_2)
      | r2_hidden('#skF_4'(A_1649,B_1650),B_1650)
      | k2_relat_1(A_1649) = B_1650
      | ~ v1_funct_1(A_1649)
      | ~ v1_relat_1(A_1649) ) ),
    inference(resolution,[status(thm)],[c_15522,c_2])).

tff(c_16618,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
    | r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_15528,c_16612])).

tff(c_16630,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_94,c_15530,c_16618])).

tff(c_16631,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_16630])).

tff(c_16672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16627,c_16631])).

tff(c_16674,plain,(
    r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_16610])).

tff(c_16676,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_3'('#skF_8','#skF_7'),B_2)
      | ~ r1_tarski('#skF_6',B_2) ) ),
    inference(resolution,[status(thm)],[c_16674,c_2])).

tff(c_16679,plain,(
    ! [B_2] : r2_hidden('#skF_3'('#skF_8','#skF_7'),B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15049,c_16676])).

tff(c_14829,plain,(
    ! [B_1558,A_1559,B_2] :
      ( r2_hidden(k1_funct_1(B_1558,A_1559),B_2)
      | ~ r1_tarski(k2_relat_1(B_1558),B_2)
      | ~ r2_hidden(A_1559,k1_relat_1(B_1558))
      | ~ v1_funct_1(B_1558)
      | ~ v1_relat_1(B_1558) ) ),
    inference(resolution,[status(thm)],[c_14823,c_2])).

tff(c_16595,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16587,c_14829])).

tff(c_16608,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_15530,c_16595])).

tff(c_16697,plain,(
    ! [B_1757] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_1757)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_1757) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16679,c_16608])).

tff(c_16707,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_16697,c_30])).

tff(c_16720,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_16707])).

tff(c_16721,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_16720])).

tff(c_16727,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_16721])).

tff(c_16730,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_16156,c_16727])).

tff(c_16743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_119,c_16730])).

tff(c_16745,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_16721])).

tff(c_16703,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_16697,c_24])).

tff(c_16716,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_49,'#skF_6')
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_15530,c_16703])).

tff(c_16717,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_49,'#skF_6')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_16716])).

tff(c_16916,plain,(
    ! [D_1765] :
      ( k1_funct_1('#skF_8',D_1765) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1765,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16745,c_16717])).

tff(c_17064,plain,(
    ! [D_1767] :
      ( k1_funct_1('#skF_8','#skF_9'(D_1767)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1767,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14812,c_16916])).

tff(c_17068,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_17064])).

tff(c_16744,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_16721])).

tff(c_17070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17068,c_16744])).

tff(c_17071,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_15521])).

tff(c_15085,plain,(
    ! [B_1596,A_1597] :
      ( r1_tarski(k2_relat_1(B_1596),A_1597)
      | ~ v5_relat_1(B_1596,k1_xboole_0)
      | ~ v1_relat_1(B_1596) ) ),
    inference(resolution,[status(thm)],[c_14,c_15034])).

tff(c_14846,plain,(
    ! [D_1563,B_2] :
      ( r2_hidden(D_1563,B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r2_hidden(D_1563,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14839,c_2])).

tff(c_14978,plain,(
    ! [D_1563] :
      ( r2_hidden(D_1563,k1_xboole_0)
      | ~ r2_hidden(D_1563,'#skF_7')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_14967,c_14846])).

tff(c_14996,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_14978])).

tff(c_15094,plain,
    ( ~ v5_relat_1('#skF_8',k1_xboole_0)
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_15085,c_14996])).

tff(c_15111,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_15094])).

tff(c_17099,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17071,c_15111])).

tff(c_17110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_17099])).

tff(c_17112,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_14978])).

tff(c_17122,plain,
    ( v5_relat_1('#skF_8','#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_17112,c_12])).

tff(c_17130,plain,(
    v5_relat_1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_17122])).

tff(c_17132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14994,c_17130])).

tff(c_17134,plain,(
    v5_relat_1('#skF_8','#skF_6') ),
    inference(splitRight,[status(thm)],[c_14993])).

tff(c_17138,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_14978])).

tff(c_17148,plain,
    ( ~ v5_relat_1('#skF_8','#skF_6')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_14,c_17138])).

tff(c_17152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_17134,c_17148])).

tff(c_17154,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_14978])).

tff(c_14966,plain,(
    ! [A_1580] :
      ( ~ r1_tarski(A_1580,'#skF_6')
      | r1_tarski(A_1580,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14956,c_4])).

tff(c_17388,plain,(
    ! [A_1793,B_1794,A_1795] :
      ( r2_hidden('#skF_1'(A_1793,B_1794),A_1795)
      | ~ r1_tarski(A_1793,k1_xboole_0)
      | r1_tarski(A_1793,B_1794) ) ),
    inference(resolution,[status(thm)],[c_8,c_14937])).

tff(c_17411,plain,(
    ! [A_1796,A_1797] :
      ( ~ r1_tarski(A_1796,k1_xboole_0)
      | r1_tarski(A_1796,A_1797) ) ),
    inference(resolution,[status(thm)],[c_17388,c_4])).

tff(c_17456,plain,(
    ! [A_1799,A_1800] :
      ( r1_tarski(A_1799,A_1800)
      | ~ r1_tarski(A_1799,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_14966,c_17411])).

tff(c_17481,plain,(
    ! [A_1800] : r1_tarski(k2_relat_1('#skF_8'),A_1800) ),
    inference(resolution,[status(thm)],[c_17154,c_17456])).

tff(c_18580,plain,(
    ! [A_1935,B_1936,D_1937] :
      ( k1_funct_1(A_1935,'#skF_3'(A_1935,B_1936)) = '#skF_2'(A_1935,B_1936)
      | k1_funct_1(A_1935,D_1937) != '#skF_4'(A_1935,B_1936)
      | ~ r2_hidden(D_1937,k1_relat_1(A_1935))
      | k2_relat_1(A_1935) = B_1936
      | ~ v1_funct_1(A_1935)
      | ~ v1_relat_1(A_1935) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18586,plain,(
    ! [B_1936,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1936)) = '#skF_2'('#skF_8',B_1936)
      | D_71 != '#skF_4'('#skF_8',B_1936)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1936
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_18580])).

tff(c_18588,plain,(
    ! [B_1936,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1936)) = '#skF_2'('#skF_8',B_1936)
      | D_71 != '#skF_4'('#skF_8',B_1936)
      | ~ r2_hidden('#skF_9'(D_71),'#skF_6')
      | k2_relat_1('#skF_8') = B_1936
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_17806,c_18586])).

tff(c_18787,plain,(
    ! [B_1970] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1970)) = '#skF_2'('#skF_8',B_1970)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1970)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1970
      | ~ r2_hidden('#skF_4'('#skF_8',B_1970),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_18588])).

tff(c_18914,plain,(
    ! [B_1973] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_1973)) = '#skF_2'('#skF_8',B_1973)
      | k2_relat_1('#skF_8') = B_1973
      | ~ r2_hidden('#skF_4'('#skF_8',B_1973),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14812,c_18787])).

tff(c_18930,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_18914])).

tff(c_18937,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_18930])).

tff(c_18938,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_18937])).

tff(c_17434,plain,(
    ! [A_1797] : r1_tarski('#skF_6',A_1797) ),
    inference(resolution,[status(thm)],[c_14813,c_17411])).

tff(c_18236,plain,(
    ! [B_1883,A_1884,B_1885] :
      ( r2_hidden(k1_funct_1(B_1883,A_1884),B_1885)
      | ~ r1_tarski(k2_relat_1(B_1883),B_1885)
      | ~ r2_hidden(A_1884,k1_relat_1(B_1883))
      | ~ v1_funct_1(B_1883)
      | ~ v1_relat_1(B_1883) ) ),
    inference(resolution,[status(thm)],[c_14823,c_2])).

tff(c_18644,plain,(
    ! [B_1950,A_1951,B_1952,B_1953] :
      ( r2_hidden(k1_funct_1(B_1950,A_1951),B_1952)
      | ~ r1_tarski(B_1953,B_1952)
      | ~ r1_tarski(k2_relat_1(B_1950),B_1953)
      | ~ r2_hidden(A_1951,k1_relat_1(B_1950))
      | ~ v1_funct_1(B_1950)
      | ~ v1_relat_1(B_1950) ) ),
    inference(resolution,[status(thm)],[c_18236,c_2])).

tff(c_18667,plain,(
    ! [B_1950,A_1951,A_1797] :
      ( r2_hidden(k1_funct_1(B_1950,A_1951),A_1797)
      | ~ r1_tarski(k2_relat_1(B_1950),'#skF_6')
      | ~ r2_hidden(A_1951,k1_relat_1(B_1950))
      | ~ v1_funct_1(B_1950)
      | ~ v1_relat_1(B_1950) ) ),
    inference(resolution,[status(thm)],[c_17434,c_18644])).

tff(c_18945,plain,(
    ! [A_1797] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),A_1797)
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_6')
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18938,c_18667])).

tff(c_18967,plain,(
    ! [A_1797] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),A_1797)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_17806,c_17481,c_18945])).

tff(c_18997,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_18967])).

tff(c_19000,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),'#skF_6')
    | r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_17972,c_18997])).

tff(c_19024,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_94,c_17806,c_19000])).

tff(c_19025,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_19024])).

tff(c_18444,plain,(
    ! [A_1909,B_1910,D_1911] :
      ( r2_hidden('#skF_3'(A_1909,B_1910),k1_relat_1(A_1909))
      | k1_funct_1(A_1909,D_1911) != '#skF_4'(A_1909,B_1910)
      | ~ r2_hidden(D_1911,k1_relat_1(A_1909))
      | k2_relat_1(A_1909) = B_1910
      | ~ v1_funct_1(A_1909)
      | ~ v1_relat_1(A_1909) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18450,plain,(
    ! [B_1910,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_1910),k1_relat_1('#skF_8'))
      | D_71 != '#skF_4'('#skF_8',B_1910)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_1910
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_18444])).

tff(c_18452,plain,(
    ! [B_1910,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_1910),'#skF_6')
      | D_71 != '#skF_4'('#skF_8',B_1910)
      | ~ r2_hidden('#skF_9'(D_71),'#skF_6')
      | k2_relat_1('#skF_8') = B_1910
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_17806,c_17806,c_18450])).

tff(c_18575,plain,(
    ! [B_1934] :
      ( r2_hidden('#skF_3'('#skF_8',B_1934),'#skF_6')
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_1934)),'#skF_6')
      | k2_relat_1('#skF_8') = B_1934
      | ~ r2_hidden('#skF_4'('#skF_8',B_1934),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_18452])).

tff(c_18589,plain,(
    ! [B_1938] :
      ( r2_hidden('#skF_3'('#skF_8',B_1938),'#skF_6')
      | k2_relat_1('#skF_8') = B_1938
      | ~ r2_hidden('#skF_4'('#skF_8',B_1938),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14812,c_18575])).

tff(c_18591,plain,(
    ! [B_1938,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_1938),B_2)
      | ~ r1_tarski('#skF_6',B_2)
      | k2_relat_1('#skF_8') = B_1938
      | ~ r2_hidden('#skF_4'('#skF_8',B_1938),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_18589,c_2])).

tff(c_18594,plain,(
    ! [B_1938,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_1938),B_2)
      | k2_relat_1('#skF_8') = B_1938
      | ~ r2_hidden('#skF_4'('#skF_8',B_1938),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17434,c_18591])).

tff(c_19003,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_18594,c_18997])).

tff(c_19028,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_19003])).

tff(c_19067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19025,c_19028])).

tff(c_19070,plain,(
    ! [A_1977] : r2_hidden('#skF_2'('#skF_8','#skF_7'),A_1977) ),
    inference(splitRight,[status(thm)],[c_18967])).

tff(c_19080,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_19070,c_30])).

tff(c_19094,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_19080])).

tff(c_19095,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_19094])).

tff(c_17186,plain,(
    ! [D_1772] :
      ( r2_hidden(D_1772,k1_xboole_0)
      | ~ r2_hidden(D_1772,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_14978])).

tff(c_17188,plain,(
    ! [D_1772,B_2] :
      ( r2_hidden(D_1772,B_2)
      | ~ r1_tarski(k1_xboole_0,B_2)
      | ~ r2_hidden(D_1772,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_17186,c_2])).

tff(c_17195,plain,(
    ! [D_1772,B_2] :
      ( r2_hidden(D_1772,B_2)
      | ~ r2_hidden(D_1772,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_17188])).

tff(c_19115,plain,(
    ! [B_2] : r2_hidden('#skF_4'('#skF_8','#skF_7'),B_2) ),
    inference(resolution,[status(thm)],[c_19095,c_17195])).

tff(c_19076,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_19070,c_24])).

tff(c_19090,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_49,'#skF_6')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_17806,c_19076])).

tff(c_19217,plain,(
    ! [D_1983] :
      ( k1_funct_1('#skF_8',D_1983) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1983,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_19090])).

tff(c_19369,plain,(
    ! [D_1984] :
      ( k1_funct_1('#skF_8','#skF_9'(D_1984)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1984,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_14812,c_19217])).

tff(c_19442,plain,(
    ! [D_1987] :
      ( D_1987 != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_1987,'#skF_7')
      | ~ r2_hidden(D_1987,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_19369])).

tff(c_19448,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_19115,c_19442])).

tff(c_19531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19115,c_19448])).

tff(c_19533,plain,(
    k1_relat_1('#skF_8') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_17805])).

tff(c_19532,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_17805])).

tff(c_19634,plain,(
    ! [C_1996,A_1997] :
      ( C_1996 = '#skF_7'
      | ~ v1_funct_2(C_1996,A_1997,'#skF_7')
      | A_1997 = '#skF_7'
      | ~ m1_subset_1(C_1996,k1_zfmisc_1(k2_zfmisc_1(A_1997,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19532,c_19532,c_19532,c_19532,c_48])).

tff(c_19637,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_60,c_19634])).

tff(c_19640,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_19637])).

tff(c_19641,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_19640])).

tff(c_19659,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19641,c_62])).

tff(c_19654,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19641,c_148])).

tff(c_19658,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19641,c_60])).

tff(c_54,plain,(
    ! [B_66,C_67] :
      ( k1_relset_1(k1_xboole_0,B_66,C_67) = k1_xboole_0
      | ~ v1_funct_2(C_67,k1_xboole_0,B_66)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_19541,plain,(
    ! [B_66,C_67] :
      ( k1_relset_1('#skF_7',B_66,C_67) = '#skF_7'
      | ~ v1_funct_2(C_67,'#skF_7',B_66)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_66))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19532,c_19532,c_19532,c_19532,c_54])).

tff(c_19825,plain,(
    ! [B_2021,C_2022] :
      ( k1_relset_1('#skF_6',B_2021,C_2022) = '#skF_6'
      | ~ v1_funct_2(C_2022,'#skF_6',B_2021)
      | ~ m1_subset_1(C_2022,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_2021))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19641,c_19641,c_19641,c_19641,c_19541])).

tff(c_19828,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_19658,c_19825])).

tff(c_19831,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19659,c_19654,c_19828])).

tff(c_19833,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19533,c_19831])).

tff(c_19834,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_19640])).

tff(c_19849,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19834,c_149])).

tff(c_19847,plain,(
    ! [D_111,A_6] :
      ( r2_hidden('#skF_9'(D_111),A_6)
      | ~ r2_hidden(D_111,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19834,c_14812])).

tff(c_19851,plain,(
    ! [D_71] :
      ( k1_funct_1('#skF_8','#skF_9'(D_71)) = D_71
      | ~ r2_hidden(D_71,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19834,c_66])).

tff(c_20075,plain,(
    ! [A_2046,B_2047,D_2048] :
      ( r2_hidden('#skF_3'(A_2046,B_2047),k1_relat_1(A_2046))
      | k1_funct_1(A_2046,D_2048) != '#skF_4'(A_2046,B_2047)
      | ~ r2_hidden(D_2048,k1_relat_1(A_2046))
      | k2_relat_1(A_2046) = B_2047
      | ~ v1_funct_1(A_2046)
      | ~ v1_relat_1(A_2046) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20077,plain,(
    ! [B_2047,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_2047),k1_relat_1('#skF_8'))
      | D_71 != '#skF_4'('#skF_8',B_2047)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_2047
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19851,c_20075])).

tff(c_20083,plain,(
    ! [B_2047,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_2047),k1_relat_1('#skF_8'))
      | D_71 != '#skF_4'('#skF_8',B_2047)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_2047
      | ~ r2_hidden(D_71,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_20077])).

tff(c_20346,plain,(
    ! [B_2096] :
      ( r2_hidden('#skF_3'('#skF_8',B_2096),k1_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_2096)),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_2096
      | ~ r2_hidden('#skF_4'('#skF_8',B_2096),'#skF_8') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_20083])).

tff(c_20351,plain,(
    ! [B_2097] :
      ( r2_hidden('#skF_3'('#skF_8',B_2097),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_2097
      | ~ r2_hidden('#skF_4'('#skF_8',B_2097),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_19847,c_20346])).

tff(c_20354,plain,(
    ! [B_2097,B_2] :
      ( r2_hidden('#skF_3'('#skF_8',B_2097),B_2)
      | ~ r1_tarski(k1_relat_1('#skF_8'),B_2)
      | k2_relat_1('#skF_8') = B_2097
      | ~ r2_hidden('#skF_4'('#skF_8',B_2097),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_20351,c_2])).

tff(c_20152,plain,(
    ! [A_2061,B_2062,D_2063] :
      ( k1_funct_1(A_2061,'#skF_3'(A_2061,B_2062)) = '#skF_2'(A_2061,B_2062)
      | k1_funct_1(A_2061,D_2063) != '#skF_4'(A_2061,B_2062)
      | ~ r2_hidden(D_2063,k1_relat_1(A_2061))
      | k2_relat_1(A_2061) = B_2062
      | ~ v1_funct_1(A_2061)
      | ~ v1_relat_1(A_2061) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20154,plain,(
    ! [B_2062,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_2062)) = '#skF_2'('#skF_8',B_2062)
      | D_71 != '#skF_4'('#skF_8',B_2062)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_2062
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19851,c_20152])).

tff(c_20160,plain,(
    ! [B_2062,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_2062)) = '#skF_2'('#skF_8',B_2062)
      | D_71 != '#skF_4'('#skF_8',B_2062)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_2062
      | ~ r2_hidden(D_71,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_20154])).

tff(c_20430,plain,(
    ! [B_2116] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_2116)) = '#skF_2'('#skF_8',B_2116)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_2116)),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_2116
      | ~ r2_hidden('#skF_4'('#skF_8',B_2116),'#skF_8') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_20160])).

tff(c_20435,plain,(
    ! [B_2117] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_2117)) = '#skF_2'('#skF_8',B_2117)
      | k2_relat_1('#skF_8') = B_2117
      | ~ r2_hidden('#skF_4'('#skF_8',B_2117),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_19847,c_20430])).

tff(c_20441,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_20435])).

tff(c_20446,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_20441])).

tff(c_20447,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_8')) = '#skF_2'('#skF_8','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_19849,c_20446])).

tff(c_20454,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_8'),B_2)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_2)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20447,c_14829])).

tff(c_20469,plain,(
    ! [B_2] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_8'),B_2)
      | ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_17481,c_20454])).

tff(c_20477,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_20469])).

tff(c_20483,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8'))
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_20354,c_20477])).

tff(c_20496,plain,
    ( k2_relat_1('#skF_8') = '#skF_8'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_20483])).

tff(c_20497,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_19849,c_20496])).

tff(c_19626,plain,(
    ! [A_1994,B_1995] :
      ( r2_hidden('#skF_3'(A_1994,B_1995),k1_relat_1(A_1994))
      | r2_hidden('#skF_4'(A_1994,B_1995),B_1995)
      | k2_relat_1(A_1994) = B_1995
      | ~ v1_funct_1(A_1994)
      | ~ v1_relat_1(A_1994) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20514,plain,(
    ! [A_2118,B_2119,B_2120] :
      ( r2_hidden('#skF_3'(A_2118,B_2119),B_2120)
      | ~ r1_tarski(k1_relat_1(A_2118),B_2120)
      | r2_hidden('#skF_4'(A_2118,B_2119),B_2119)
      | k2_relat_1(A_2118) = B_2119
      | ~ v1_funct_1(A_2118)
      | ~ v1_relat_1(A_2118) ) ),
    inference(resolution,[status(thm)],[c_19626,c_2])).

tff(c_20517,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_8'),k1_relat_1('#skF_8'))
    | r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_20514,c_20477])).

tff(c_20531,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_94,c_20517])).

tff(c_20533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19849,c_20497,c_20531])).

tff(c_20536,plain,(
    ! [B_2121] : r2_hidden('#skF_2'('#skF_8','#skF_8'),B_2121) ),
    inference(splitRight,[status(thm)],[c_20469])).

tff(c_20546,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_20536,c_30])).

tff(c_20557,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_20546])).

tff(c_20558,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_19849,c_20557])).

tff(c_19844,plain,(
    ! [D_1772,B_2] :
      ( r2_hidden(D_1772,B_2)
      | ~ r2_hidden(D_1772,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19834,c_17195])).

tff(c_20571,plain,(
    ! [B_2] : r2_hidden('#skF_4'('#skF_8','#skF_8'),B_2) ),
    inference(resolution,[status(thm)],[c_20558,c_19844])).

tff(c_20539,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_8'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_20536,c_24])).

tff(c_20551,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_20539])).

tff(c_20593,plain,(
    ! [D_2123] :
      ( k1_funct_1('#skF_8',D_2123) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_2123,k1_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_19849,c_20551])).

tff(c_20733,plain,(
    ! [D_2128] :
      ( k1_funct_1('#skF_8','#skF_9'(D_2128)) != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_2128,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_19847,c_20593])).

tff(c_20738,plain,(
    ! [D_2129] :
      ( D_2129 != '#skF_4'('#skF_8','#skF_8')
      | ~ r2_hidden(D_2129,'#skF_8')
      | ~ r2_hidden(D_2129,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19851,c_20733])).

tff(c_20748,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_8'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_20571,c_20738])).

tff(c_20789,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20571,c_20748])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.37/4.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.85/4.20  
% 10.85/4.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.85/4.21  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 10.85/4.21  
% 10.85/4.21  %Foreground sorts:
% 10.85/4.21  
% 10.85/4.21  
% 10.85/4.21  %Background operators:
% 10.85/4.21  
% 10.85/4.21  
% 10.85/4.21  %Foreground operators:
% 10.85/4.21  tff('#skF_9', type, '#skF_9': $i > $i).
% 10.85/4.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.85/4.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.85/4.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.85/4.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.85/4.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.85/4.21  tff('#skF_7', type, '#skF_7': $i).
% 10.85/4.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.85/4.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.85/4.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.85/4.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.85/4.21  tff('#skF_6', type, '#skF_6': $i).
% 10.85/4.21  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 10.85/4.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 10.85/4.21  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.85/4.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.85/4.21  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.85/4.21  tff('#skF_8', type, '#skF_8': $i).
% 10.85/4.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.85/4.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.85/4.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.85/4.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.85/4.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.85/4.21  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.85/4.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.85/4.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.85/4.21  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 10.85/4.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.85/4.21  
% 11.12/4.27  tff(f_123, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 11.12/4.27  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.12/4.27  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 11.12/4.27  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 11.12/4.27  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.12/4.27  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 11.12/4.27  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 11.12/4.27  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 11.12/4.27  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 11.12/4.27  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 11.12/4.27  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 11.12/4.27  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.12/4.27  tff(c_60, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.12/4.27  tff(c_139, plain, (![A_105, B_106, C_107]: (k2_relset_1(A_105, B_106, C_107)=k2_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.12/4.27  tff(c_143, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_139])).
% 11.12/4.27  tff(c_58, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.12/4.27  tff(c_149, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_58])).
% 11.12/4.27  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.12/4.27  tff(c_82, plain, (![B_80, A_81]: (v1_relat_1(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_41])).
% 11.12/4.27  tff(c_85, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_82])).
% 11.12/4.27  tff(c_88, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_85])).
% 11.12/4.27  tff(c_64, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.12/4.27  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.12/4.27  tff(c_89, plain, (![A_82, B_83]: (~r2_hidden('#skF_1'(A_82, B_83), B_83) | r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.12/4.27  tff(c_94, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_89])).
% 11.12/4.27  tff(c_62, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.12/4.27  tff(c_144, plain, (![A_108, B_109, C_110]: (k1_relset_1(A_108, B_109, C_110)=k1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.12/4.27  tff(c_148, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_144])).
% 11.12/4.27  tff(c_17799, plain, (![B_1829, A_1830, C_1831]: (k1_xboole_0=B_1829 | k1_relset_1(A_1830, B_1829, C_1831)=A_1830 | ~v1_funct_2(C_1831, A_1830, B_1829) | ~m1_subset_1(C_1831, k1_zfmisc_1(k2_zfmisc_1(A_1830, B_1829))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.12/4.27  tff(c_17802, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_17799])).
% 11.12/4.27  tff(c_17805, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_148, c_17802])).
% 11.12/4.27  tff(c_17806, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_17805])).
% 11.12/4.27  tff(c_17963, plain, (![A_1841, B_1842]: (r2_hidden('#skF_3'(A_1841, B_1842), k1_relat_1(A_1841)) | r2_hidden('#skF_4'(A_1841, B_1842), B_1842) | k2_relat_1(A_1841)=B_1842 | ~v1_funct_1(A_1841) | ~v1_relat_1(A_1841))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.12/4.27  tff(c_17972, plain, (![A_1841, B_1842, B_2]: (r2_hidden('#skF_3'(A_1841, B_1842), B_2) | ~r1_tarski(k1_relat_1(A_1841), B_2) | r2_hidden('#skF_4'(A_1841, B_1842), B_1842) | k2_relat_1(A_1841)=B_1842 | ~v1_funct_1(A_1841) | ~v1_relat_1(A_1841))), inference(resolution, [status(thm)], [c_17963, c_2])).
% 11.12/4.27  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.12/4.27  tff(c_115, plain, (![C_93, B_94, A_95]: (v5_relat_1(C_93, B_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.12/4.27  tff(c_119, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_115])).
% 11.12/4.27  tff(c_66, plain, (![D_71]: (k1_funct_1('#skF_8', '#skF_9'(D_71))=D_71 | ~r2_hidden(D_71, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.12/4.27  tff(c_68, plain, (![D_71]: (r2_hidden('#skF_9'(D_71), '#skF_6') | ~r2_hidden(D_71, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 11.12/4.27  tff(c_107, plain, (![C_89, B_90, A_91]: (r2_hidden(C_89, B_90) | ~r2_hidden(C_89, A_91) | ~r1_tarski(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.12/4.27  tff(c_113, plain, (![D_71, B_90]: (r2_hidden('#skF_9'(D_71), B_90) | ~r1_tarski('#skF_6', B_90) | ~r2_hidden(D_71, '#skF_7'))), inference(resolution, [status(thm)], [c_68, c_107])).
% 11.12/4.27  tff(c_129, plain, (![A_101, B_102, B_103]: (r2_hidden('#skF_1'(A_101, B_102), B_103) | ~r1_tarski(A_101, B_103) | r1_tarski(A_101, B_102))), inference(resolution, [status(thm)], [c_6, c_107])).
% 11.12/4.27  tff(c_5318, plain, (![A_649, B_650, B_651, B_652]: (r2_hidden('#skF_1'(A_649, B_650), B_651) | ~r1_tarski(B_652, B_651) | ~r1_tarski(A_649, B_652) | r1_tarski(A_649, B_650))), inference(resolution, [status(thm)], [c_129, c_2])).
% 11.12/4.27  tff(c_6370, plain, (![A_768, B_769, A_770, B_771]: (r2_hidden('#skF_1'(A_768, B_769), A_770) | ~r1_tarski(A_768, k2_relat_1(B_771)) | r1_tarski(A_768, B_769) | ~v5_relat_1(B_771, A_770) | ~v1_relat_1(B_771))), inference(resolution, [status(thm)], [c_14, c_5318])).
% 11.12/4.27  tff(c_6398, plain, (![B_772, B_773, A_774]: (r2_hidden('#skF_1'(k2_relat_1(B_772), B_773), A_774) | r1_tarski(k2_relat_1(B_772), B_773) | ~v5_relat_1(B_772, A_774) | ~v1_relat_1(B_772))), inference(resolution, [status(thm)], [c_94, c_6370])).
% 11.12/4.27  tff(c_258, plain, (![B_146, A_147, C_148]: (k1_xboole_0=B_146 | k1_relset_1(A_147, B_146, C_148)=A_147 | ~v1_funct_2(C_148, A_147, B_146) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.12/4.27  tff(c_261, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_258])).
% 11.12/4.27  tff(c_264, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_148, c_261])).
% 11.12/4.27  tff(c_265, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_264])).
% 11.12/4.27  tff(c_169, plain, (![B_114, A_115]: (r2_hidden(k1_funct_1(B_114, A_115), k2_relat_1(B_114)) | ~r2_hidden(A_115, k1_relat_1(B_114)) | ~v1_funct_1(B_114) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.12/4.27  tff(c_174, plain, (![D_71]: (r2_hidden(D_71, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_169])).
% 11.12/4.27  tff(c_178, plain, (![D_116]: (r2_hidden(D_116, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_116), k1_relat_1('#skF_8')) | ~r2_hidden(D_116, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_174])).
% 11.12/4.27  tff(c_183, plain, (![D_71]: (r2_hidden(D_71, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_71, '#skF_7'))), inference(resolution, [status(thm)], [c_113, c_178])).
% 11.12/4.27  tff(c_184, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_183])).
% 11.12/4.27  tff(c_266, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_184])).
% 11.12/4.27  tff(c_271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_266])).
% 11.12/4.27  tff(c_272, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_264])).
% 11.12/4.27  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.12/4.27  tff(c_186, plain, (![A_119, B_120, B_121, B_122]: (r2_hidden('#skF_1'(A_119, B_120), B_121) | ~r1_tarski(B_122, B_121) | ~r1_tarski(A_119, B_122) | r1_tarski(A_119, B_120))), inference(resolution, [status(thm)], [c_129, c_2])).
% 11.12/4.27  tff(c_196, plain, (![A_123, B_124, A_125]: (r2_hidden('#skF_1'(A_123, B_124), A_125) | ~r1_tarski(A_123, k1_xboole_0) | r1_tarski(A_123, B_124))), inference(resolution, [status(thm)], [c_8, c_186])).
% 11.12/4.27  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.12/4.27  tff(c_206, plain, (![A_129, A_130]: (~r1_tarski(A_129, k1_xboole_0) | r1_tarski(A_129, A_130))), inference(resolution, [status(thm)], [c_196, c_4])).
% 11.12/4.27  tff(c_221, plain, (![B_131, A_132]: (r1_tarski(k2_relat_1(B_131), A_132) | ~v5_relat_1(B_131, k1_xboole_0) | ~v1_relat_1(B_131))), inference(resolution, [status(thm)], [c_14, c_206])).
% 11.12/4.27  tff(c_12, plain, (![B_11, A_10]: (v5_relat_1(B_11, A_10) | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.12/4.27  tff(c_235, plain, (![B_131, A_132]: (v5_relat_1(B_131, A_132) | ~v5_relat_1(B_131, k1_xboole_0) | ~v1_relat_1(B_131))), inference(resolution, [status(thm)], [c_221, c_12])).
% 11.12/4.27  tff(c_318, plain, (![B_155, A_156]: (v5_relat_1(B_155, A_156) | ~v5_relat_1(B_155, '#skF_7') | ~v1_relat_1(B_155))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_235])).
% 11.12/4.27  tff(c_320, plain, (![A_156]: (v5_relat_1('#skF_8', A_156) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_119, c_318])).
% 11.12/4.27  tff(c_323, plain, (![A_156]: (v5_relat_1('#skF_8', A_156))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_320])).
% 11.12/4.27  tff(c_48, plain, (![C_67, A_65]: (k1_xboole_0=C_67 | ~v1_funct_2(C_67, A_65, k1_xboole_0) | k1_xboole_0=A_65 | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.12/4.27  tff(c_356, plain, (![C_164, A_165]: (C_164='#skF_7' | ~v1_funct_2(C_164, A_165, '#skF_7') | A_165='#skF_7' | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_165, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_272, c_272, c_272, c_48])).
% 11.12/4.27  tff(c_359, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_60, c_356])).
% 11.12/4.27  tff(c_362, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_359])).
% 11.12/4.27  tff(c_363, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_362])).
% 11.12/4.27  tff(c_120, plain, (![D_96, B_97]: (r2_hidden('#skF_9'(D_96), B_97) | ~r1_tarski('#skF_6', B_97) | ~r2_hidden(D_96, '#skF_7'))), inference(resolution, [status(thm)], [c_68, c_107])).
% 11.12/4.27  tff(c_158, plain, (![D_111, B_112, B_113]: (r2_hidden('#skF_9'(D_111), B_112) | ~r1_tarski(B_113, B_112) | ~r1_tarski('#skF_6', B_113) | ~r2_hidden(D_111, '#skF_7'))), inference(resolution, [status(thm)], [c_120, c_2])).
% 11.12/4.27  tff(c_167, plain, (![D_111, A_6]: (r2_hidden('#skF_9'(D_111), A_6) | ~r1_tarski('#skF_6', k1_xboole_0) | ~r2_hidden(D_111, '#skF_7'))), inference(resolution, [status(thm)], [c_8, c_158])).
% 11.12/4.27  tff(c_168, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_167])).
% 11.12/4.27  tff(c_282, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_272, c_168])).
% 11.12/4.27  tff(c_370, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_363, c_282])).
% 11.12/4.27  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_370])).
% 11.12/4.27  tff(c_388, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_362])).
% 11.12/4.27  tff(c_404, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_388, c_149])).
% 11.12/4.27  tff(c_284, plain, (![A_6]: (r1_tarski('#skF_7', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_8])).
% 11.12/4.27  tff(c_397, plain, (![A_6]: (r1_tarski('#skF_8', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_284])).
% 11.12/4.27  tff(c_348, plain, (![A_161, B_162]: (r2_hidden('#skF_3'(A_161, B_162), k1_relat_1(A_161)) | r2_hidden('#skF_4'(A_161, B_162), B_162) | k2_relat_1(A_161)=B_162 | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_353, plain, (![A_161, B_162, B_2]: (r2_hidden('#skF_3'(A_161, B_162), B_2) | ~r1_tarski(k1_relat_1(A_161), B_2) | r2_hidden('#skF_4'(A_161, B_162), B_162) | k2_relat_1(A_161)=B_162 | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(resolution, [status(thm)], [c_348, c_2])).
% 11.12/4.27  tff(c_424, plain, (![A_167, B_168]: (k1_funct_1(A_167, '#skF_3'(A_167, B_168))='#skF_2'(A_167, B_168) | r2_hidden('#skF_4'(A_167, B_168), B_168) | k2_relat_1(A_167)=B_168 | ~v1_funct_1(A_167) | ~v1_relat_1(A_167))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_36, plain, (![B_55, A_54]: (r2_hidden(k1_funct_1(B_55, A_54), k2_relat_1(B_55)) | ~r2_hidden(A_54, k1_relat_1(B_55)) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.12/4.27  tff(c_1028, plain, (![A_282, B_283]: (r2_hidden('#skF_2'(A_282, B_283), k2_relat_1(A_282)) | ~r2_hidden('#skF_3'(A_282, B_283), k1_relat_1(A_282)) | ~v1_funct_1(A_282) | ~v1_relat_1(A_282) | r2_hidden('#skF_4'(A_282, B_283), B_283) | k2_relat_1(A_282)=B_283 | ~v1_funct_1(A_282) | ~v1_relat_1(A_282))), inference(superposition, [status(thm), theory('equality')], [c_424, c_36])).
% 11.12/4.27  tff(c_1031, plain, (![A_161, B_162]: (r2_hidden('#skF_2'(A_161, B_162), k2_relat_1(A_161)) | ~r1_tarski(k1_relat_1(A_161), k1_relat_1(A_161)) | r2_hidden('#skF_4'(A_161, B_162), B_162) | k2_relat_1(A_161)=B_162 | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(resolution, [status(thm)], [c_353, c_1028])).
% 11.12/4.27  tff(c_1054, plain, (![A_287, B_288]: (r2_hidden('#skF_2'(A_287, B_288), k2_relat_1(A_287)) | r2_hidden('#skF_4'(A_287, B_288), B_288) | k2_relat_1(A_287)=B_288 | ~v1_funct_1(A_287) | ~v1_relat_1(A_287))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1031])).
% 11.12/4.27  tff(c_239, plain, (![A_139, C_140]: (r2_hidden('#skF_5'(A_139, k2_relat_1(A_139), C_140), k1_relat_1(A_139)) | ~r2_hidden(C_140, k2_relat_1(A_139)) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_242, plain, (![A_139, C_140, B_2]: (r2_hidden('#skF_5'(A_139, k2_relat_1(A_139), C_140), B_2) | ~r1_tarski(k1_relat_1(A_139), B_2) | ~r2_hidden(C_140, k2_relat_1(A_139)) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(resolution, [status(thm)], [c_239, c_2])).
% 11.12/4.27  tff(c_20, plain, (![A_14, C_50]: (k1_funct_1(A_14, '#skF_5'(A_14, k2_relat_1(A_14), C_50))=C_50 | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_643, plain, (![A_216, B_217, A_218, B_219]: (r2_hidden('#skF_1'(A_216, B_217), A_218) | ~r1_tarski(A_216, k2_relat_1(B_219)) | r1_tarski(A_216, B_217) | ~v5_relat_1(B_219, A_218) | ~v1_relat_1(B_219))), inference(resolution, [status(thm)], [c_14, c_186])).
% 11.12/4.27  tff(c_754, plain, (![B_249, B_250, A_251, B_252]: (r2_hidden('#skF_1'(k2_relat_1(B_249), B_250), A_251) | r1_tarski(k2_relat_1(B_249), B_250) | ~v5_relat_1(B_252, A_251) | ~v1_relat_1(B_252) | ~v5_relat_1(B_249, k2_relat_1(B_252)) | ~v1_relat_1(B_249))), inference(resolution, [status(thm)], [c_14, c_643])).
% 11.12/4.27  tff(c_756, plain, (![B_249, B_250, A_156]: (r2_hidden('#skF_1'(k2_relat_1(B_249), B_250), A_156) | r1_tarski(k2_relat_1(B_249), B_250) | ~v1_relat_1('#skF_8') | ~v5_relat_1(B_249, k2_relat_1('#skF_8')) | ~v1_relat_1(B_249))), inference(resolution, [status(thm)], [c_323, c_754])).
% 11.12/4.27  tff(c_763, plain, (![B_253, B_254, A_255]: (r2_hidden('#skF_1'(k2_relat_1(B_253), B_254), A_255) | r1_tarski(k2_relat_1(B_253), B_254) | ~v5_relat_1(B_253, k2_relat_1('#skF_8')) | ~v1_relat_1(B_253))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_756])).
% 11.12/4.27  tff(c_772, plain, (![B_256, A_257]: (r1_tarski(k2_relat_1(B_256), A_257) | ~v5_relat_1(B_256, k2_relat_1('#skF_8')) | ~v1_relat_1(B_256))), inference(resolution, [status(thm)], [c_763, c_4])).
% 11.12/4.27  tff(c_775, plain, (![A_257]: (r1_tarski(k2_relat_1('#skF_8'), A_257) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_323, c_772])).
% 11.12/4.27  tff(c_781, plain, (![A_257]: (r1_tarski(k2_relat_1('#skF_8'), A_257))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_775])).
% 11.12/4.27  tff(c_790, plain, (![A_260]: (r1_tarski(k2_relat_1('#skF_8'), A_260))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_775])).
% 11.12/4.27  tff(c_590, plain, (![B_203, A_204, B_205]: (r2_hidden(k1_funct_1(B_203, A_204), B_205) | ~r1_tarski(k2_relat_1(B_203), B_205) | ~r2_hidden(A_204, k1_relat_1(B_203)) | ~v1_funct_1(B_203) | ~v1_relat_1(B_203))), inference(resolution, [status(thm)], [c_169, c_2])).
% 11.12/4.27  tff(c_602, plain, (![B_203, A_204, B_2, B_205]: (r2_hidden(k1_funct_1(B_203, A_204), B_2) | ~r1_tarski(B_205, B_2) | ~r1_tarski(k2_relat_1(B_203), B_205) | ~r2_hidden(A_204, k1_relat_1(B_203)) | ~v1_funct_1(B_203) | ~v1_relat_1(B_203))), inference(resolution, [status(thm)], [c_590, c_2])).
% 11.12/4.27  tff(c_892, plain, (![B_269, A_270, A_271]: (r2_hidden(k1_funct_1(B_269, A_270), A_271) | ~r1_tarski(k2_relat_1(B_269), k2_relat_1('#skF_8')) | ~r2_hidden(A_270, k1_relat_1(B_269)) | ~v1_funct_1(B_269) | ~v1_relat_1(B_269))), inference(resolution, [status(thm)], [c_790, c_602])).
% 11.12/4.27  tff(c_895, plain, (![A_270, A_271]: (r2_hidden(k1_funct_1('#skF_8', A_270), A_271) | ~r2_hidden(A_270, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_781, c_892])).
% 11.12/4.27  tff(c_913, plain, (![A_272, A_273]: (r2_hidden(k1_funct_1('#skF_8', A_272), A_273) | ~r2_hidden(A_272, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_895])).
% 11.12/4.27  tff(c_926, plain, (![C_50, A_273]: (r2_hidden(C_50, A_273) | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_50), k1_relat_1('#skF_8')) | ~r2_hidden(C_50, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_913])).
% 11.12/4.27  tff(c_935, plain, (![C_275, A_276]: (r2_hidden(C_275, A_276) | ~r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_275), k1_relat_1('#skF_8')) | ~r2_hidden(C_275, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_926])).
% 11.12/4.27  tff(c_938, plain, (![C_140, A_276]: (r2_hidden(C_140, A_276) | ~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8')) | ~r2_hidden(C_140, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_242, c_935])).
% 11.12/4.27  tff(c_944, plain, (![C_140, A_276]: (r2_hidden(C_140, A_276) | ~r2_hidden(C_140, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_94, c_938])).
% 11.12/4.27  tff(c_1057, plain, (![B_288, A_276]: (r2_hidden('#skF_2'('#skF_8', B_288), A_276) | r2_hidden('#skF_4'('#skF_8', B_288), B_288) | k2_relat_1('#skF_8')=B_288 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1054, c_944])).
% 11.12/4.27  tff(c_1079, plain, (![B_289, A_290]: (r2_hidden('#skF_2'('#skF_8', B_289), A_290) | r2_hidden('#skF_4'('#skF_8', B_289), B_289) | k2_relat_1('#skF_8')=B_289)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_1057])).
% 11.12/4.27  tff(c_30, plain, (![A_14, B_36]: (~r2_hidden('#skF_2'(A_14, B_36), B_36) | r2_hidden('#skF_4'(A_14, B_36), B_36) | k2_relat_1(A_14)=B_36 | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_1089, plain, (![A_290]: (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | r2_hidden('#skF_4'('#skF_8', A_290), A_290) | k2_relat_1('#skF_8')=A_290)), inference(resolution, [status(thm)], [c_1079, c_30])).
% 11.12/4.27  tff(c_1113, plain, (![A_292]: (r2_hidden('#skF_4'('#skF_8', A_292), A_292) | k2_relat_1('#skF_8')=A_292)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_1089])).
% 11.12/4.27  tff(c_1122, plain, (![A_293, B_294]: (r2_hidden('#skF_4'('#skF_8', A_293), B_294) | ~r1_tarski(A_293, B_294) | k2_relat_1('#skF_8')=A_293)), inference(resolution, [status(thm)], [c_1113, c_2])).
% 11.12/4.27  tff(c_1138, plain, (![A_297, B_298, B_299]: (r2_hidden('#skF_4'('#skF_8', A_297), B_298) | ~r1_tarski(B_299, B_298) | ~r1_tarski(A_297, B_299) | k2_relat_1('#skF_8')=A_297)), inference(resolution, [status(thm)], [c_1122, c_2])).
% 11.12/4.27  tff(c_1167, plain, (![A_305, A_306, B_307]: (r2_hidden('#skF_4'('#skF_8', A_305), A_306) | ~r1_tarski(A_305, k2_relat_1(B_307)) | k2_relat_1('#skF_8')=A_305 | ~v5_relat_1(B_307, A_306) | ~v1_relat_1(B_307))), inference(resolution, [status(thm)], [c_14, c_1138])).
% 11.12/4.27  tff(c_1176, plain, (![A_306, B_307]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), A_306) | k2_relat_1('#skF_8')='#skF_8' | ~v5_relat_1(B_307, A_306) | ~v1_relat_1(B_307))), inference(resolution, [status(thm)], [c_397, c_1167])).
% 11.12/4.27  tff(c_1191, plain, (![A_308, B_309]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), A_308) | ~v5_relat_1(B_309, A_308) | ~v1_relat_1(B_309))), inference(negUnitSimplification, [status(thm)], [c_404, c_1176])).
% 11.12/4.27  tff(c_1193, plain, (![A_156]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), A_156) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_323, c_1191])).
% 11.12/4.27  tff(c_1198, plain, (![A_156]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), A_156))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1193])).
% 11.12/4.27  tff(c_22, plain, (![A_14, C_50]: (r2_hidden('#skF_5'(A_14, k2_relat_1(A_14), C_50), k1_relat_1(A_14)) | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_1038, plain, (![A_161, B_162]: (r2_hidden('#skF_2'(A_161, B_162), k2_relat_1(A_161)) | r2_hidden('#skF_4'(A_161, B_162), B_162) | k2_relat_1(A_161)=B_162 | ~v1_funct_1(A_161) | ~v1_relat_1(A_161))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1031])).
% 11.12/4.27  tff(c_204, plain, (![A_123, A_125]: (~r1_tarski(A_123, k1_xboole_0) | r1_tarski(A_123, A_125))), inference(resolution, [status(thm)], [c_196, c_4])).
% 11.12/4.27  tff(c_280, plain, (![A_123, A_125]: (~r1_tarski(A_123, '#skF_7') | r1_tarski(A_123, A_125))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_204])).
% 11.12/4.27  tff(c_473, plain, (![A_169, A_170]: (~r1_tarski(A_169, '#skF_8') | r1_tarski(A_169, A_170))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_280])).
% 11.12/4.27  tff(c_485, plain, (![B_11, A_170]: (r1_tarski(k2_relat_1(B_11), A_170) | ~v5_relat_1(B_11, '#skF_8') | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_14, c_473])).
% 11.12/4.27  tff(c_1006, plain, (![B_279, A_280, A_281]: (r2_hidden(k1_funct_1(B_279, A_280), A_281) | ~r2_hidden(A_280, k1_relat_1(B_279)) | ~v1_funct_1(B_279) | ~v5_relat_1(B_279, '#skF_8') | ~v1_relat_1(B_279))), inference(resolution, [status(thm)], [c_485, c_892])).
% 11.12/4.27  tff(c_1277, plain, (![C_324, A_325, A_326]: (r2_hidden(C_324, A_325) | ~r2_hidden('#skF_5'(A_326, k2_relat_1(A_326), C_324), k1_relat_1(A_326)) | ~v1_funct_1(A_326) | ~v5_relat_1(A_326, '#skF_8') | ~v1_relat_1(A_326) | ~r2_hidden(C_324, k2_relat_1(A_326)) | ~v1_funct_1(A_326) | ~v1_relat_1(A_326))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1006])).
% 11.12/4.27  tff(c_1280, plain, (![C_140, A_325, A_139]: (r2_hidden(C_140, A_325) | ~v5_relat_1(A_139, '#skF_8') | ~r1_tarski(k1_relat_1(A_139), k1_relat_1(A_139)) | ~r2_hidden(C_140, k2_relat_1(A_139)) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(resolution, [status(thm)], [c_242, c_1277])).
% 11.12/4.27  tff(c_1287, plain, (![C_327, A_328, A_329]: (r2_hidden(C_327, A_328) | ~v5_relat_1(A_329, '#skF_8') | ~r2_hidden(C_327, k2_relat_1(A_329)) | ~v1_funct_1(A_329) | ~v1_relat_1(A_329))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1280])).
% 11.12/4.27  tff(c_1420, plain, (![A_339, B_340, A_341]: (r2_hidden('#skF_2'(A_339, B_340), A_341) | ~v5_relat_1(A_339, '#skF_8') | r2_hidden('#skF_4'(A_339, B_340), B_340) | k2_relat_1(A_339)=B_340 | ~v1_funct_1(A_339) | ~v1_relat_1(A_339))), inference(resolution, [status(thm)], [c_1038, c_1287])).
% 11.12/4.27  tff(c_1452, plain, (![A_342, A_343]: (~v5_relat_1(A_342, '#skF_8') | r2_hidden('#skF_4'(A_342, A_343), A_343) | k2_relat_1(A_342)=A_343 | ~v1_funct_1(A_342) | ~v1_relat_1(A_342))), inference(resolution, [status(thm)], [c_1420, c_30])).
% 11.12/4.27  tff(c_1476, plain, (![A_346, A_347, B_348]: (r2_hidden('#skF_4'(A_346, A_347), B_348) | ~r1_tarski(A_347, B_348) | ~v5_relat_1(A_346, '#skF_8') | k2_relat_1(A_346)=A_347 | ~v1_funct_1(A_346) | ~v1_relat_1(A_346))), inference(resolution, [status(thm)], [c_1452, c_2])).
% 11.12/4.27  tff(c_1651, plain, (![A_382, A_383, B_384, B_385]: (r2_hidden('#skF_4'(A_382, A_383), B_384) | ~r1_tarski(B_385, B_384) | ~r1_tarski(A_383, B_385) | ~v5_relat_1(A_382, '#skF_8') | k2_relat_1(A_382)=A_383 | ~v1_funct_1(A_382) | ~v1_relat_1(A_382))), inference(resolution, [status(thm)], [c_1476, c_2])).
% 11.12/4.27  tff(c_2885, plain, (![A_567, A_568, A_569, B_570]: (r2_hidden('#skF_4'(A_567, A_568), A_569) | ~r1_tarski(A_568, k2_relat_1(B_570)) | ~v5_relat_1(A_567, '#skF_8') | k2_relat_1(A_567)=A_568 | ~v1_funct_1(A_567) | ~v1_relat_1(A_567) | ~v5_relat_1(B_570, A_569) | ~v1_relat_1(B_570))), inference(resolution, [status(thm)], [c_14, c_1651])).
% 11.12/4.27  tff(c_2906, plain, (![A_571, A_572, B_573]: (r2_hidden('#skF_4'(A_571, '#skF_8'), A_572) | ~v5_relat_1(A_571, '#skF_8') | k2_relat_1(A_571)='#skF_8' | ~v1_funct_1(A_571) | ~v1_relat_1(A_571) | ~v5_relat_1(B_573, A_572) | ~v1_relat_1(B_573))), inference(resolution, [status(thm)], [c_397, c_2885])).
% 11.12/4.27  tff(c_2908, plain, (![A_571, A_156]: (r2_hidden('#skF_4'(A_571, '#skF_8'), A_156) | ~v5_relat_1(A_571, '#skF_8') | k2_relat_1(A_571)='#skF_8' | ~v1_funct_1(A_571) | ~v1_relat_1(A_571) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_323, c_2906])).
% 11.12/4.27  tff(c_2913, plain, (![A_571, A_156]: (r2_hidden('#skF_4'(A_571, '#skF_8'), A_156) | ~v5_relat_1(A_571, '#skF_8') | k2_relat_1(A_571)='#skF_8' | ~v1_funct_1(A_571) | ~v1_relat_1(A_571))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2908])).
% 11.12/4.27  tff(c_531, plain, (![A_183, B_184, D_185]: (r2_hidden('#skF_3'(A_183, B_184), k1_relat_1(A_183)) | k1_funct_1(A_183, D_185)!='#skF_4'(A_183, B_184) | ~r2_hidden(D_185, k1_relat_1(A_183)) | k2_relat_1(A_183)=B_184 | ~v1_funct_1(A_183) | ~v1_relat_1(A_183))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_537, plain, (![A_14, B_184, C_50]: (r2_hidden('#skF_3'(A_14, B_184), k1_relat_1(A_14)) | C_50!='#skF_4'(A_14, B_184) | ~r2_hidden('#skF_5'(A_14, k2_relat_1(A_14), C_50), k1_relat_1(A_14)) | k2_relat_1(A_14)=B_184 | ~v1_funct_1(A_14) | ~v1_relat_1(A_14) | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_20, c_531])).
% 11.12/4.27  tff(c_2927, plain, (![A_576, B_577]: (r2_hidden('#skF_3'(A_576, B_577), k1_relat_1(A_576)) | ~r2_hidden('#skF_5'(A_576, k2_relat_1(A_576), '#skF_4'(A_576, B_577)), k1_relat_1(A_576)) | k2_relat_1(A_576)=B_577 | ~v1_funct_1(A_576) | ~v1_relat_1(A_576) | ~r2_hidden('#skF_4'(A_576, B_577), k2_relat_1(A_576)) | ~v1_funct_1(A_576) | ~v1_relat_1(A_576))), inference(reflexivity, [status(thm), theory('equality')], [c_537])).
% 11.12/4.27  tff(c_2939, plain, (![A_139, B_577]: (r2_hidden('#skF_3'(A_139, B_577), k1_relat_1(A_139)) | k2_relat_1(A_139)=B_577 | ~r1_tarski(k1_relat_1(A_139), k1_relat_1(A_139)) | ~r2_hidden('#skF_4'(A_139, B_577), k2_relat_1(A_139)) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(resolution, [status(thm)], [c_242, c_2927])).
% 11.12/4.27  tff(c_2950, plain, (![A_578, B_579]: (r2_hidden('#skF_3'(A_578, B_579), k1_relat_1(A_578)) | k2_relat_1(A_578)=B_579 | ~r2_hidden('#skF_4'(A_578, B_579), k2_relat_1(A_578)) | ~v1_funct_1(A_578) | ~v1_relat_1(A_578))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2939])).
% 11.12/4.27  tff(c_2954, plain, (![A_580, B_581, B_582]: (r2_hidden('#skF_3'(A_580, B_581), B_582) | ~r1_tarski(k1_relat_1(A_580), B_582) | k2_relat_1(A_580)=B_581 | ~r2_hidden('#skF_4'(A_580, B_581), k2_relat_1(A_580)) | ~v1_funct_1(A_580) | ~v1_relat_1(A_580))), inference(resolution, [status(thm)], [c_2950, c_2])).
% 11.12/4.27  tff(c_3101, plain, (![A_571, B_582]: (r2_hidden('#skF_3'(A_571, '#skF_8'), B_582) | ~r1_tarski(k1_relat_1(A_571), B_582) | ~v5_relat_1(A_571, '#skF_8') | k2_relat_1(A_571)='#skF_8' | ~v1_funct_1(A_571) | ~v1_relat_1(A_571))), inference(resolution, [status(thm)], [c_2913, c_2954])).
% 11.12/4.27  tff(c_580, plain, (![A_200, B_201, D_202]: (k1_funct_1(A_200, '#skF_3'(A_200, B_201))='#skF_2'(A_200, B_201) | k1_funct_1(A_200, D_202)!='#skF_4'(A_200, B_201) | ~r2_hidden(D_202, k1_relat_1(A_200)) | k2_relat_1(A_200)=B_201 | ~v1_funct_1(A_200) | ~v1_relat_1(A_200))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_586, plain, (![A_14, B_201, C_50]: (k1_funct_1(A_14, '#skF_3'(A_14, B_201))='#skF_2'(A_14, B_201) | C_50!='#skF_4'(A_14, B_201) | ~r2_hidden('#skF_5'(A_14, k2_relat_1(A_14), C_50), k1_relat_1(A_14)) | k2_relat_1(A_14)=B_201 | ~v1_funct_1(A_14) | ~v1_relat_1(A_14) | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_20, c_580])).
% 11.12/4.27  tff(c_3248, plain, (![A_596, B_597]: (k1_funct_1(A_596, '#skF_3'(A_596, B_597))='#skF_2'(A_596, B_597) | ~r2_hidden('#skF_5'(A_596, k2_relat_1(A_596), '#skF_4'(A_596, B_597)), k1_relat_1(A_596)) | k2_relat_1(A_596)=B_597 | ~v1_funct_1(A_596) | ~v1_relat_1(A_596) | ~r2_hidden('#skF_4'(A_596, B_597), k2_relat_1(A_596)) | ~v1_funct_1(A_596) | ~v1_relat_1(A_596))), inference(reflexivity, [status(thm), theory('equality')], [c_586])).
% 11.12/4.27  tff(c_3324, plain, (![A_609, B_610]: (k1_funct_1(A_609, '#skF_3'(A_609, B_610))='#skF_2'(A_609, B_610) | k2_relat_1(A_609)=B_610 | ~r2_hidden('#skF_4'(A_609, B_610), k2_relat_1(A_609)) | ~v1_funct_1(A_609) | ~v1_relat_1(A_609))), inference(resolution, [status(thm)], [c_22, c_3248])).
% 11.12/4.27  tff(c_3490, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1198, c_3324])).
% 11.12/4.27  tff(c_3578, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8') | k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_3490])).
% 11.12/4.27  tff(c_3579, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_404, c_3578])).
% 11.12/4.27  tff(c_712, plain, (![B_236, A_237, B_238, B_239]: (r2_hidden(k1_funct_1(B_236, A_237), B_238) | ~r1_tarski(B_239, B_238) | ~r1_tarski(k2_relat_1(B_236), B_239) | ~r2_hidden(A_237, k1_relat_1(B_236)) | ~v1_funct_1(B_236) | ~v1_relat_1(B_236))), inference(resolution, [status(thm)], [c_590, c_2])).
% 11.12/4.27  tff(c_1785, plain, (![B_415, A_416, A_417, B_418]: (r2_hidden(k1_funct_1(B_415, A_416), A_417) | ~r1_tarski(k2_relat_1(B_415), k2_relat_1(B_418)) | ~r2_hidden(A_416, k1_relat_1(B_415)) | ~v1_funct_1(B_415) | ~v1_relat_1(B_415) | ~v5_relat_1(B_418, A_417) | ~v1_relat_1(B_418))), inference(resolution, [status(thm)], [c_14, c_712])).
% 11.12/4.27  tff(c_1803, plain, (![B_415, A_416, A_417]: (r2_hidden(k1_funct_1(B_415, A_416), A_417) | ~r2_hidden(A_416, k1_relat_1(B_415)) | ~v1_funct_1(B_415) | ~v5_relat_1(B_415, A_417) | ~v1_relat_1(B_415))), inference(resolution, [status(thm)], [c_94, c_1785])).
% 11.12/4.27  tff(c_3603, plain, (![A_417]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), A_417) | ~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_417) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3579, c_1803])).
% 11.12/4.27  tff(c_3632, plain, (![A_417]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), A_417) | ~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_323, c_64, c_3603])).
% 11.12/4.27  tff(c_3646, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_3632])).
% 11.12/4.27  tff(c_3650, plain, (~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8')) | ~v5_relat_1('#skF_8', '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_3101, c_3646])).
% 11.12/4.27  tff(c_3695, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_323, c_94, c_3650])).
% 11.12/4.27  tff(c_3697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_404, c_3695])).
% 11.12/4.27  tff(c_3700, plain, (![A_615]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), A_615))), inference(splitRight, [status(thm)], [c_3632])).
% 11.12/4.27  tff(c_24, plain, (![A_14, B_36, D_49]: (~r2_hidden('#skF_2'(A_14, B_36), B_36) | k1_funct_1(A_14, D_49)!='#skF_4'(A_14, B_36) | ~r2_hidden(D_49, k1_relat_1(A_14)) | k2_relat_1(A_14)=B_36 | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_3709, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_49, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_3700, c_24])).
% 11.12/4.27  tff(c_3722, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_49, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_3709])).
% 11.12/4.27  tff(c_3733, plain, (![D_616]: (k1_funct_1('#skF_8', D_616)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_616, k1_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_404, c_3722])).
% 11.12/4.27  tff(c_4084, plain, (![C_50]: (k1_funct_1('#skF_8', '#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_50))!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(C_50, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_22, c_3733])).
% 11.12/4.27  tff(c_4759, plain, (![C_628]: (k1_funct_1('#skF_8', '#skF_5'('#skF_8', k2_relat_1('#skF_8'), C_628))!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(C_628, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_4084])).
% 11.12/4.27  tff(c_4763, plain, (![C_50]: (C_50!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(C_50, k2_relat_1('#skF_8')) | ~r2_hidden(C_50, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_4759])).
% 11.12/4.27  tff(c_4768, plain, (![C_630]: (C_630!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(C_630, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_4763])).
% 11.12/4.27  tff(c_5192, plain, $false, inference(resolution, [status(thm)], [c_1198, c_4768])).
% 11.12/4.27  tff(c_5200, plain, (![D_631]: (r2_hidden(D_631, k2_relat_1('#skF_8')) | ~r2_hidden(D_631, '#skF_7'))), inference(splitRight, [status(thm)], [c_183])).
% 11.12/4.27  tff(c_5213, plain, (![D_633, B_634]: (r2_hidden(D_633, B_634) | ~r1_tarski(k2_relat_1('#skF_8'), B_634) | ~r2_hidden(D_633, '#skF_7'))), inference(resolution, [status(thm)], [c_5200, c_2])).
% 11.12/4.27  tff(c_5216, plain, (![D_633, A_10]: (r2_hidden(D_633, A_10) | ~r2_hidden(D_633, '#skF_7') | ~v5_relat_1('#skF_8', A_10) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_14, c_5213])).
% 11.12/4.27  tff(c_5222, plain, (![D_633, A_10]: (r2_hidden(D_633, A_10) | ~r2_hidden(D_633, '#skF_7') | ~v5_relat_1('#skF_8', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5216])).
% 11.12/4.27  tff(c_6757, plain, (![B_811, B_812, A_813]: (r2_hidden('#skF_1'(k2_relat_1(B_811), B_812), A_813) | ~v5_relat_1('#skF_8', A_813) | r1_tarski(k2_relat_1(B_811), B_812) | ~v5_relat_1(B_811, '#skF_7') | ~v1_relat_1(B_811))), inference(resolution, [status(thm)], [c_6398, c_5222])).
% 11.12/4.27  tff(c_6782, plain, (![A_813, B_811]: (~v5_relat_1('#skF_8', A_813) | r1_tarski(k2_relat_1(B_811), A_813) | ~v5_relat_1(B_811, '#skF_7') | ~v1_relat_1(B_811))), inference(resolution, [status(thm)], [c_6757, c_4])).
% 11.12/4.27  tff(c_6171, plain, (![B_742, A_743, C_744]: (k1_xboole_0=B_742 | k1_relset_1(A_743, B_742, C_744)=A_743 | ~v1_funct_2(C_744, A_743, B_742) | ~m1_subset_1(C_744, k1_zfmisc_1(k2_zfmisc_1(A_743, B_742))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.12/4.27  tff(c_6174, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_6171])).
% 11.12/4.27  tff(c_6177, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_148, c_6174])).
% 11.12/4.27  tff(c_6178, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_6177])).
% 11.12/4.27  tff(c_6256, plain, (![A_751, B_752]: (r2_hidden('#skF_3'(A_751, B_752), k1_relat_1(A_751)) | r2_hidden('#skF_4'(A_751, B_752), B_752) | k2_relat_1(A_751)=B_752 | ~v1_funct_1(A_751) | ~v1_relat_1(A_751))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_6265, plain, (![A_751, B_752, B_2]: (r2_hidden('#skF_3'(A_751, B_752), B_2) | ~r1_tarski(k1_relat_1(A_751), B_2) | r2_hidden('#skF_4'(A_751, B_752), B_752) | k2_relat_1(A_751)=B_752 | ~v1_funct_1(A_751) | ~v1_relat_1(A_751))), inference(resolution, [status(thm)], [c_6256, c_2])).
% 11.12/4.27  tff(c_32, plain, (![A_14, B_36]: (k1_funct_1(A_14, '#skF_3'(A_14, B_36))='#skF_2'(A_14, B_36) | r2_hidden('#skF_4'(A_14, B_36), B_36) | k2_relat_1(A_14)=B_36 | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_6948, plain, (![A_827, B_828, D_829]: (k1_funct_1(A_827, '#skF_3'(A_827, B_828))='#skF_2'(A_827, B_828) | k1_funct_1(A_827, D_829)!='#skF_4'(A_827, B_828) | ~r2_hidden(D_829, k1_relat_1(A_827)) | k2_relat_1(A_827)=B_828 | ~v1_funct_1(A_827) | ~v1_relat_1(A_827))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_6954, plain, (![B_828, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_828))='#skF_2'('#skF_8', B_828) | D_71!='#skF_4'('#skF_8', B_828) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_828 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_6948])).
% 11.12/4.27  tff(c_6956, plain, (![B_828, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_828))='#skF_2'('#skF_8', B_828) | D_71!='#skF_4'('#skF_8', B_828) | ~r2_hidden('#skF_9'(D_71), '#skF_6') | k2_relat_1('#skF_8')=B_828 | ~r2_hidden(D_71, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_6178, c_6954])).
% 11.12/4.27  tff(c_7293, plain, (![B_875]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_875))='#skF_2'('#skF_8', B_875) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_875)), '#skF_6') | k2_relat_1('#skF_8')=B_875 | ~r2_hidden('#skF_4'('#skF_8', B_875), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_6956])).
% 11.12/4.27  tff(c_7296, plain, (![B_875]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_875))='#skF_2'('#skF_8', B_875) | k2_relat_1('#skF_8')=B_875 | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden('#skF_4'('#skF_8', B_875), '#skF_7'))), inference(resolution, [status(thm)], [c_113, c_7293])).
% 11.12/4.27  tff(c_7337, plain, (![B_878]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_878))='#skF_2'('#skF_8', B_878) | k2_relat_1('#skF_8')=B_878 | ~r2_hidden('#skF_4'('#skF_8', B_878), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_7296])).
% 11.12/4.27  tff(c_7351, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_7337])).
% 11.12/4.27  tff(c_7362, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_7351])).
% 11.12/4.27  tff(c_7363, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_7362])).
% 11.12/4.27  tff(c_7375, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_7363, c_36])).
% 11.12/4.27  tff(c_7386, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_6178, c_7375])).
% 11.12/4.27  tff(c_7388, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_7386])).
% 11.12/4.27  tff(c_7394, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_6265, c_7388])).
% 11.12/4.27  tff(c_7422, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_94, c_6178, c_7394])).
% 11.12/4.27  tff(c_7423, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_7422])).
% 11.12/4.27  tff(c_6725, plain, (![A_804, B_805, D_806]: (r2_hidden('#skF_3'(A_804, B_805), k1_relat_1(A_804)) | k1_funct_1(A_804, D_806)!='#skF_4'(A_804, B_805) | ~r2_hidden(D_806, k1_relat_1(A_804)) | k2_relat_1(A_804)=B_805 | ~v1_funct_1(A_804) | ~v1_relat_1(A_804))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_6731, plain, (![B_805, D_71]: (r2_hidden('#skF_3'('#skF_8', B_805), k1_relat_1('#skF_8')) | D_71!='#skF_4'('#skF_8', B_805) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_805 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_6725])).
% 11.12/4.27  tff(c_6733, plain, (![B_805, D_71]: (r2_hidden('#skF_3'('#skF_8', B_805), '#skF_6') | D_71!='#skF_4'('#skF_8', B_805) | ~r2_hidden('#skF_9'(D_71), '#skF_6') | k2_relat_1('#skF_8')=B_805 | ~r2_hidden(D_71, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_6178, c_6178, c_6731])).
% 11.12/4.27  tff(c_7051, plain, (![B_839]: (r2_hidden('#skF_3'('#skF_8', B_839), '#skF_6') | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_839)), '#skF_6') | k2_relat_1('#skF_8')=B_839 | ~r2_hidden('#skF_4'('#skF_8', B_839), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_6733])).
% 11.12/4.27  tff(c_7054, plain, (![B_839]: (r2_hidden('#skF_3'('#skF_8', B_839), '#skF_6') | k2_relat_1('#skF_8')=B_839 | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden('#skF_4'('#skF_8', B_839), '#skF_7'))), inference(resolution, [status(thm)], [c_113, c_7051])).
% 11.12/4.27  tff(c_7060, plain, (![B_839]: (r2_hidden('#skF_3'('#skF_8', B_839), '#skF_6') | k2_relat_1('#skF_8')=B_839 | ~r2_hidden('#skF_4'('#skF_8', B_839), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_7054])).
% 11.12/4.27  tff(c_7406, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_7060, c_7388])).
% 11.12/4.27  tff(c_7437, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_7406])).
% 11.12/4.27  tff(c_7510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7423, c_7437])).
% 11.12/4.27  tff(c_7511, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_7386])).
% 11.12/4.27  tff(c_7531, plain, (![B_883]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_883) | ~r1_tarski(k2_relat_1('#skF_8'), B_883))), inference(resolution, [status(thm)], [c_7511, c_2])).
% 11.12/4.27  tff(c_7541, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_7531, c_30])).
% 11.12/4.27  tff(c_7554, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_7541])).
% 11.12/4.27  tff(c_7555, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_7554])).
% 11.12/4.27  tff(c_7605, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_7555])).
% 11.12/4.27  tff(c_7608, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_6782, c_7605])).
% 11.12/4.27  tff(c_7618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_119, c_7608])).
% 11.12/4.27  tff(c_7620, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_7555])).
% 11.12/4.27  tff(c_7537, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_49, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_7531, c_24])).
% 11.12/4.27  tff(c_7550, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_49, '#skF_6') | k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_6178, c_7537])).
% 11.12/4.27  tff(c_7551, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_49, '#skF_6') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_149, c_7550])).
% 11.12/4.27  tff(c_7857, plain, (![D_895]: (k1_funct_1('#skF_8', D_895)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_895, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7620, c_7551])).
% 11.12/4.27  tff(c_7985, plain, (![D_71]: (k1_funct_1('#skF_8', '#skF_9'(D_71))!='#skF_4'('#skF_8', '#skF_7') | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden(D_71, '#skF_7'))), inference(resolution, [status(thm)], [c_113, c_7857])).
% 11.12/4.27  tff(c_8075, plain, (![D_900]: (k1_funct_1('#skF_8', '#skF_9'(D_900))!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_900, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_7985])).
% 11.12/4.27  tff(c_8079, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_66, c_8075])).
% 11.12/4.27  tff(c_7619, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_7555])).
% 11.12/4.27  tff(c_8081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8079, c_7619])).
% 11.12/4.27  tff(c_8082, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_6177])).
% 11.12/4.27  tff(c_5350, plain, (![A_654, B_655, A_656]: (r2_hidden('#skF_1'(A_654, B_655), A_656) | ~r1_tarski(A_654, k1_xboole_0) | r1_tarski(A_654, B_655))), inference(resolution, [status(thm)], [c_8, c_5318])).
% 11.12/4.27  tff(c_5368, plain, (![A_657, A_658]: (~r1_tarski(A_657, k1_xboole_0) | r1_tarski(A_657, A_658))), inference(resolution, [status(thm)], [c_5350, c_4])).
% 11.12/4.27  tff(c_5384, plain, (![B_661, A_662]: (r1_tarski(k2_relat_1(B_661), A_662) | ~v5_relat_1(B_661, k1_xboole_0) | ~v1_relat_1(B_661))), inference(resolution, [status(thm)], [c_14, c_5368])).
% 11.12/4.27  tff(c_5207, plain, (![D_631, B_2]: (r2_hidden(D_631, B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r2_hidden(D_631, '#skF_7'))), inference(resolution, [status(thm)], [c_5200, c_2])).
% 11.12/4.27  tff(c_5392, plain, (![D_631, A_662]: (r2_hidden(D_631, A_662) | ~r2_hidden(D_631, '#skF_7') | ~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_5384, c_5207])).
% 11.12/4.27  tff(c_5402, plain, (![D_631, A_662]: (r2_hidden(D_631, A_662) | ~r2_hidden(D_631, '#skF_7') | ~v5_relat_1('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5392])).
% 11.12/4.27  tff(c_5406, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_5402])).
% 11.12/4.27  tff(c_8088, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_8082, c_5406])).
% 11.12/4.27  tff(c_8100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_8088])).
% 11.12/4.27  tff(c_8102, plain, (v5_relat_1('#skF_8', k1_xboole_0)), inference(splitRight, [status(thm)], [c_5402])).
% 11.12/4.27  tff(c_5404, plain, (![B_661, A_662]: (v5_relat_1(B_661, A_662) | ~v5_relat_1(B_661, k1_xboole_0) | ~v1_relat_1(B_661))), inference(resolution, [status(thm)], [c_5384, c_12])).
% 11.12/4.27  tff(c_8104, plain, (![A_662]: (v5_relat_1('#skF_8', A_662) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_8102, c_5404])).
% 11.12/4.27  tff(c_8110, plain, (![A_662]: (v5_relat_1('#skF_8', A_662))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_8104])).
% 11.12/4.27  tff(c_8389, plain, (![A_944, B_945, A_946, B_947]: (r2_hidden('#skF_1'(A_944, B_945), A_946) | ~r1_tarski(A_944, k2_relat_1(B_947)) | r1_tarski(A_944, B_945) | ~v5_relat_1(B_947, A_946) | ~v1_relat_1(B_947))), inference(resolution, [status(thm)], [c_14, c_5318])).
% 11.12/4.27  tff(c_8828, plain, (![B_1027, B_1028, A_1029, B_1030]: (r2_hidden('#skF_1'(k2_relat_1(B_1027), B_1028), A_1029) | r1_tarski(k2_relat_1(B_1027), B_1028) | ~v5_relat_1(B_1030, A_1029) | ~v1_relat_1(B_1030) | ~v5_relat_1(B_1027, k2_relat_1(B_1030)) | ~v1_relat_1(B_1027))), inference(resolution, [status(thm)], [c_14, c_8389])).
% 11.12/4.27  tff(c_8830, plain, (![B_1027, B_1028, A_662]: (r2_hidden('#skF_1'(k2_relat_1(B_1027), B_1028), A_662) | r1_tarski(k2_relat_1(B_1027), B_1028) | ~v1_relat_1('#skF_8') | ~v5_relat_1(B_1027, k2_relat_1('#skF_8')) | ~v1_relat_1(B_1027))), inference(resolution, [status(thm)], [c_8110, c_8828])).
% 11.12/4.27  tff(c_8840, plain, (![B_1031, B_1032, A_1033]: (r2_hidden('#skF_1'(k2_relat_1(B_1031), B_1032), A_1033) | r1_tarski(k2_relat_1(B_1031), B_1032) | ~v5_relat_1(B_1031, k2_relat_1('#skF_8')) | ~v1_relat_1(B_1031))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_8830])).
% 11.12/4.27  tff(c_8858, plain, (![B_1034, A_1035]: (r1_tarski(k2_relat_1(B_1034), A_1035) | ~v5_relat_1(B_1034, k2_relat_1('#skF_8')) | ~v1_relat_1(B_1034))), inference(resolution, [status(thm)], [c_8840, c_4])).
% 11.12/4.27  tff(c_8861, plain, (![A_1035]: (r1_tarski(k2_relat_1('#skF_8'), A_1035) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_8110, c_8858])).
% 11.12/4.27  tff(c_8869, plain, (![A_1035]: (r1_tarski(k2_relat_1('#skF_8'), A_1035))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_8861])).
% 11.12/4.27  tff(c_8293, plain, (![B_926, A_927, C_928]: (k1_xboole_0=B_926 | k1_relset_1(A_927, B_926, C_928)=A_927 | ~v1_funct_2(C_928, A_927, B_926) | ~m1_subset_1(C_928, k1_zfmisc_1(k2_zfmisc_1(A_927, B_926))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.12/4.27  tff(c_8296, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_8293])).
% 11.12/4.27  tff(c_8299, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_148, c_8296])).
% 11.12/4.27  tff(c_8300, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_8299])).
% 11.12/4.27  tff(c_8453, plain, (![A_954, B_955]: (r2_hidden('#skF_3'(A_954, B_955), k1_relat_1(A_954)) | r2_hidden('#skF_4'(A_954, B_955), B_955) | k2_relat_1(A_954)=B_955 | ~v1_funct_1(A_954) | ~v1_relat_1(A_954))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_8461, plain, (![B_955]: (r2_hidden('#skF_3'('#skF_8', B_955), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_955), B_955) | k2_relat_1('#skF_8')=B_955 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_8300, c_8453])).
% 11.12/4.27  tff(c_8466, plain, (![B_956]: (r2_hidden('#skF_3'('#skF_8', B_956), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_956), B_956) | k2_relat_1('#skF_8')=B_956)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_8461])).
% 11.12/4.27  tff(c_8472, plain, (![B_956, B_2]: (r2_hidden('#skF_3'('#skF_8', B_956), B_2) | ~r1_tarski('#skF_6', B_2) | r2_hidden('#skF_4'('#skF_8', B_956), B_956) | k2_relat_1('#skF_8')=B_956)), inference(resolution, [status(thm)], [c_8466, c_2])).
% 11.12/4.27  tff(c_8610, plain, (![A_982, B_983]: (k1_funct_1(A_982, '#skF_3'(A_982, B_983))='#skF_2'(A_982, B_983) | r2_hidden('#skF_4'(A_982, B_983), B_983) | k2_relat_1(A_982)=B_983 | ~v1_funct_1(A_982) | ~v1_relat_1(A_982))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_9418, plain, (![A_1085, B_1086]: (r2_hidden('#skF_2'(A_1085, B_1086), k2_relat_1(A_1085)) | ~r2_hidden('#skF_3'(A_1085, B_1086), k1_relat_1(A_1085)) | ~v1_funct_1(A_1085) | ~v1_relat_1(A_1085) | r2_hidden('#skF_4'(A_1085, B_1086), B_1086) | k2_relat_1(A_1085)=B_1086 | ~v1_funct_1(A_1085) | ~v1_relat_1(A_1085))), inference(superposition, [status(thm), theory('equality')], [c_8610, c_36])).
% 11.12/4.27  tff(c_9441, plain, (![B_956]: (r2_hidden('#skF_2'('#skF_8', B_956), k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | r2_hidden('#skF_4'('#skF_8', B_956), B_956) | k2_relat_1('#skF_8')=B_956)), inference(resolution, [status(thm)], [c_8472, c_9418])).
% 11.12/4.27  tff(c_9471, plain, (![B_1087]: (r2_hidden('#skF_2'('#skF_8', B_1087), k2_relat_1('#skF_8')) | r2_hidden('#skF_4'('#skF_8', B_1087), B_1087) | k2_relat_1('#skF_8')=B_1087)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_8300, c_88, c_64, c_9441])).
% 11.12/4.27  tff(c_9482, plain, (![B_1087, B_2]: (r2_hidden('#skF_2'('#skF_8', B_1087), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | r2_hidden('#skF_4'('#skF_8', B_1087), B_1087) | k2_relat_1('#skF_8')=B_1087)), inference(resolution, [status(thm)], [c_9471, c_2])).
% 11.12/4.27  tff(c_9500, plain, (![B_1088, B_1089]: (r2_hidden('#skF_2'('#skF_8', B_1088), B_1089) | r2_hidden('#skF_4'('#skF_8', B_1088), B_1088) | k2_relat_1('#skF_8')=B_1088)), inference(demodulation, [status(thm), theory('equality')], [c_8869, c_9482])).
% 11.12/4.27  tff(c_9510, plain, (![B_1089]: (~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | r2_hidden('#skF_4'('#skF_8', B_1089), B_1089) | k2_relat_1('#skF_8')=B_1089)), inference(resolution, [status(thm)], [c_9500, c_30])).
% 11.12/4.27  tff(c_9534, plain, (![B_1090]: (r2_hidden('#skF_4'('#skF_8', B_1090), B_1090) | k2_relat_1('#skF_8')=B_1090)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_9510])).
% 11.12/4.27  tff(c_8101, plain, (![D_631, A_662]: (r2_hidden(D_631, A_662) | ~r2_hidden(D_631, '#skF_7'))), inference(splitRight, [status(thm)], [c_5402])).
% 11.12/4.27  tff(c_9540, plain, (![A_662]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), A_662) | k2_relat_1('#skF_8')='#skF_7')), inference(resolution, [status(thm)], [c_9534, c_8101])).
% 11.12/4.27  tff(c_9547, plain, (![A_662]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), A_662))), inference(negUnitSimplification, [status(thm)], [c_149, c_9540])).
% 11.12/4.27  tff(c_8874, plain, (![A_1036, B_1037, D_1038]: (r2_hidden('#skF_3'(A_1036, B_1037), k1_relat_1(A_1036)) | k1_funct_1(A_1036, D_1038)!='#skF_4'(A_1036, B_1037) | ~r2_hidden(D_1038, k1_relat_1(A_1036)) | k2_relat_1(A_1036)=B_1037 | ~v1_funct_1(A_1036) | ~v1_relat_1(A_1036))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_8882, plain, (![B_1037, D_71]: (r2_hidden('#skF_3'('#skF_8', B_1037), k1_relat_1('#skF_8')) | D_71!='#skF_4'('#skF_8', B_1037) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1037 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_8874])).
% 11.12/4.27  tff(c_8884, plain, (![B_1037, D_71]: (r2_hidden('#skF_3'('#skF_8', B_1037), '#skF_6') | D_71!='#skF_4'('#skF_8', B_1037) | ~r2_hidden('#skF_9'(D_71), '#skF_6') | k2_relat_1('#skF_8')=B_1037 | ~r2_hidden(D_71, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_8300, c_8300, c_8882])).
% 11.12/4.27  tff(c_9349, plain, (![B_1075]: (r2_hidden('#skF_3'('#skF_8', B_1075), '#skF_6') | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1075)), '#skF_6') | k2_relat_1('#skF_8')=B_1075 | ~r2_hidden('#skF_4'('#skF_8', B_1075), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_8884])).
% 11.12/4.27  tff(c_9352, plain, (![B_1075]: (r2_hidden('#skF_3'('#skF_8', B_1075), '#skF_6') | k2_relat_1('#skF_8')=B_1075 | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden('#skF_4'('#skF_8', B_1075), '#skF_7'))), inference(resolution, [status(thm)], [c_113, c_9349])).
% 11.12/4.27  tff(c_9360, plain, (![B_1076]: (r2_hidden('#skF_3'('#skF_8', B_1076), '#skF_6') | k2_relat_1('#skF_8')=B_1076 | ~r2_hidden('#skF_4'('#skF_8', B_1076), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_9352])).
% 11.12/4.27  tff(c_9363, plain, (![B_1076, B_2]: (r2_hidden('#skF_3'('#skF_8', B_1076), B_2) | ~r1_tarski('#skF_6', B_2) | k2_relat_1('#skF_8')=B_1076 | ~r2_hidden('#skF_4'('#skF_8', B_1076), '#skF_7'))), inference(resolution, [status(thm)], [c_9360, c_2])).
% 11.12/4.27  tff(c_9008, plain, (![A_1049, B_1050, D_1051]: (k1_funct_1(A_1049, '#skF_3'(A_1049, B_1050))='#skF_2'(A_1049, B_1050) | k1_funct_1(A_1049, D_1051)!='#skF_4'(A_1049, B_1050) | ~r2_hidden(D_1051, k1_relat_1(A_1049)) | k2_relat_1(A_1049)=B_1050 | ~v1_funct_1(A_1049) | ~v1_relat_1(A_1049))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_9016, plain, (![B_1050, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1050))='#skF_2'('#skF_8', B_1050) | D_71!='#skF_4'('#skF_8', B_1050) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1050 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_9008])).
% 11.12/4.27  tff(c_9018, plain, (![B_1050, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1050))='#skF_2'('#skF_8', B_1050) | D_71!='#skF_4'('#skF_8', B_1050) | ~r2_hidden('#skF_9'(D_71), '#skF_6') | k2_relat_1('#skF_8')=B_1050 | ~r2_hidden(D_71, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_8300, c_9016])).
% 11.12/4.27  tff(c_9639, plain, (![B_1106]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1106))='#skF_2'('#skF_8', B_1106) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1106)), '#skF_6') | k2_relat_1('#skF_8')=B_1106 | ~r2_hidden('#skF_4'('#skF_8', B_1106), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_9018])).
% 11.12/4.27  tff(c_9642, plain, (![B_1106]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1106))='#skF_2'('#skF_8', B_1106) | k2_relat_1('#skF_8')=B_1106 | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden('#skF_4'('#skF_8', B_1106), '#skF_7'))), inference(resolution, [status(thm)], [c_113, c_9639])).
% 11.12/4.27  tff(c_9650, plain, (![B_1107]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1107))='#skF_2'('#skF_8', B_1107) | k2_relat_1('#skF_8')=B_1107 | ~r2_hidden('#skF_4'('#skF_8', B_1107), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_9642])).
% 11.12/4.27  tff(c_9690, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_9650])).
% 11.12/4.27  tff(c_9712, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_9690])).
% 11.12/4.27  tff(c_9713, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_9712])).
% 11.12/4.27  tff(c_8373, plain, (![B_941, A_942, B_943]: (r2_hidden(k1_funct_1(B_941, A_942), B_943) | ~r1_tarski(k2_relat_1(B_941), B_943) | ~r2_hidden(A_942, k1_relat_1(B_941)) | ~v1_funct_1(B_941) | ~v1_relat_1(B_941))), inference(resolution, [status(thm)], [c_169, c_2])).
% 11.12/4.27  tff(c_8727, plain, (![B_1009, A_1010, B_1011, B_1012]: (r2_hidden(k1_funct_1(B_1009, A_1010), B_1011) | ~r1_tarski(B_1012, B_1011) | ~r1_tarski(k2_relat_1(B_1009), B_1012) | ~r2_hidden(A_1010, k1_relat_1(B_1009)) | ~v1_funct_1(B_1009) | ~v1_relat_1(B_1009))), inference(resolution, [status(thm)], [c_8373, c_2])).
% 11.12/4.27  tff(c_8745, plain, (![B_1009, A_1010, A_6]: (r2_hidden(k1_funct_1(B_1009, A_1010), A_6) | ~r1_tarski(k2_relat_1(B_1009), k1_xboole_0) | ~r2_hidden(A_1010, k1_relat_1(B_1009)) | ~v1_funct_1(B_1009) | ~v1_relat_1(B_1009))), inference(resolution, [status(thm)], [c_8, c_8727])).
% 11.12/4.27  tff(c_9732, plain, (![A_6]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), A_6) | ~r1_tarski(k2_relat_1('#skF_8'), k1_xboole_0) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_9713, c_8745])).
% 11.12/4.27  tff(c_9757, plain, (![A_6]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), A_6) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_8300, c_8869, c_9732])).
% 11.12/4.27  tff(c_9773, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_9757])).
% 11.12/4.27  tff(c_9776, plain, (~r1_tarski('#skF_6', '#skF_6') | k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_9363, c_9773])).
% 11.12/4.27  tff(c_9785, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_9547, c_94, c_9776])).
% 11.12/4.27  tff(c_9787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_9785])).
% 11.12/4.27  tff(c_9790, plain, (![A_1111]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), A_1111))), inference(splitRight, [status(thm)], [c_9757])).
% 11.12/4.27  tff(c_9796, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_49, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_9790, c_24])).
% 11.12/4.27  tff(c_9810, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_49, '#skF_6') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_8300, c_9796])).
% 11.12/4.27  tff(c_9842, plain, (![D_1113]: (k1_funct_1('#skF_8', D_1113)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1113, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_149, c_9810])).
% 11.12/4.27  tff(c_10007, plain, (![D_1117]: (k1_funct_1('#skF_8', '#skF_9'(D_1117))!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1117, '#skF_7'))), inference(resolution, [status(thm)], [c_68, c_9842])).
% 11.12/4.27  tff(c_10021, plain, (![D_1121]: (D_1121!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1121, '#skF_7') | ~r2_hidden(D_1121, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_10007])).
% 11.12/4.27  tff(c_10042, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_9547, c_10021])).
% 11.12/4.27  tff(c_10114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9547, c_10042])).
% 11.12/4.27  tff(c_10115, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_8299])).
% 11.12/4.27  tff(c_10136, plain, (![C_1124, A_1125]: (C_1124='#skF_7' | ~v1_funct_2(C_1124, A_1125, '#skF_7') | A_1125='#skF_7' | ~m1_subset_1(C_1124, k1_zfmisc_1(k2_zfmisc_1(A_1125, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_10115, c_10115, c_10115, c_10115, c_48])).
% 11.12/4.27  tff(c_10139, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_60, c_10136])).
% 11.12/4.27  tff(c_10142, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_10139])).
% 11.12/4.27  tff(c_10143, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_10142])).
% 11.12/4.27  tff(c_5225, plain, (![D_637, A_638]: (r2_hidden(D_637, A_638) | ~r2_hidden(D_637, '#skF_7') | ~v5_relat_1('#skF_8', A_638))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_5216])).
% 11.12/4.27  tff(c_5236, plain, (![D_71, A_638]: (r2_hidden('#skF_9'(D_71), A_638) | ~v5_relat_1('#skF_8', A_638) | ~r1_tarski('#skF_6', '#skF_7') | ~r2_hidden(D_71, '#skF_7'))), inference(resolution, [status(thm)], [c_113, c_5225])).
% 11.12/4.27  tff(c_5252, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_5236])).
% 11.12/4.27  tff(c_10166, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10143, c_5252])).
% 11.12/4.27  tff(c_10180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_10166])).
% 11.12/4.27  tff(c_10181, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_10142])).
% 11.12/4.27  tff(c_112, plain, (![A_1, B_2, B_90]: (r2_hidden('#skF_1'(A_1, B_2), B_90) | ~r1_tarski(A_1, B_90) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_107])).
% 11.12/4.27  tff(c_8163, plain, (![D_905, A_906]: (r2_hidden(D_905, A_906) | ~r2_hidden(D_905, '#skF_7'))), inference(splitRight, [status(thm)], [c_5402])).
% 11.12/4.27  tff(c_8189, plain, (![A_910, B_911, A_912]: (r2_hidden('#skF_1'(A_910, B_911), A_912) | ~r1_tarski(A_910, '#skF_7') | r1_tarski(A_910, B_911))), inference(resolution, [status(thm)], [c_112, c_8163])).
% 11.12/4.27  tff(c_8206, plain, (![A_910, A_912]: (~r1_tarski(A_910, '#skF_7') | r1_tarski(A_910, A_912))), inference(resolution, [status(thm)], [c_8189, c_4])).
% 11.12/4.27  tff(c_10292, plain, (![A_1137, A_1138]: (~r1_tarski(A_1137, '#skF_8') | r1_tarski(A_1137, A_1138))), inference(demodulation, [status(thm), theory('equality')], [c_10181, c_8206])).
% 11.12/4.27  tff(c_10304, plain, (![B_11, A_1138]: (r1_tarski(k2_relat_1(B_11), A_1138) | ~v5_relat_1(B_11, '#skF_8') | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_14, c_10292])).
% 11.12/4.27  tff(c_10203, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_10181, c_149])).
% 11.12/4.27  tff(c_10366, plain, (![A_1151, B_1152]: (r2_hidden('#skF_3'(A_1151, B_1152), k1_relat_1(A_1151)) | r2_hidden('#skF_4'(A_1151, B_1152), B_1152) | k2_relat_1(A_1151)=B_1152 | ~v1_funct_1(A_1151) | ~v1_relat_1(A_1151))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_10372, plain, (![A_1151, B_1152, B_2]: (r2_hidden('#skF_3'(A_1151, B_1152), B_2) | ~r1_tarski(k1_relat_1(A_1151), B_2) | r2_hidden('#skF_4'(A_1151, B_1152), B_1152) | k2_relat_1(A_1151)=B_1152 | ~v1_funct_1(A_1151) | ~v1_relat_1(A_1151))), inference(resolution, [status(thm)], [c_10366, c_2])).
% 11.12/4.27  tff(c_5194, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_183])).
% 11.12/4.27  tff(c_123, plain, (![D_96, B_2, B_97]: (r2_hidden('#skF_9'(D_96), B_2) | ~r1_tarski(B_97, B_2) | ~r1_tarski('#skF_6', B_97) | ~r2_hidden(D_96, '#skF_7'))), inference(resolution, [status(thm)], [c_120, c_2])).
% 11.12/4.27  tff(c_5196, plain, (![D_96]: (r2_hidden('#skF_9'(D_96), k1_relat_1('#skF_8')) | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden(D_96, '#skF_7'))), inference(resolution, [status(thm)], [c_5194, c_123])).
% 11.12/4.27  tff(c_5199, plain, (![D_96]: (r2_hidden('#skF_9'(D_96), k1_relat_1('#skF_8')) | ~r2_hidden(D_96, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_5196])).
% 11.12/4.27  tff(c_10322, plain, (![D_1142]: (r2_hidden('#skF_9'(D_1142), k1_relat_1('#skF_8')) | ~r2_hidden(D_1142, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_10181, c_5199])).
% 11.12/4.27  tff(c_10325, plain, (![D_1142, B_2]: (r2_hidden('#skF_9'(D_1142), B_2) | ~r1_tarski(k1_relat_1('#skF_8'), B_2) | ~r2_hidden(D_1142, '#skF_8'))), inference(resolution, [status(thm)], [c_10322, c_2])).
% 11.12/4.27  tff(c_10206, plain, (![D_71]: (k1_funct_1('#skF_8', '#skF_9'(D_71))=D_71 | ~r2_hidden(D_71, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_10181, c_66])).
% 11.12/4.27  tff(c_10678, plain, (![A_1221, B_1222, D_1223]: (k1_funct_1(A_1221, '#skF_3'(A_1221, B_1222))='#skF_2'(A_1221, B_1222) | k1_funct_1(A_1221, D_1223)!='#skF_4'(A_1221, B_1222) | ~r2_hidden(D_1223, k1_relat_1(A_1221)) | k2_relat_1(A_1221)=B_1222 | ~v1_funct_1(A_1221) | ~v1_relat_1(A_1221))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_10682, plain, (![B_1222, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1222))='#skF_2'('#skF_8', B_1222) | D_71!='#skF_4'('#skF_8', B_1222) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1222 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10206, c_10678])).
% 11.12/4.27  tff(c_10686, plain, (![B_1222, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1222))='#skF_2'('#skF_8', B_1222) | D_71!='#skF_4'('#skF_8', B_1222) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1222 | ~r2_hidden(D_71, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_10682])).
% 11.12/4.27  tff(c_10968, plain, (![B_1259]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1259))='#skF_2'('#skF_8', B_1259) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1259)), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1259 | ~r2_hidden('#skF_4'('#skF_8', B_1259), '#skF_8'))), inference(reflexivity, [status(thm), theory('equality')], [c_10686])).
% 11.12/4.27  tff(c_10971, plain, (![B_1259]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1259))='#skF_2'('#skF_8', B_1259) | k2_relat_1('#skF_8')=B_1259 | ~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_4'('#skF_8', B_1259), '#skF_8'))), inference(resolution, [status(thm)], [c_10325, c_10968])).
% 11.12/4.27  tff(c_11054, plain, (![B_1263]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1263))='#skF_2'('#skF_8', B_1263) | k2_relat_1('#skF_8')=B_1263 | ~r2_hidden('#skF_4'('#skF_8', B_1263), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_10971])).
% 11.12/4.27  tff(c_11060, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_11054])).
% 11.12/4.27  tff(c_11065, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8') | k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_11060])).
% 11.12/4.27  tff(c_11066, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_10203, c_11065])).
% 11.12/4.27  tff(c_11081, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_8'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_11066, c_36])).
% 11.12/4.27  tff(c_11094, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_8'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_11081])).
% 11.12/4.27  tff(c_11096, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_11094])).
% 11.12/4.27  tff(c_11113, plain, (~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8')) | r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_10372, c_11096])).
% 11.12/4.27  tff(c_11125, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_94, c_11113])).
% 11.12/4.27  tff(c_11126, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_10203, c_11125])).
% 11.12/4.27  tff(c_10200, plain, (![D_96]: (r2_hidden('#skF_9'(D_96), k1_relat_1('#skF_8')) | ~r2_hidden(D_96, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_10181, c_5199])).
% 11.12/4.27  tff(c_10603, plain, (![A_1201, B_1202, D_1203]: (r2_hidden('#skF_3'(A_1201, B_1202), k1_relat_1(A_1201)) | k1_funct_1(A_1201, D_1203)!='#skF_4'(A_1201, B_1202) | ~r2_hidden(D_1203, k1_relat_1(A_1201)) | k2_relat_1(A_1201)=B_1202 | ~v1_funct_1(A_1201) | ~v1_relat_1(A_1201))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_10607, plain, (![B_1202, D_71]: (r2_hidden('#skF_3'('#skF_8', B_1202), k1_relat_1('#skF_8')) | D_71!='#skF_4'('#skF_8', B_1202) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1202 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10206, c_10603])).
% 11.12/4.27  tff(c_10611, plain, (![B_1202, D_71]: (r2_hidden('#skF_3'('#skF_8', B_1202), k1_relat_1('#skF_8')) | D_71!='#skF_4'('#skF_8', B_1202) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1202 | ~r2_hidden(D_71, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_10607])).
% 11.12/4.27  tff(c_10858, plain, (![B_1248]: (r2_hidden('#skF_3'('#skF_8', B_1248), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1248)), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1248 | ~r2_hidden('#skF_4'('#skF_8', B_1248), '#skF_8'))), inference(reflexivity, [status(thm), theory('equality')], [c_10611])).
% 11.12/4.27  tff(c_10874, plain, (![B_1248]: (r2_hidden('#skF_3'('#skF_8', B_1248), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1248 | ~r2_hidden('#skF_4'('#skF_8', B_1248), '#skF_8'))), inference(resolution, [status(thm)], [c_10200, c_10858])).
% 11.12/4.27  tff(c_11116, plain, (k2_relat_1('#skF_8')='#skF_8' | ~r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_10874, c_11096])).
% 11.12/4.27  tff(c_11129, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_10203, c_11116])).
% 11.12/4.27  tff(c_11153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11126, c_11129])).
% 11.12/4.27  tff(c_11154, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_8'), k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_11094])).
% 11.12/4.27  tff(c_11162, plain, (![B_1267]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), B_1267) | ~r1_tarski(k2_relat_1('#skF_8'), B_1267))), inference(resolution, [status(thm)], [c_11154, c_2])).
% 11.12/4.27  tff(c_11169, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_11162, c_30])).
% 11.12/4.27  tff(c_11181, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_11169])).
% 11.12/4.27  tff(c_11182, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_10203, c_11181])).
% 11.12/4.27  tff(c_11193, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_11182])).
% 11.12/4.27  tff(c_11213, plain, (~v5_relat_1('#skF_8', '#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_10304, c_11193])).
% 11.12/4.27  tff(c_11221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_8110, c_11213])).
% 11.12/4.27  tff(c_11222, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_11182])).
% 11.12/4.27  tff(c_10192, plain, (![D_631, A_662]: (r2_hidden(D_631, A_662) | ~r2_hidden(D_631, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_10181, c_8101])).
% 11.12/4.27  tff(c_11447, plain, (![A_662]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), A_662))), inference(resolution, [status(thm)], [c_11222, c_10192])).
% 11.12/4.27  tff(c_10205, plain, (![D_71, B_90]: (r2_hidden('#skF_9'(D_71), B_90) | ~r1_tarski('#skF_6', B_90) | ~r2_hidden(D_71, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_10181, c_113])).
% 11.12/4.27  tff(c_11223, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_11182])).
% 11.12/4.27  tff(c_10190, plain, (![A_910, A_912]: (~r1_tarski(A_910, '#skF_8') | r1_tarski(A_910, A_912))), inference(demodulation, [status(thm), theory('equality')], [c_10181, c_8206])).
% 11.12/4.27  tff(c_11253, plain, (![A_912]: (r1_tarski(k2_relat_1('#skF_8'), A_912))), inference(resolution, [status(thm)], [c_11223, c_10190])).
% 11.12/4.27  tff(c_11165, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_49, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_8'))), inference(resolution, [status(thm)], [c_11162, c_24])).
% 11.12/4.27  tff(c_11177, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_49, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_8' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_11165])).
% 11.12/4.27  tff(c_11178, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_49, k1_relat_1('#skF_8')) | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_10203, c_11177])).
% 11.12/4.27  tff(c_11323, plain, (![D_1273]: (k1_funct_1('#skF_8', D_1273)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_1273, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_11253, c_11178])).
% 11.12/4.27  tff(c_11383, plain, (![D_71]: (k1_funct_1('#skF_8', '#skF_9'(D_71))!='#skF_4'('#skF_8', '#skF_8') | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_71, '#skF_8'))), inference(resolution, [status(thm)], [c_10205, c_11323])).
% 11.12/4.27  tff(c_11530, plain, (![D_1279]: (k1_funct_1('#skF_8', '#skF_9'(D_1279))!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_1279, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_5194, c_11383])).
% 11.12/4.27  tff(c_11537, plain, (![D_1280]: (D_1280!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_1280, '#skF_8') | ~r2_hidden(D_1280, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10206, c_11530])).
% 11.12/4.27  tff(c_11544, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_11447, c_11537])).
% 11.12/4.27  tff(c_11587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11447, c_11544])).
% 11.12/4.27  tff(c_11589, plain, (r1_tarski('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_5236])).
% 11.12/4.27  tff(c_5238, plain, (![A_639]: (r1_tarski(A_639, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_639, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_5200, c_4])).
% 11.12/4.27  tff(c_5247, plain, (![A_1]: (~r1_tarski(A_1, '#skF_7') | r1_tarski(A_1, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_112, c_5238])).
% 11.12/4.27  tff(c_11764, plain, (![A_1308, B_1309, B_1310, B_1311]: (r2_hidden('#skF_1'(A_1308, B_1309), B_1310) | ~r1_tarski(B_1311, B_1310) | ~r1_tarski(A_1308, B_1311) | r1_tarski(A_1308, B_1309))), inference(resolution, [status(thm)], [c_129, c_2])).
% 11.12/4.27  tff(c_12498, plain, (![A_1388, B_1389, A_1390]: (r2_hidden('#skF_1'(A_1388, B_1389), k2_relat_1('#skF_8')) | ~r1_tarski(A_1388, A_1390) | r1_tarski(A_1388, B_1389) | ~r1_tarski(A_1390, '#skF_7'))), inference(resolution, [status(thm)], [c_5247, c_11764])).
% 11.12/4.27  tff(c_12508, plain, (![B_1389]: (r2_hidden('#skF_1'('#skF_6', B_1389), k2_relat_1('#skF_8')) | r1_tarski('#skF_6', B_1389) | ~r1_tarski('#skF_7', '#skF_7'))), inference(resolution, [status(thm)], [c_11589, c_12498])).
% 11.12/4.27  tff(c_12550, plain, (![B_1393]: (r2_hidden('#skF_1'('#skF_6', B_1393), k2_relat_1('#skF_8')) | r1_tarski('#skF_6', B_1393))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_12508])).
% 11.12/4.27  tff(c_12596, plain, (![B_1394, B_1395]: (r2_hidden('#skF_1'('#skF_6', B_1394), B_1395) | ~r1_tarski(k2_relat_1('#skF_8'), B_1395) | r1_tarski('#skF_6', B_1394))), inference(resolution, [status(thm)], [c_12550, c_2])).
% 11.12/4.27  tff(c_12612, plain, (![B_1394, A_10]: (r2_hidden('#skF_1'('#skF_6', B_1394), A_10) | ~v5_relat_1('#skF_8', A_10) | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7') | r1_tarski('#skF_6', B_1394))), inference(resolution, [status(thm)], [c_12596, c_5222])).
% 11.12/4.27  tff(c_12888, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_12612])).
% 11.12/4.27  tff(c_12897, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_14, c_12888])).
% 11.12/4.27  tff(c_12905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_119, c_12897])).
% 11.12/4.27  tff(c_12907, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_12612])).
% 11.12/4.27  tff(c_12327, plain, (![B_1369, A_1370, C_1371]: (k1_xboole_0=B_1369 | k1_relset_1(A_1370, B_1369, C_1371)=A_1370 | ~v1_funct_2(C_1371, A_1370, B_1369) | ~m1_subset_1(C_1371, k1_zfmisc_1(k2_zfmisc_1(A_1370, B_1369))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.12/4.27  tff(c_12330, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_12327])).
% 11.12/4.27  tff(c_12333, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_148, c_12330])).
% 11.12/4.27  tff(c_12334, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_12333])).
% 11.12/4.27  tff(c_12417, plain, (![A_1380, B_1381]: (r2_hidden('#skF_3'(A_1380, B_1381), k1_relat_1(A_1380)) | r2_hidden('#skF_4'(A_1380, B_1381), B_1381) | k2_relat_1(A_1380)=B_1381 | ~v1_funct_1(A_1380) | ~v1_relat_1(A_1380))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_12426, plain, (![A_1380, B_1381, B_2]: (r2_hidden('#skF_3'(A_1380, B_1381), B_2) | ~r1_tarski(k1_relat_1(A_1380), B_2) | r2_hidden('#skF_4'(A_1380, B_1381), B_1381) | k2_relat_1(A_1380)=B_1381 | ~v1_funct_1(A_1380) | ~v1_relat_1(A_1380))), inference(resolution, [status(thm)], [c_12417, c_2])).
% 11.12/4.27  tff(c_13157, plain, (![A_1429, B_1430, D_1431]: (k1_funct_1(A_1429, '#skF_3'(A_1429, B_1430))='#skF_2'(A_1429, B_1430) | k1_funct_1(A_1429, D_1431)!='#skF_4'(A_1429, B_1430) | ~r2_hidden(D_1431, k1_relat_1(A_1429)) | k2_relat_1(A_1429)=B_1430 | ~v1_funct_1(A_1429) | ~v1_relat_1(A_1429))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_13163, plain, (![B_1430, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1430))='#skF_2'('#skF_8', B_1430) | D_71!='#skF_4'('#skF_8', B_1430) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1430 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_13157])).
% 11.12/4.27  tff(c_13165, plain, (![B_1430, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1430))='#skF_2'('#skF_8', B_1430) | D_71!='#skF_4'('#skF_8', B_1430) | ~r2_hidden('#skF_9'(D_71), '#skF_6') | k2_relat_1('#skF_8')=B_1430 | ~r2_hidden(D_71, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_12334, c_13163])).
% 11.12/4.27  tff(c_13773, plain, (![B_1498]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1498))='#skF_2'('#skF_8', B_1498) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1498)), '#skF_6') | k2_relat_1('#skF_8')=B_1498 | ~r2_hidden('#skF_4'('#skF_8', B_1498), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_13165])).
% 11.12/4.27  tff(c_13933, plain, (![B_1501]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1501))='#skF_2'('#skF_8', B_1501) | k2_relat_1('#skF_8')=B_1501 | ~r2_hidden('#skF_4'('#skF_8', B_1501), '#skF_7'))), inference(resolution, [status(thm)], [c_68, c_13773])).
% 11.12/4.27  tff(c_13945, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_13933])).
% 11.12/4.27  tff(c_13952, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_13945])).
% 11.12/4.27  tff(c_13953, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_13952])).
% 11.12/4.27  tff(c_13965, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_13953, c_36])).
% 11.12/4.27  tff(c_13976, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_12334, c_13965])).
% 11.12/4.27  tff(c_13978, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_13976])).
% 11.12/4.27  tff(c_14003, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_12426, c_13978])).
% 11.12/4.27  tff(c_14027, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_94, c_12334, c_14003])).
% 11.12/4.27  tff(c_14028, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_14027])).
% 11.12/4.27  tff(c_12967, plain, (![A_1414, B_1415, D_1416]: (r2_hidden('#skF_3'(A_1414, B_1415), k1_relat_1(A_1414)) | k1_funct_1(A_1414, D_1416)!='#skF_4'(A_1414, B_1415) | ~r2_hidden(D_1416, k1_relat_1(A_1414)) | k2_relat_1(A_1414)=B_1415 | ~v1_funct_1(A_1414) | ~v1_relat_1(A_1414))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_12973, plain, (![B_1415, D_71]: (r2_hidden('#skF_3'('#skF_8', B_1415), k1_relat_1('#skF_8')) | D_71!='#skF_4'('#skF_8', B_1415) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1415 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_12967])).
% 11.12/4.27  tff(c_12975, plain, (![B_1415, D_71]: (r2_hidden('#skF_3'('#skF_8', B_1415), '#skF_6') | D_71!='#skF_4'('#skF_8', B_1415) | ~r2_hidden('#skF_9'(D_71), '#skF_6') | k2_relat_1('#skF_8')=B_1415 | ~r2_hidden(D_71, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_12334, c_12334, c_12973])).
% 11.12/4.27  tff(c_13616, plain, (![B_1481]: (r2_hidden('#skF_3'('#skF_8', B_1481), '#skF_6') | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1481)), '#skF_6') | k2_relat_1('#skF_8')=B_1481 | ~r2_hidden('#skF_4'('#skF_8', B_1481), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_12975])).
% 11.12/4.27  tff(c_13628, plain, (![B_1481]: (r2_hidden('#skF_3'('#skF_8', B_1481), '#skF_6') | k2_relat_1('#skF_8')=B_1481 | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden('#skF_4'('#skF_8', B_1481), '#skF_7'))), inference(resolution, [status(thm)], [c_113, c_13616])).
% 11.12/4.27  tff(c_13639, plain, (![B_1482]: (r2_hidden('#skF_3'('#skF_8', B_1482), '#skF_6') | k2_relat_1('#skF_8')=B_1482 | ~r2_hidden('#skF_4'('#skF_8', B_1482), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_13628])).
% 11.12/4.27  tff(c_13642, plain, (![B_1482, B_2]: (r2_hidden('#skF_3'('#skF_8', B_1482), B_2) | ~r1_tarski('#skF_6', B_2) | k2_relat_1('#skF_8')=B_1482 | ~r2_hidden('#skF_4'('#skF_8', B_1482), '#skF_7'))), inference(resolution, [status(thm)], [c_13639, c_2])).
% 11.12/4.27  tff(c_14009, plain, (~r1_tarski('#skF_6', '#skF_6') | k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_13642, c_13978])).
% 11.12/4.27  tff(c_14033, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_14009])).
% 11.12/4.27  tff(c_14034, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_14033])).
% 11.12/4.27  tff(c_14063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14028, c_14034])).
% 11.12/4.27  tff(c_14064, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_13976])).
% 11.12/4.27  tff(c_14100, plain, (![B_1507]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_1507) | ~r1_tarski(k2_relat_1('#skF_8'), B_1507))), inference(resolution, [status(thm)], [c_14064, c_2])).
% 11.12/4.27  tff(c_14106, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_49, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_14100, c_24])).
% 11.12/4.27  tff(c_14119, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_49, '#skF_6') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_12907, c_88, c_64, c_12334, c_14106])).
% 11.12/4.27  tff(c_14214, plain, (![D_1513]: (k1_funct_1('#skF_8', D_1513)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1513, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_149, c_14119])).
% 11.12/4.27  tff(c_14375, plain, (![D_71]: (k1_funct_1('#skF_8', '#skF_9'(D_71))!='#skF_4'('#skF_8', '#skF_7') | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden(D_71, '#skF_7'))), inference(resolution, [status(thm)], [c_113, c_14214])).
% 11.12/4.27  tff(c_14514, plain, (![D_1518]: (k1_funct_1('#skF_8', '#skF_9'(D_1518))!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1518, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_14375])).
% 11.12/4.27  tff(c_14518, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_66, c_14514])).
% 11.12/4.27  tff(c_14110, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_14100, c_30])).
% 11.12/4.27  tff(c_14123, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_12907, c_88, c_64, c_14110])).
% 11.12/4.27  tff(c_14124, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_14123])).
% 11.12/4.27  tff(c_14520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14518, c_14124])).
% 11.12/4.27  tff(c_14521, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_12333])).
% 11.12/4.27  tff(c_11591, plain, (![D_96]: (r2_hidden('#skF_9'(D_96), '#skF_7') | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden(D_96, '#skF_7'))), inference(resolution, [status(thm)], [c_11589, c_123])).
% 11.12/4.27  tff(c_11609, plain, (![D_1284]: (r2_hidden('#skF_9'(D_1284), '#skF_7') | ~r2_hidden(D_1284, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_11591])).
% 11.12/4.27  tff(c_11633, plain, (![D_1289, B_1290]: (r2_hidden('#skF_9'(D_1289), B_1290) | ~r1_tarski('#skF_7', B_1290) | ~r2_hidden(D_1289, '#skF_7'))), inference(resolution, [status(thm)], [c_11609, c_2])).
% 11.12/4.27  tff(c_11727, plain, (![D_1303, B_1304, B_1305]: (r2_hidden('#skF_9'(D_1303), B_1304) | ~r1_tarski(B_1305, B_1304) | ~r1_tarski('#skF_7', B_1305) | ~r2_hidden(D_1303, '#skF_7'))), inference(resolution, [status(thm)], [c_11633, c_2])).
% 11.12/4.27  tff(c_11750, plain, (![D_1303, A_6]: (r2_hidden('#skF_9'(D_1303), A_6) | ~r1_tarski('#skF_7', k1_xboole_0) | ~r2_hidden(D_1303, '#skF_7'))), inference(resolution, [status(thm)], [c_8, c_11727])).
% 11.12/4.27  tff(c_11751, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_11750])).
% 11.12/4.27  tff(c_14530, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14521, c_11751])).
% 11.12/4.27  tff(c_14540, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_14530])).
% 11.12/4.27  tff(c_14542, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_11750])).
% 11.12/4.27  tff(c_14578, plain, (![A_1523, B_1524, B_1525, B_1526]: (r2_hidden('#skF_1'(A_1523, B_1524), B_1525) | ~r1_tarski(B_1526, B_1525) | ~r1_tarski(A_1523, B_1526) | r1_tarski(A_1523, B_1524))), inference(resolution, [status(thm)], [c_129, c_2])).
% 11.12/4.27  tff(c_14775, plain, (![A_1552, B_1553]: (r2_hidden('#skF_1'(A_1552, B_1553), k1_xboole_0) | ~r1_tarski(A_1552, '#skF_7') | r1_tarski(A_1552, B_1553))), inference(resolution, [status(thm)], [c_14542, c_14578])).
% 11.12/4.27  tff(c_14790, plain, (![A_1555]: (~r1_tarski(A_1555, '#skF_7') | r1_tarski(A_1555, k1_xboole_0))), inference(resolution, [status(thm)], [c_14775, c_4])).
% 11.12/4.27  tff(c_14800, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_14790, c_168])).
% 11.12/4.27  tff(c_14811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11589, c_14800])).
% 11.12/4.27  tff(c_14813, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_167])).
% 11.12/4.27  tff(c_14937, plain, (![A_1576, B_1577, B_1578, B_1579]: (r2_hidden('#skF_1'(A_1576, B_1577), B_1578) | ~r1_tarski(B_1579, B_1578) | ~r1_tarski(A_1576, B_1579) | r1_tarski(A_1576, B_1577))), inference(resolution, [status(thm)], [c_129, c_2])).
% 11.12/4.27  tff(c_14956, plain, (![A_1580, B_1581]: (r2_hidden('#skF_1'(A_1580, B_1581), k1_xboole_0) | ~r1_tarski(A_1580, '#skF_6') | r1_tarski(A_1580, B_1581))), inference(resolution, [status(thm)], [c_14813, c_14937])).
% 11.12/4.27  tff(c_14967, plain, (![A_1582]: (~r1_tarski(A_1582, '#skF_6') | r1_tarski(A_1582, k1_xboole_0))), inference(resolution, [status(thm)], [c_14956, c_4])).
% 11.12/4.27  tff(c_14980, plain, (![B_1583]: (v5_relat_1(B_1583, k1_xboole_0) | ~v1_relat_1(B_1583) | ~r1_tarski(k2_relat_1(B_1583), '#skF_6'))), inference(resolution, [status(thm)], [c_14967, c_12])).
% 11.12/4.27  tff(c_14986, plain, (![B_1584]: (v5_relat_1(B_1584, k1_xboole_0) | ~v5_relat_1(B_1584, '#skF_6') | ~v1_relat_1(B_1584))), inference(resolution, [status(thm)], [c_14, c_14980])).
% 11.12/4.27  tff(c_14812, plain, (![D_111, A_6]: (r2_hidden('#skF_9'(D_111), A_6) | ~r2_hidden(D_111, '#skF_7'))), inference(splitRight, [status(thm)], [c_167])).
% 11.12/4.27  tff(c_14823, plain, (![B_1558, A_1559]: (r2_hidden(k1_funct_1(B_1558, A_1559), k2_relat_1(B_1558)) | ~r2_hidden(A_1559, k1_relat_1(B_1558)) | ~v1_funct_1(B_1558) | ~v1_relat_1(B_1558))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.12/4.27  tff(c_14828, plain, (![D_71]: (r2_hidden(D_71, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_14823])).
% 11.12/4.27  tff(c_14833, plain, (![D_1562]: (r2_hidden(D_1562, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_1562), k1_relat_1('#skF_8')) | ~r2_hidden(D_1562, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_14828])).
% 11.12/4.27  tff(c_14839, plain, (![D_1563]: (r2_hidden(D_1563, k2_relat_1('#skF_8')) | ~r2_hidden(D_1563, '#skF_7'))), inference(resolution, [status(thm)], [c_14812, c_14833])).
% 11.12/4.27  tff(c_14848, plain, (![D_1564, B_1565]: (r2_hidden(D_1564, B_1565) | ~r1_tarski(k2_relat_1('#skF_8'), B_1565) | ~r2_hidden(D_1564, '#skF_7'))), inference(resolution, [status(thm)], [c_14839, c_2])).
% 11.12/4.27  tff(c_14851, plain, (![D_1564, A_10]: (r2_hidden(D_1564, A_10) | ~r2_hidden(D_1564, '#skF_7') | ~v5_relat_1('#skF_8', A_10) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_14, c_14848])).
% 11.12/4.27  tff(c_14859, plain, (![D_1566, A_1567]: (r2_hidden(D_1566, A_1567) | ~r2_hidden(D_1566, '#skF_7') | ~v5_relat_1('#skF_8', A_1567))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_14851])).
% 11.12/4.27  tff(c_14895, plain, (![B_1573, A_1574]: (r2_hidden('#skF_1'('#skF_7', B_1573), A_1574) | ~v5_relat_1('#skF_8', A_1574) | r1_tarski('#skF_7', B_1573))), inference(resolution, [status(thm)], [c_6, c_14859])).
% 11.12/4.27  tff(c_14916, plain, (![A_1574]: (~v5_relat_1('#skF_8', A_1574) | r1_tarski('#skF_7', A_1574))), inference(resolution, [status(thm)], [c_14895, c_4])).
% 11.12/4.27  tff(c_14990, plain, (r1_tarski('#skF_7', k1_xboole_0) | ~v5_relat_1('#skF_8', '#skF_6') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_14986, c_14916])).
% 11.12/4.27  tff(c_14993, plain, (r1_tarski('#skF_7', k1_xboole_0) | ~v5_relat_1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_14990])).
% 11.12/4.27  tff(c_14994, plain, (~v5_relat_1('#skF_8', '#skF_6')), inference(splitLeft, [status(thm)], [c_14993])).
% 11.12/4.27  tff(c_15646, plain, (![A_1667, B_1668, A_1669, B_1670]: (r2_hidden('#skF_1'(A_1667, B_1668), A_1669) | ~r1_tarski(A_1667, k2_relat_1(B_1670)) | r1_tarski(A_1667, B_1668) | ~v5_relat_1(B_1670, A_1669) | ~v1_relat_1(B_1670))), inference(resolution, [status(thm)], [c_14, c_14937])).
% 11.12/4.27  tff(c_15684, plain, (![B_1673, B_1674, A_1675]: (r2_hidden('#skF_1'(k2_relat_1(B_1673), B_1674), A_1675) | r1_tarski(k2_relat_1(B_1673), B_1674) | ~v5_relat_1(B_1673, A_1675) | ~v1_relat_1(B_1673))), inference(resolution, [status(thm)], [c_94, c_15646])).
% 11.12/4.27  tff(c_14847, plain, (![A_1]: (r1_tarski(A_1, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_14839, c_4])).
% 11.12/4.27  tff(c_15702, plain, (![B_1676]: (r1_tarski(k2_relat_1(B_1676), k2_relat_1('#skF_8')) | ~v5_relat_1(B_1676, '#skF_7') | ~v1_relat_1(B_1676))), inference(resolution, [status(thm)], [c_15684, c_14847])).
% 11.12/4.27  tff(c_14953, plain, (![A_1576, B_1577, A_10, B_11]: (r2_hidden('#skF_1'(A_1576, B_1577), A_10) | ~r1_tarski(A_1576, k2_relat_1(B_11)) | r1_tarski(A_1576, B_1577) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_14, c_14937])).
% 11.12/4.27  tff(c_15704, plain, (![B_1676, B_1577, A_10]: (r2_hidden('#skF_1'(k2_relat_1(B_1676), B_1577), A_10) | r1_tarski(k2_relat_1(B_1676), B_1577) | ~v5_relat_1('#skF_8', A_10) | ~v1_relat_1('#skF_8') | ~v5_relat_1(B_1676, '#skF_7') | ~v1_relat_1(B_1676))), inference(resolution, [status(thm)], [c_15702, c_14953])).
% 11.12/4.27  tff(c_16131, plain, (![B_1712, B_1713, A_1714]: (r2_hidden('#skF_1'(k2_relat_1(B_1712), B_1713), A_1714) | r1_tarski(k2_relat_1(B_1712), B_1713) | ~v5_relat_1('#skF_8', A_1714) | ~v5_relat_1(B_1712, '#skF_7') | ~v1_relat_1(B_1712))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_15704])).
% 11.12/4.27  tff(c_16156, plain, (![B_1712, A_1714]: (r1_tarski(k2_relat_1(B_1712), A_1714) | ~v5_relat_1('#skF_8', A_1714) | ~v5_relat_1(B_1712, '#skF_7') | ~v1_relat_1(B_1712))), inference(resolution, [status(thm)], [c_16131, c_4])).
% 11.12/4.27  tff(c_15003, plain, (![A_1587, B_1588, A_1589]: (r2_hidden('#skF_1'(A_1587, B_1588), A_1589) | ~r1_tarski(A_1587, k1_xboole_0) | r1_tarski(A_1587, B_1588))), inference(resolution, [status(thm)], [c_8, c_14937])).
% 11.12/4.27  tff(c_15034, plain, (![A_1591, A_1592]: (~r1_tarski(A_1591, k1_xboole_0) | r1_tarski(A_1591, A_1592))), inference(resolution, [status(thm)], [c_15003, c_4])).
% 11.12/4.27  tff(c_15049, plain, (![A_1592]: (r1_tarski('#skF_6', A_1592))), inference(resolution, [status(thm)], [c_14813, c_15034])).
% 11.12/4.27  tff(c_15515, plain, (![B_1646, A_1647, C_1648]: (k1_xboole_0=B_1646 | k1_relset_1(A_1647, B_1646, C_1648)=A_1647 | ~v1_funct_2(C_1648, A_1647, B_1646) | ~m1_subset_1(C_1648, k1_zfmisc_1(k2_zfmisc_1(A_1647, B_1646))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.12/4.27  tff(c_15518, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_15515])).
% 11.12/4.27  tff(c_15521, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_148, c_15518])).
% 11.12/4.27  tff(c_15530, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_15521])).
% 11.12/4.27  tff(c_16080, plain, (![A_1706, B_1707, D_1708]: (r2_hidden('#skF_3'(A_1706, B_1707), k1_relat_1(A_1706)) | k1_funct_1(A_1706, D_1708)!='#skF_4'(A_1706, B_1707) | ~r2_hidden(D_1708, k1_relat_1(A_1706)) | k2_relat_1(A_1706)=B_1707 | ~v1_funct_1(A_1706) | ~v1_relat_1(A_1706))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_16086, plain, (![B_1707, D_71]: (r2_hidden('#skF_3'('#skF_8', B_1707), k1_relat_1('#skF_8')) | D_71!='#skF_4'('#skF_8', B_1707) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1707 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_16080])).
% 11.12/4.27  tff(c_16088, plain, (![B_1707, D_71]: (r2_hidden('#skF_3'('#skF_8', B_1707), '#skF_6') | D_71!='#skF_4'('#skF_8', B_1707) | ~r2_hidden('#skF_9'(D_71), '#skF_6') | k2_relat_1('#skF_8')=B_1707 | ~r2_hidden(D_71, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_15530, c_15530, c_16086])).
% 11.12/4.27  tff(c_16492, plain, (![B_1741]: (r2_hidden('#skF_3'('#skF_8', B_1741), '#skF_6') | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1741)), '#skF_6') | k2_relat_1('#skF_8')=B_1741 | ~r2_hidden('#skF_4'('#skF_8', B_1741), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_16088])).
% 11.12/4.27  tff(c_16517, plain, (![B_1745]: (r2_hidden('#skF_3'('#skF_8', B_1745), '#skF_6') | k2_relat_1('#skF_8')=B_1745 | ~r2_hidden('#skF_4'('#skF_8', B_1745), '#skF_7'))), inference(resolution, [status(thm)], [c_14812, c_16492])).
% 11.12/4.27  tff(c_16519, plain, (![B_1745, B_2]: (r2_hidden('#skF_3'('#skF_8', B_1745), B_2) | ~r1_tarski('#skF_6', B_2) | k2_relat_1('#skF_8')=B_1745 | ~r2_hidden('#skF_4'('#skF_8', B_1745), '#skF_7'))), inference(resolution, [status(thm)], [c_16517, c_2])).
% 11.12/4.27  tff(c_16522, plain, (![B_1745, B_2]: (r2_hidden('#skF_3'('#skF_8', B_1745), B_2) | k2_relat_1('#skF_8')=B_1745 | ~r2_hidden('#skF_4'('#skF_8', B_1745), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_15049, c_16519])).
% 11.12/4.27  tff(c_16298, plain, (![A_1724, B_1725, D_1726]: (k1_funct_1(A_1724, '#skF_3'(A_1724, B_1725))='#skF_2'(A_1724, B_1725) | k1_funct_1(A_1724, D_1726)!='#skF_4'(A_1724, B_1725) | ~r2_hidden(D_1726, k1_relat_1(A_1724)) | k2_relat_1(A_1724)=B_1725 | ~v1_funct_1(A_1724) | ~v1_relat_1(A_1724))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_16304, plain, (![B_1725, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1725))='#skF_2'('#skF_8', B_1725) | D_71!='#skF_4'('#skF_8', B_1725) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1725 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_16298])).
% 11.12/4.27  tff(c_16306, plain, (![B_1725, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1725))='#skF_2'('#skF_8', B_1725) | D_71!='#skF_4'('#skF_8', B_1725) | ~r2_hidden('#skF_9'(D_71), '#skF_6') | k2_relat_1('#skF_8')=B_1725 | ~r2_hidden(D_71, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_15530, c_16304])).
% 11.12/4.27  tff(c_16566, plain, (![B_1751]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1751))='#skF_2'('#skF_8', B_1751) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1751)), '#skF_6') | k2_relat_1('#skF_8')=B_1751 | ~r2_hidden('#skF_4'('#skF_8', B_1751), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_16306])).
% 11.12/4.27  tff(c_16571, plain, (![B_1752]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1752))='#skF_2'('#skF_8', B_1752) | k2_relat_1('#skF_8')=B_1752 | ~r2_hidden('#skF_4'('#skF_8', B_1752), '#skF_7'))), inference(resolution, [status(thm)], [c_14812, c_16566])).
% 11.12/4.27  tff(c_16577, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_16571])).
% 11.12/4.27  tff(c_16586, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_16577])).
% 11.12/4.27  tff(c_16587, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_16586])).
% 11.12/4.27  tff(c_16599, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_16587, c_36])).
% 11.12/4.27  tff(c_16610, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_15530, c_16599])).
% 11.12/4.27  tff(c_16612, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_16610])).
% 11.12/4.27  tff(c_16615, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_16522, c_16612])).
% 11.12/4.27  tff(c_16627, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_16615])).
% 11.12/4.27  tff(c_15522, plain, (![A_1649, B_1650]: (r2_hidden('#skF_3'(A_1649, B_1650), k1_relat_1(A_1649)) | r2_hidden('#skF_4'(A_1649, B_1650), B_1650) | k2_relat_1(A_1649)=B_1650 | ~v1_funct_1(A_1649) | ~v1_relat_1(A_1649))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_15528, plain, (![A_1649, B_1650, B_2]: (r2_hidden('#skF_3'(A_1649, B_1650), B_2) | ~r1_tarski(k1_relat_1(A_1649), B_2) | r2_hidden('#skF_4'(A_1649, B_1650), B_1650) | k2_relat_1(A_1649)=B_1650 | ~v1_funct_1(A_1649) | ~v1_relat_1(A_1649))), inference(resolution, [status(thm)], [c_15522, c_2])).
% 11.12/4.27  tff(c_16618, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_15528, c_16612])).
% 11.12/4.27  tff(c_16630, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_94, c_15530, c_16618])).
% 11.12/4.27  tff(c_16631, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_16630])).
% 11.12/4.27  tff(c_16672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16627, c_16631])).
% 11.12/4.27  tff(c_16674, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_16610])).
% 11.12/4.27  tff(c_16676, plain, (![B_2]: (r2_hidden('#skF_3'('#skF_8', '#skF_7'), B_2) | ~r1_tarski('#skF_6', B_2))), inference(resolution, [status(thm)], [c_16674, c_2])).
% 11.12/4.27  tff(c_16679, plain, (![B_2]: (r2_hidden('#skF_3'('#skF_8', '#skF_7'), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_15049, c_16676])).
% 11.12/4.27  tff(c_14829, plain, (![B_1558, A_1559, B_2]: (r2_hidden(k1_funct_1(B_1558, A_1559), B_2) | ~r1_tarski(k2_relat_1(B_1558), B_2) | ~r2_hidden(A_1559, k1_relat_1(B_1558)) | ~v1_funct_1(B_1558) | ~v1_relat_1(B_1558))), inference(resolution, [status(thm)], [c_14823, c_2])).
% 11.12/4.27  tff(c_16595, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_16587, c_14829])).
% 11.12/4.27  tff(c_16608, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_15530, c_16595])).
% 11.12/4.27  tff(c_16697, plain, (![B_1757]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_1757) | ~r1_tarski(k2_relat_1('#skF_8'), B_1757))), inference(demodulation, [status(thm), theory('equality')], [c_16679, c_16608])).
% 11.12/4.27  tff(c_16707, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_16697, c_30])).
% 11.12/4.27  tff(c_16720, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_16707])).
% 11.12/4.27  tff(c_16721, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_16720])).
% 11.12/4.27  tff(c_16727, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_16721])).
% 11.12/4.27  tff(c_16730, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_16156, c_16727])).
% 11.12/4.27  tff(c_16743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_119, c_16730])).
% 11.12/4.27  tff(c_16745, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_16721])).
% 11.12/4.27  tff(c_16703, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_49, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_16697, c_24])).
% 11.12/4.27  tff(c_16716, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_49, '#skF_6') | k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_15530, c_16703])).
% 11.12/4.27  tff(c_16717, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_49, '#skF_6') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_149, c_16716])).
% 11.12/4.27  tff(c_16916, plain, (![D_1765]: (k1_funct_1('#skF_8', D_1765)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1765, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_16745, c_16717])).
% 11.12/4.27  tff(c_17064, plain, (![D_1767]: (k1_funct_1('#skF_8', '#skF_9'(D_1767))!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1767, '#skF_7'))), inference(resolution, [status(thm)], [c_14812, c_16916])).
% 11.12/4.27  tff(c_17068, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_66, c_17064])).
% 11.12/4.27  tff(c_16744, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_16721])).
% 11.12/4.27  tff(c_17070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17068, c_16744])).
% 11.12/4.27  tff(c_17071, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_15521])).
% 11.12/4.27  tff(c_15085, plain, (![B_1596, A_1597]: (r1_tarski(k2_relat_1(B_1596), A_1597) | ~v5_relat_1(B_1596, k1_xboole_0) | ~v1_relat_1(B_1596))), inference(resolution, [status(thm)], [c_14, c_15034])).
% 11.12/4.27  tff(c_14846, plain, (![D_1563, B_2]: (r2_hidden(D_1563, B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r2_hidden(D_1563, '#skF_7'))), inference(resolution, [status(thm)], [c_14839, c_2])).
% 11.12/4.27  tff(c_14978, plain, (![D_1563]: (r2_hidden(D_1563, k1_xboole_0) | ~r2_hidden(D_1563, '#skF_7') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_6'))), inference(resolution, [status(thm)], [c_14967, c_14846])).
% 11.12/4.27  tff(c_14996, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_14978])).
% 11.12/4.27  tff(c_15094, plain, (~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_15085, c_14996])).
% 11.12/4.27  tff(c_15111, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_88, c_15094])).
% 11.12/4.27  tff(c_17099, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_17071, c_15111])).
% 11.12/4.27  tff(c_17110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_17099])).
% 11.12/4.27  tff(c_17112, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_14978])).
% 11.12/4.27  tff(c_17122, plain, (v5_relat_1('#skF_8', '#skF_6') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_17112, c_12])).
% 11.12/4.27  tff(c_17130, plain, (v5_relat_1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_17122])).
% 11.12/4.27  tff(c_17132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14994, c_17130])).
% 11.12/4.27  tff(c_17134, plain, (v5_relat_1('#skF_8', '#skF_6')), inference(splitRight, [status(thm)], [c_14993])).
% 11.12/4.27  tff(c_17138, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_14978])).
% 11.12/4.27  tff(c_17148, plain, (~v5_relat_1('#skF_8', '#skF_6') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_14, c_17138])).
% 11.12/4.27  tff(c_17152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_17134, c_17148])).
% 11.12/4.27  tff(c_17154, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_14978])).
% 11.12/4.27  tff(c_14966, plain, (![A_1580]: (~r1_tarski(A_1580, '#skF_6') | r1_tarski(A_1580, k1_xboole_0))), inference(resolution, [status(thm)], [c_14956, c_4])).
% 11.12/4.27  tff(c_17388, plain, (![A_1793, B_1794, A_1795]: (r2_hidden('#skF_1'(A_1793, B_1794), A_1795) | ~r1_tarski(A_1793, k1_xboole_0) | r1_tarski(A_1793, B_1794))), inference(resolution, [status(thm)], [c_8, c_14937])).
% 11.12/4.27  tff(c_17411, plain, (![A_1796, A_1797]: (~r1_tarski(A_1796, k1_xboole_0) | r1_tarski(A_1796, A_1797))), inference(resolution, [status(thm)], [c_17388, c_4])).
% 11.12/4.27  tff(c_17456, plain, (![A_1799, A_1800]: (r1_tarski(A_1799, A_1800) | ~r1_tarski(A_1799, '#skF_6'))), inference(resolution, [status(thm)], [c_14966, c_17411])).
% 11.12/4.27  tff(c_17481, plain, (![A_1800]: (r1_tarski(k2_relat_1('#skF_8'), A_1800))), inference(resolution, [status(thm)], [c_17154, c_17456])).
% 11.12/4.27  tff(c_18580, plain, (![A_1935, B_1936, D_1937]: (k1_funct_1(A_1935, '#skF_3'(A_1935, B_1936))='#skF_2'(A_1935, B_1936) | k1_funct_1(A_1935, D_1937)!='#skF_4'(A_1935, B_1936) | ~r2_hidden(D_1937, k1_relat_1(A_1935)) | k2_relat_1(A_1935)=B_1936 | ~v1_funct_1(A_1935) | ~v1_relat_1(A_1935))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_18586, plain, (![B_1936, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1936))='#skF_2'('#skF_8', B_1936) | D_71!='#skF_4'('#skF_8', B_1936) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1936 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_18580])).
% 11.12/4.27  tff(c_18588, plain, (![B_1936, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1936))='#skF_2'('#skF_8', B_1936) | D_71!='#skF_4'('#skF_8', B_1936) | ~r2_hidden('#skF_9'(D_71), '#skF_6') | k2_relat_1('#skF_8')=B_1936 | ~r2_hidden(D_71, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_17806, c_18586])).
% 11.12/4.27  tff(c_18787, plain, (![B_1970]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1970))='#skF_2'('#skF_8', B_1970) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1970)), '#skF_6') | k2_relat_1('#skF_8')=B_1970 | ~r2_hidden('#skF_4'('#skF_8', B_1970), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_18588])).
% 11.12/4.27  tff(c_18914, plain, (![B_1973]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_1973))='#skF_2'('#skF_8', B_1973) | k2_relat_1('#skF_8')=B_1973 | ~r2_hidden('#skF_4'('#skF_8', B_1973), '#skF_7'))), inference(resolution, [status(thm)], [c_14812, c_18787])).
% 11.12/4.27  tff(c_18930, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_18914])).
% 11.12/4.27  tff(c_18937, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_18930])).
% 11.12/4.27  tff(c_18938, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_18937])).
% 11.12/4.27  tff(c_17434, plain, (![A_1797]: (r1_tarski('#skF_6', A_1797))), inference(resolution, [status(thm)], [c_14813, c_17411])).
% 11.12/4.27  tff(c_18236, plain, (![B_1883, A_1884, B_1885]: (r2_hidden(k1_funct_1(B_1883, A_1884), B_1885) | ~r1_tarski(k2_relat_1(B_1883), B_1885) | ~r2_hidden(A_1884, k1_relat_1(B_1883)) | ~v1_funct_1(B_1883) | ~v1_relat_1(B_1883))), inference(resolution, [status(thm)], [c_14823, c_2])).
% 11.12/4.27  tff(c_18644, plain, (![B_1950, A_1951, B_1952, B_1953]: (r2_hidden(k1_funct_1(B_1950, A_1951), B_1952) | ~r1_tarski(B_1953, B_1952) | ~r1_tarski(k2_relat_1(B_1950), B_1953) | ~r2_hidden(A_1951, k1_relat_1(B_1950)) | ~v1_funct_1(B_1950) | ~v1_relat_1(B_1950))), inference(resolution, [status(thm)], [c_18236, c_2])).
% 11.12/4.27  tff(c_18667, plain, (![B_1950, A_1951, A_1797]: (r2_hidden(k1_funct_1(B_1950, A_1951), A_1797) | ~r1_tarski(k2_relat_1(B_1950), '#skF_6') | ~r2_hidden(A_1951, k1_relat_1(B_1950)) | ~v1_funct_1(B_1950) | ~v1_relat_1(B_1950))), inference(resolution, [status(thm)], [c_17434, c_18644])).
% 11.12/4.27  tff(c_18945, plain, (![A_1797]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), A_1797) | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_6') | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_18938, c_18667])).
% 11.12/4.27  tff(c_18967, plain, (![A_1797]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), A_1797) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_17806, c_17481, c_18945])).
% 11.12/4.27  tff(c_18997, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_18967])).
% 11.12/4.27  tff(c_19000, plain, (~r1_tarski(k1_relat_1('#skF_8'), '#skF_6') | r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_17972, c_18997])).
% 11.12/4.27  tff(c_19024, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_94, c_17806, c_19000])).
% 11.12/4.27  tff(c_19025, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_19024])).
% 11.12/4.27  tff(c_18444, plain, (![A_1909, B_1910, D_1911]: (r2_hidden('#skF_3'(A_1909, B_1910), k1_relat_1(A_1909)) | k1_funct_1(A_1909, D_1911)!='#skF_4'(A_1909, B_1910) | ~r2_hidden(D_1911, k1_relat_1(A_1909)) | k2_relat_1(A_1909)=B_1910 | ~v1_funct_1(A_1909) | ~v1_relat_1(A_1909))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_18450, plain, (![B_1910, D_71]: (r2_hidden('#skF_3'('#skF_8', B_1910), k1_relat_1('#skF_8')) | D_71!='#skF_4'('#skF_8', B_1910) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_1910 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_18444])).
% 11.12/4.27  tff(c_18452, plain, (![B_1910, D_71]: (r2_hidden('#skF_3'('#skF_8', B_1910), '#skF_6') | D_71!='#skF_4'('#skF_8', B_1910) | ~r2_hidden('#skF_9'(D_71), '#skF_6') | k2_relat_1('#skF_8')=B_1910 | ~r2_hidden(D_71, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_17806, c_17806, c_18450])).
% 11.12/4.27  tff(c_18575, plain, (![B_1934]: (r2_hidden('#skF_3'('#skF_8', B_1934), '#skF_6') | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_1934)), '#skF_6') | k2_relat_1('#skF_8')=B_1934 | ~r2_hidden('#skF_4'('#skF_8', B_1934), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_18452])).
% 11.12/4.27  tff(c_18589, plain, (![B_1938]: (r2_hidden('#skF_3'('#skF_8', B_1938), '#skF_6') | k2_relat_1('#skF_8')=B_1938 | ~r2_hidden('#skF_4'('#skF_8', B_1938), '#skF_7'))), inference(resolution, [status(thm)], [c_14812, c_18575])).
% 11.12/4.27  tff(c_18591, plain, (![B_1938, B_2]: (r2_hidden('#skF_3'('#skF_8', B_1938), B_2) | ~r1_tarski('#skF_6', B_2) | k2_relat_1('#skF_8')=B_1938 | ~r2_hidden('#skF_4'('#skF_8', B_1938), '#skF_7'))), inference(resolution, [status(thm)], [c_18589, c_2])).
% 11.12/4.27  tff(c_18594, plain, (![B_1938, B_2]: (r2_hidden('#skF_3'('#skF_8', B_1938), B_2) | k2_relat_1('#skF_8')=B_1938 | ~r2_hidden('#skF_4'('#skF_8', B_1938), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_17434, c_18591])).
% 11.12/4.27  tff(c_19003, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_18594, c_18997])).
% 11.12/4.27  tff(c_19028, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_19003])).
% 11.12/4.27  tff(c_19067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19025, c_19028])).
% 11.12/4.27  tff(c_19070, plain, (![A_1977]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), A_1977))), inference(splitRight, [status(thm)], [c_18967])).
% 11.12/4.27  tff(c_19080, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_19070, c_30])).
% 11.12/4.27  tff(c_19094, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_19080])).
% 11.12/4.27  tff(c_19095, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_149, c_19094])).
% 11.12/4.27  tff(c_17186, plain, (![D_1772]: (r2_hidden(D_1772, k1_xboole_0) | ~r2_hidden(D_1772, '#skF_7'))), inference(splitRight, [status(thm)], [c_14978])).
% 11.12/4.27  tff(c_17188, plain, (![D_1772, B_2]: (r2_hidden(D_1772, B_2) | ~r1_tarski(k1_xboole_0, B_2) | ~r2_hidden(D_1772, '#skF_7'))), inference(resolution, [status(thm)], [c_17186, c_2])).
% 11.12/4.27  tff(c_17195, plain, (![D_1772, B_2]: (r2_hidden(D_1772, B_2) | ~r2_hidden(D_1772, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_17188])).
% 11.12/4.27  tff(c_19115, plain, (![B_2]: (r2_hidden('#skF_4'('#skF_8', '#skF_7'), B_2))), inference(resolution, [status(thm)], [c_19095, c_17195])).
% 11.12/4.27  tff(c_19076, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_49, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_19070, c_24])).
% 11.12/4.27  tff(c_19090, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_49, '#skF_6') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_17806, c_19076])).
% 11.12/4.27  tff(c_19217, plain, (![D_1983]: (k1_funct_1('#skF_8', D_1983)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1983, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_149, c_19090])).
% 11.12/4.27  tff(c_19369, plain, (![D_1984]: (k1_funct_1('#skF_8', '#skF_9'(D_1984))!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1984, '#skF_7'))), inference(resolution, [status(thm)], [c_14812, c_19217])).
% 11.12/4.27  tff(c_19442, plain, (![D_1987]: (D_1987!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_1987, '#skF_7') | ~r2_hidden(D_1987, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_19369])).
% 11.12/4.27  tff(c_19448, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_19115, c_19442])).
% 11.12/4.27  tff(c_19531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19115, c_19448])).
% 11.12/4.27  tff(c_19533, plain, (k1_relat_1('#skF_8')!='#skF_6'), inference(splitRight, [status(thm)], [c_17805])).
% 11.12/4.27  tff(c_19532, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_17805])).
% 11.12/4.27  tff(c_19634, plain, (![C_1996, A_1997]: (C_1996='#skF_7' | ~v1_funct_2(C_1996, A_1997, '#skF_7') | A_1997='#skF_7' | ~m1_subset_1(C_1996, k1_zfmisc_1(k2_zfmisc_1(A_1997, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_19532, c_19532, c_19532, c_19532, c_48])).
% 11.12/4.27  tff(c_19637, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_60, c_19634])).
% 11.12/4.27  tff(c_19640, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_19637])).
% 11.12/4.27  tff(c_19641, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_19640])).
% 11.12/4.27  tff(c_19659, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19641, c_62])).
% 11.12/4.27  tff(c_19654, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_19641, c_148])).
% 11.12/4.27  tff(c_19658, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_19641, c_60])).
% 11.12/4.27  tff(c_54, plain, (![B_66, C_67]: (k1_relset_1(k1_xboole_0, B_66, C_67)=k1_xboole_0 | ~v1_funct_2(C_67, k1_xboole_0, B_66) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_66))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 11.12/4.27  tff(c_19541, plain, (![B_66, C_67]: (k1_relset_1('#skF_7', B_66, C_67)='#skF_7' | ~v1_funct_2(C_67, '#skF_7', B_66) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_66))))), inference(demodulation, [status(thm), theory('equality')], [c_19532, c_19532, c_19532, c_19532, c_54])).
% 11.12/4.27  tff(c_19825, plain, (![B_2021, C_2022]: (k1_relset_1('#skF_6', B_2021, C_2022)='#skF_6' | ~v1_funct_2(C_2022, '#skF_6', B_2021) | ~m1_subset_1(C_2022, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_2021))))), inference(demodulation, [status(thm), theory('equality')], [c_19641, c_19641, c_19641, c_19641, c_19541])).
% 11.12/4.27  tff(c_19828, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_19658, c_19825])).
% 11.12/4.27  tff(c_19831, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_19659, c_19654, c_19828])).
% 11.12/4.27  tff(c_19833, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19533, c_19831])).
% 11.12/4.27  tff(c_19834, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_19640])).
% 11.12/4.27  tff(c_19849, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_19834, c_149])).
% 11.12/4.27  tff(c_19847, plain, (![D_111, A_6]: (r2_hidden('#skF_9'(D_111), A_6) | ~r2_hidden(D_111, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_19834, c_14812])).
% 11.12/4.27  tff(c_19851, plain, (![D_71]: (k1_funct_1('#skF_8', '#skF_9'(D_71))=D_71 | ~r2_hidden(D_71, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_19834, c_66])).
% 11.12/4.27  tff(c_20075, plain, (![A_2046, B_2047, D_2048]: (r2_hidden('#skF_3'(A_2046, B_2047), k1_relat_1(A_2046)) | k1_funct_1(A_2046, D_2048)!='#skF_4'(A_2046, B_2047) | ~r2_hidden(D_2048, k1_relat_1(A_2046)) | k2_relat_1(A_2046)=B_2047 | ~v1_funct_1(A_2046) | ~v1_relat_1(A_2046))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_20077, plain, (![B_2047, D_71]: (r2_hidden('#skF_3'('#skF_8', B_2047), k1_relat_1('#skF_8')) | D_71!='#skF_4'('#skF_8', B_2047) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_2047 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_19851, c_20075])).
% 11.12/4.27  tff(c_20083, plain, (![B_2047, D_71]: (r2_hidden('#skF_3'('#skF_8', B_2047), k1_relat_1('#skF_8')) | D_71!='#skF_4'('#skF_8', B_2047) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_2047 | ~r2_hidden(D_71, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_20077])).
% 11.12/4.27  tff(c_20346, plain, (![B_2096]: (r2_hidden('#skF_3'('#skF_8', B_2096), k1_relat_1('#skF_8')) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_2096)), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_2096 | ~r2_hidden('#skF_4'('#skF_8', B_2096), '#skF_8'))), inference(reflexivity, [status(thm), theory('equality')], [c_20083])).
% 11.12/4.27  tff(c_20351, plain, (![B_2097]: (r2_hidden('#skF_3'('#skF_8', B_2097), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_2097 | ~r2_hidden('#skF_4'('#skF_8', B_2097), '#skF_8'))), inference(resolution, [status(thm)], [c_19847, c_20346])).
% 11.12/4.27  tff(c_20354, plain, (![B_2097, B_2]: (r2_hidden('#skF_3'('#skF_8', B_2097), B_2) | ~r1_tarski(k1_relat_1('#skF_8'), B_2) | k2_relat_1('#skF_8')=B_2097 | ~r2_hidden('#skF_4'('#skF_8', B_2097), '#skF_8'))), inference(resolution, [status(thm)], [c_20351, c_2])).
% 11.12/4.27  tff(c_20152, plain, (![A_2061, B_2062, D_2063]: (k1_funct_1(A_2061, '#skF_3'(A_2061, B_2062))='#skF_2'(A_2061, B_2062) | k1_funct_1(A_2061, D_2063)!='#skF_4'(A_2061, B_2062) | ~r2_hidden(D_2063, k1_relat_1(A_2061)) | k2_relat_1(A_2061)=B_2062 | ~v1_funct_1(A_2061) | ~v1_relat_1(A_2061))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_20154, plain, (![B_2062, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_2062))='#skF_2'('#skF_8', B_2062) | D_71!='#skF_4'('#skF_8', B_2062) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_2062 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_19851, c_20152])).
% 11.12/4.27  tff(c_20160, plain, (![B_2062, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_2062))='#skF_2'('#skF_8', B_2062) | D_71!='#skF_4'('#skF_8', B_2062) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_2062 | ~r2_hidden(D_71, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_20154])).
% 11.12/4.27  tff(c_20430, plain, (![B_2116]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_2116))='#skF_2'('#skF_8', B_2116) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_2116)), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_2116 | ~r2_hidden('#skF_4'('#skF_8', B_2116), '#skF_8'))), inference(reflexivity, [status(thm), theory('equality')], [c_20160])).
% 11.12/4.27  tff(c_20435, plain, (![B_2117]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_2117))='#skF_2'('#skF_8', B_2117) | k2_relat_1('#skF_8')=B_2117 | ~r2_hidden('#skF_4'('#skF_8', B_2117), '#skF_8'))), inference(resolution, [status(thm)], [c_19847, c_20430])).
% 11.12/4.27  tff(c_20441, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_20435])).
% 11.12/4.27  tff(c_20446, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8') | k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_20441])).
% 11.12/4.27  tff(c_20447, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_8'))='#skF_2'('#skF_8', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_19849, c_20446])).
% 11.12/4.27  tff(c_20454, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), B_2) | ~r1_tarski(k2_relat_1('#skF_8'), B_2) | ~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_20447, c_14829])).
% 11.12/4.27  tff(c_20469, plain, (![B_2]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), B_2) | ~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_17481, c_20454])).
% 11.12/4.27  tff(c_20477, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_8'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_20469])).
% 11.12/4.27  tff(c_20483, plain, (~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_8' | ~r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_20354, c_20477])).
% 11.12/4.27  tff(c_20496, plain, (k2_relat_1('#skF_8')='#skF_8' | ~r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_20483])).
% 11.12/4.27  tff(c_20497, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_19849, c_20496])).
% 11.12/4.27  tff(c_19626, plain, (![A_1994, B_1995]: (r2_hidden('#skF_3'(A_1994, B_1995), k1_relat_1(A_1994)) | r2_hidden('#skF_4'(A_1994, B_1995), B_1995) | k2_relat_1(A_1994)=B_1995 | ~v1_funct_1(A_1994) | ~v1_relat_1(A_1994))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.12/4.27  tff(c_20514, plain, (![A_2118, B_2119, B_2120]: (r2_hidden('#skF_3'(A_2118, B_2119), B_2120) | ~r1_tarski(k1_relat_1(A_2118), B_2120) | r2_hidden('#skF_4'(A_2118, B_2119), B_2119) | k2_relat_1(A_2118)=B_2119 | ~v1_funct_1(A_2118) | ~v1_relat_1(A_2118))), inference(resolution, [status(thm)], [c_19626, c_2])).
% 11.12/4.27  tff(c_20517, plain, (~r1_tarski(k1_relat_1('#skF_8'), k1_relat_1('#skF_8')) | r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_20514, c_20477])).
% 11.12/4.27  tff(c_20531, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_94, c_20517])).
% 11.12/4.27  tff(c_20533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19849, c_20497, c_20531])).
% 11.12/4.27  tff(c_20536, plain, (![B_2121]: (r2_hidden('#skF_2'('#skF_8', '#skF_8'), B_2121))), inference(splitRight, [status(thm)], [c_20469])).
% 11.12/4.27  tff(c_20546, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_20536, c_30])).
% 11.12/4.27  tff(c_20557, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8') | k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_20546])).
% 11.12/4.27  tff(c_20558, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_19849, c_20557])).
% 11.12/4.27  tff(c_19844, plain, (![D_1772, B_2]: (r2_hidden(D_1772, B_2) | ~r2_hidden(D_1772, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_19834, c_17195])).
% 11.12/4.27  tff(c_20571, plain, (![B_2]: (r2_hidden('#skF_4'('#skF_8', '#skF_8'), B_2))), inference(resolution, [status(thm)], [c_20558, c_19844])).
% 11.12/4.27  tff(c_20539, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_49, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_20536, c_24])).
% 11.12/4.27  tff(c_20551, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_49, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_20539])).
% 11.12/4.27  tff(c_20593, plain, (![D_2123]: (k1_funct_1('#skF_8', D_2123)!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_2123, k1_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_19849, c_20551])).
% 11.12/4.27  tff(c_20733, plain, (![D_2128]: (k1_funct_1('#skF_8', '#skF_9'(D_2128))!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_2128, '#skF_8'))), inference(resolution, [status(thm)], [c_19847, c_20593])).
% 11.12/4.27  tff(c_20738, plain, (![D_2129]: (D_2129!='#skF_4'('#skF_8', '#skF_8') | ~r2_hidden(D_2129, '#skF_8') | ~r2_hidden(D_2129, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_19851, c_20733])).
% 11.12/4.27  tff(c_20748, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_8'), '#skF_8')), inference(resolution, [status(thm)], [c_20571, c_20738])).
% 11.12/4.27  tff(c_20789, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20571, c_20748])).
% 11.12/4.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.12/4.27  
% 11.12/4.27  Inference rules
% 11.12/4.27  ----------------------
% 11.12/4.27  #Ref     : 21
% 11.12/4.27  #Sup     : 4421
% 11.12/4.27  #Fact    : 4
% 11.12/4.27  #Define  : 0
% 11.12/4.27  #Split   : 78
% 11.12/4.27  #Chain   : 0
% 11.12/4.27  #Close   : 0
% 11.12/4.27  
% 11.12/4.27  Ordering : KBO
% 11.12/4.27  
% 11.12/4.27  Simplification rules
% 11.12/4.27  ----------------------
% 11.12/4.27  #Subsume      : 1839
% 11.12/4.27  #Demod        : 2410
% 11.12/4.27  #Tautology    : 748
% 11.12/4.27  #SimpNegUnit  : 118
% 11.12/4.27  #BackRed      : 288
% 11.12/4.27  
% 11.12/4.27  #Partial instantiations: 0
% 11.12/4.27  #Strategies tried      : 1
% 11.12/4.27  
% 11.12/4.27  Timing (in seconds)
% 11.12/4.27  ----------------------
% 11.12/4.28  Preprocessing        : 0.34
% 11.12/4.28  Parsing              : 0.17
% 11.12/4.28  CNF conversion       : 0.03
% 11.12/4.28  Main loop            : 2.98
% 11.12/4.28  Inferencing          : 0.99
% 11.12/4.28  Reduction            : 0.79
% 11.12/4.28  Demodulation         : 0.52
% 11.12/4.28  BG Simplification    : 0.08
% 11.12/4.28  Subsumption          : 0.91
% 11.12/4.28  Abstraction          : 0.12
% 11.12/4.28  MUC search           : 0.00
% 11.12/4.28  Cooper               : 0.00
% 11.12/4.28  Total                : 3.54
% 11.12/4.28  Index Insertion      : 0.00
% 11.12/4.28  Index Deletion       : 0.00
% 11.12/4.28  Index Matching       : 0.00
% 11.12/4.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
