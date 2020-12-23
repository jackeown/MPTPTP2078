%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:48 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  106 (1192 expanded)
%              Number of leaves         :   24 ( 414 expanded)
%              Depth                    :   12
%              Number of atoms          :  204 (3389 expanded)
%              Number of equality atoms :   65 ( 846 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_79,axiom,(
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

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1618,plain,(
    ! [C_233,A_234,B_235] :
      ( m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ r1_tarski(k2_relat_1(C_233),B_235)
      | ~ r1_tarski(k1_relat_1(C_233),A_234)
      | ~ v1_relat_1(C_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_77,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_85,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_77])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_257,plain,(
    ! [C_67,A_68,B_69] :
      ( m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ r1_tarski(k2_relat_1(C_67),B_69)
      | ~ r1_tarski(k1_relat_1(C_67),A_68)
      | ~ v1_relat_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1009,plain,(
    ! [C_156,A_157,B_158] :
      ( r1_tarski(C_156,k2_zfmisc_1(A_157,B_158))
      | ~ r1_tarski(k2_relat_1(C_156),B_158)
      | ~ r1_tarski(k1_relat_1(C_156),A_157)
      | ~ v1_relat_1(C_156) ) ),
    inference(resolution,[status(thm)],[c_257,c_16])).

tff(c_1014,plain,(
    ! [C_159,A_160] :
      ( r1_tarski(C_159,k2_zfmisc_1(A_160,k2_relat_1(C_159)))
      | ~ r1_tarski(k1_relat_1(C_159),A_160)
      | ~ v1_relat_1(C_159) ) ),
    inference(resolution,[status(thm)],[c_6,c_1009])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_138,plain,(
    ! [A_45,B_46,C_47] :
      ( k1_relset_1(A_45,B_46,C_47) = k1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_153,plain,(
    ! [A_45,B_46,A_6] :
      ( k1_relset_1(A_45,B_46,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_45,B_46)) ) ),
    inference(resolution,[status(thm)],[c_18,c_138])).

tff(c_1036,plain,(
    ! [A_162,C_163] :
      ( k1_relset_1(A_162,k2_relat_1(C_163),C_163) = k1_relat_1(C_163)
      | ~ r1_tarski(k1_relat_1(C_163),A_162)
      | ~ v1_relat_1(C_163) ) ),
    inference(resolution,[status(thm)],[c_1014,c_153])).

tff(c_1048,plain,(
    ! [C_163] :
      ( k1_relset_1(k1_relat_1(C_163),k2_relat_1(C_163),C_163) = k1_relat_1(C_163)
      | ~ v1_relat_1(C_163) ) ),
    inference(resolution,[status(thm)],[c_6,c_1036])).

tff(c_1013,plain,(
    ! [C_156,A_157] :
      ( r1_tarski(C_156,k2_zfmisc_1(A_157,k2_relat_1(C_156)))
      | ~ r1_tarski(k1_relat_1(C_156),A_157)
      | ~ v1_relat_1(C_156) ) ),
    inference(resolution,[status(thm)],[c_6,c_1009])).

tff(c_956,plain,(
    ! [B_148,C_149,A_150] :
      ( k1_xboole_0 = B_148
      | v1_funct_2(C_149,A_150,B_148)
      | k1_relset_1(A_150,B_148,C_149) != A_150
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_150,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1072,plain,(
    ! [B_165,A_166,A_167] :
      ( k1_xboole_0 = B_165
      | v1_funct_2(A_166,A_167,B_165)
      | k1_relset_1(A_167,B_165,A_166) != A_167
      | ~ r1_tarski(A_166,k2_zfmisc_1(A_167,B_165)) ) ),
    inference(resolution,[status(thm)],[c_18,c_956])).

tff(c_1221,plain,(
    ! [C_187,A_188] :
      ( k2_relat_1(C_187) = k1_xboole_0
      | v1_funct_2(C_187,A_188,k2_relat_1(C_187))
      | k1_relset_1(A_188,k2_relat_1(C_187),C_187) != A_188
      | ~ r1_tarski(k1_relat_1(C_187),A_188)
      | ~ v1_relat_1(C_187) ) ),
    inference(resolution,[status(thm)],[c_1013,c_1072])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38])).

tff(c_86,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_1235,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1221,c_86])).

tff(c_1243,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6,c_1235])).

tff(c_1244,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1243])).

tff(c_1276,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1048,c_1244])).

tff(c_1280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1276])).

tff(c_1281,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1243])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1029,plain,(
    ! [A_160,C_159] :
      ( k2_zfmisc_1(A_160,k2_relat_1(C_159)) = C_159
      | ~ r1_tarski(k2_zfmisc_1(A_160,k2_relat_1(C_159)),C_159)
      | ~ r1_tarski(k1_relat_1(C_159),A_160)
      | ~ v1_relat_1(C_159) ) ),
    inference(resolution,[status(thm)],[c_1014,c_2])).

tff(c_1290,plain,(
    ! [A_160] :
      ( k2_zfmisc_1(A_160,k2_relat_1('#skF_1')) = '#skF_1'
      | ~ r1_tarski(k2_zfmisc_1(A_160,k1_xboole_0),'#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_160)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1281,c_1029])).

tff(c_1308,plain,(
    ! [A_160] :
      ( k1_xboole_0 = '#skF_1'
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_85,c_10,c_10,c_1281,c_1290])).

tff(c_1326,plain,(
    ! [A_192] : ~ r1_tarski(k1_relat_1('#skF_1'),A_192) ),
    inference(splitLeft,[status(thm)],[c_1308])).

tff(c_1336,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_1326])).

tff(c_1337,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1308])).

tff(c_328,plain,(
    ! [C_82,A_83,B_84] :
      ( r1_tarski(C_82,k2_zfmisc_1(A_83,B_84))
      | ~ r1_tarski(k2_relat_1(C_82),B_84)
      | ~ r1_tarski(k1_relat_1(C_82),A_83)
      | ~ v1_relat_1(C_82) ) ),
    inference(resolution,[status(thm)],[c_257,c_16])).

tff(c_376,plain,(
    ! [C_90,A_91] :
      ( r1_tarski(C_90,k2_zfmisc_1(A_91,k2_relat_1(C_90)))
      | ~ r1_tarski(k1_relat_1(C_90),A_91)
      | ~ v1_relat_1(C_90) ) ),
    inference(resolution,[status(thm)],[c_6,c_328])).

tff(c_393,plain,(
    ! [A_93,C_94] :
      ( k1_relset_1(A_93,k2_relat_1(C_94),C_94) = k1_relat_1(C_94)
      | ~ r1_tarski(k1_relat_1(C_94),A_93)
      | ~ v1_relat_1(C_94) ) ),
    inference(resolution,[status(thm)],[c_376,c_153])).

tff(c_401,plain,(
    ! [C_94] :
      ( k1_relset_1(k1_relat_1(C_94),k2_relat_1(C_94),C_94) = k1_relat_1(C_94)
      | ~ v1_relat_1(C_94) ) ),
    inference(resolution,[status(thm)],[c_6,c_393])).

tff(c_24,plain,(
    ! [C_16,A_14,B_15] :
      ( m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ r1_tarski(k2_relat_1(C_16),B_15)
      | ~ r1_tarski(k1_relat_1(C_16),A_14)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_333,plain,(
    ! [B_85,C_86,A_87] :
      ( k1_xboole_0 = B_85
      | v1_funct_2(C_86,A_87,B_85)
      | k1_relset_1(A_87,B_85,C_86) != A_87
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_581,plain,(
    ! [B_119,C_120,A_121] :
      ( k1_xboole_0 = B_119
      | v1_funct_2(C_120,A_121,B_119)
      | k1_relset_1(A_121,B_119,C_120) != A_121
      | ~ r1_tarski(k2_relat_1(C_120),B_119)
      | ~ r1_tarski(k1_relat_1(C_120),A_121)
      | ~ v1_relat_1(C_120) ) ),
    inference(resolution,[status(thm)],[c_24,c_333])).

tff(c_590,plain,(
    ! [C_122,A_123] :
      ( k2_relat_1(C_122) = k1_xboole_0
      | v1_funct_2(C_122,A_123,k2_relat_1(C_122))
      | k1_relset_1(A_123,k2_relat_1(C_122),C_122) != A_123
      | ~ r1_tarski(k1_relat_1(C_122),A_123)
      | ~ v1_relat_1(C_122) ) ),
    inference(resolution,[status(thm)],[c_6,c_581])).

tff(c_608,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_590,c_86])).

tff(c_617,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6,c_608])).

tff(c_618,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_617])).

tff(c_621,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_618])).

tff(c_625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_621])).

tff(c_626,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_391,plain,(
    ! [A_91,C_90] :
      ( k2_zfmisc_1(A_91,k2_relat_1(C_90)) = C_90
      | ~ r1_tarski(k2_zfmisc_1(A_91,k2_relat_1(C_90)),C_90)
      | ~ r1_tarski(k1_relat_1(C_90),A_91)
      | ~ v1_relat_1(C_90) ) ),
    inference(resolution,[status(thm)],[c_376,c_2])).

tff(c_637,plain,(
    ! [A_91] :
      ( k2_zfmisc_1(A_91,k2_relat_1('#skF_1')) = '#skF_1'
      | ~ r1_tarski(k2_zfmisc_1(A_91,k1_xboole_0),'#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_91)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_391])).

tff(c_657,plain,(
    ! [A_91] :
      ( k1_xboole_0 = '#skF_1'
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_85,c_10,c_10,c_626,c_637])).

tff(c_670,plain,(
    ! [A_124] : ~ r1_tarski(k1_relat_1('#skF_1'),A_124) ),
    inference(splitLeft,[status(thm)],[c_657])).

tff(c_680,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_670])).

tff(c_681,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_154,plain,(
    ! [A_45,B_46] : k1_relset_1(A_45,B_46,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_138])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_247,plain,(
    ! [C_65,B_66] :
      ( v1_funct_2(C_65,k1_xboole_0,B_66)
      | k1_relset_1(k1_xboole_0,B_66,C_65) != k1_xboole_0
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_30])).

tff(c_253,plain,(
    ! [B_66] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_66)
      | k1_relset_1(k1_xboole_0,B_66,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_247])).

tff(c_256,plain,(
    ! [B_66] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_66)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_253])).

tff(c_275,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_701,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_681,c_275])).

tff(c_26,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_17,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_26])).

tff(c_867,plain,(
    ! [A_135] :
      ( v1_funct_2('#skF_1',A_135,'#skF_1')
      | A_135 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_681,c_681,c_46])).

tff(c_628,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_86])).

tff(c_682,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_628])).

tff(c_870,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_867,c_682])).

tff(c_876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_701,c_870])).

tff(c_877,plain,(
    ! [B_66] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_66) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_1357,plain,(
    ! [B_66] : v1_funct_2('#skF_1','#skF_1',B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_1337,c_877])).

tff(c_878,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_1358,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_1337,c_878])).

tff(c_1283,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1281,c_86])).

tff(c_1339,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_1283])).

tff(c_1459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_1358,c_1339])).

tff(c_1460,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1626,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1618,c_1460])).

tff(c_1641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6,c_6,c_1626])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:10:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.59  
% 3.54/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.59  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.54/1.59  
% 3.54/1.59  %Foreground sorts:
% 3.54/1.59  
% 3.54/1.59  
% 3.54/1.59  %Background operators:
% 3.54/1.59  
% 3.54/1.59  
% 3.54/1.59  %Foreground operators:
% 3.54/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.54/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.54/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.54/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.54/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.54/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.54/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.54/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.54/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.59  
% 3.54/1.61  tff(f_90, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 3.54/1.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.54/1.61  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.54/1.61  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.54/1.61  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.54/1.61  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.54/1.61  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.54/1.61  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.54/1.61  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.54/1.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.61  tff(c_1618, plain, (![C_233, A_234, B_235]: (m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~r1_tarski(k2_relat_1(C_233), B_235) | ~r1_tarski(k1_relat_1(C_233), A_234) | ~v1_relat_1(C_233))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.61  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.54/1.61  tff(c_77, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.54/1.61  tff(c_85, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_77])).
% 3.54/1.61  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.54/1.61  tff(c_257, plain, (![C_67, A_68, B_69]: (m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~r1_tarski(k2_relat_1(C_67), B_69) | ~r1_tarski(k1_relat_1(C_67), A_68) | ~v1_relat_1(C_67))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.61  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.54/1.61  tff(c_1009, plain, (![C_156, A_157, B_158]: (r1_tarski(C_156, k2_zfmisc_1(A_157, B_158)) | ~r1_tarski(k2_relat_1(C_156), B_158) | ~r1_tarski(k1_relat_1(C_156), A_157) | ~v1_relat_1(C_156))), inference(resolution, [status(thm)], [c_257, c_16])).
% 3.54/1.61  tff(c_1014, plain, (![C_159, A_160]: (r1_tarski(C_159, k2_zfmisc_1(A_160, k2_relat_1(C_159))) | ~r1_tarski(k1_relat_1(C_159), A_160) | ~v1_relat_1(C_159))), inference(resolution, [status(thm)], [c_6, c_1009])).
% 3.54/1.61  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.54/1.61  tff(c_138, plain, (![A_45, B_46, C_47]: (k1_relset_1(A_45, B_46, C_47)=k1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.54/1.61  tff(c_153, plain, (![A_45, B_46, A_6]: (k1_relset_1(A_45, B_46, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_45, B_46)))), inference(resolution, [status(thm)], [c_18, c_138])).
% 3.54/1.61  tff(c_1036, plain, (![A_162, C_163]: (k1_relset_1(A_162, k2_relat_1(C_163), C_163)=k1_relat_1(C_163) | ~r1_tarski(k1_relat_1(C_163), A_162) | ~v1_relat_1(C_163))), inference(resolution, [status(thm)], [c_1014, c_153])).
% 3.54/1.61  tff(c_1048, plain, (![C_163]: (k1_relset_1(k1_relat_1(C_163), k2_relat_1(C_163), C_163)=k1_relat_1(C_163) | ~v1_relat_1(C_163))), inference(resolution, [status(thm)], [c_6, c_1036])).
% 3.54/1.61  tff(c_1013, plain, (![C_156, A_157]: (r1_tarski(C_156, k2_zfmisc_1(A_157, k2_relat_1(C_156))) | ~r1_tarski(k1_relat_1(C_156), A_157) | ~v1_relat_1(C_156))), inference(resolution, [status(thm)], [c_6, c_1009])).
% 3.54/1.61  tff(c_956, plain, (![B_148, C_149, A_150]: (k1_xboole_0=B_148 | v1_funct_2(C_149, A_150, B_148) | k1_relset_1(A_150, B_148, C_149)!=A_150 | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_150, B_148))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.54/1.61  tff(c_1072, plain, (![B_165, A_166, A_167]: (k1_xboole_0=B_165 | v1_funct_2(A_166, A_167, B_165) | k1_relset_1(A_167, B_165, A_166)!=A_167 | ~r1_tarski(A_166, k2_zfmisc_1(A_167, B_165)))), inference(resolution, [status(thm)], [c_18, c_956])).
% 3.54/1.61  tff(c_1221, plain, (![C_187, A_188]: (k2_relat_1(C_187)=k1_xboole_0 | v1_funct_2(C_187, A_188, k2_relat_1(C_187)) | k1_relset_1(A_188, k2_relat_1(C_187), C_187)!=A_188 | ~r1_tarski(k1_relat_1(C_187), A_188) | ~v1_relat_1(C_187))), inference(resolution, [status(thm)], [c_1013, c_1072])).
% 3.54/1.61  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.54/1.61  tff(c_38, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.54/1.61  tff(c_44, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38])).
% 3.54/1.61  tff(c_86, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.54/1.61  tff(c_1235, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1221, c_86])).
% 3.54/1.61  tff(c_1243, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6, c_1235])).
% 3.54/1.61  tff(c_1244, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1243])).
% 3.54/1.61  tff(c_1276, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1048, c_1244])).
% 3.54/1.61  tff(c_1280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_1276])).
% 3.54/1.61  tff(c_1281, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1243])).
% 3.54/1.61  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.54/1.61  tff(c_1029, plain, (![A_160, C_159]: (k2_zfmisc_1(A_160, k2_relat_1(C_159))=C_159 | ~r1_tarski(k2_zfmisc_1(A_160, k2_relat_1(C_159)), C_159) | ~r1_tarski(k1_relat_1(C_159), A_160) | ~v1_relat_1(C_159))), inference(resolution, [status(thm)], [c_1014, c_2])).
% 3.54/1.61  tff(c_1290, plain, (![A_160]: (k2_zfmisc_1(A_160, k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(A_160, k1_xboole_0), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), A_160) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1281, c_1029])).
% 3.54/1.61  tff(c_1308, plain, (![A_160]: (k1_xboole_0='#skF_1' | ~r1_tarski(k1_relat_1('#skF_1'), A_160))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_85, c_10, c_10, c_1281, c_1290])).
% 3.54/1.61  tff(c_1326, plain, (![A_192]: (~r1_tarski(k1_relat_1('#skF_1'), A_192))), inference(splitLeft, [status(thm)], [c_1308])).
% 3.54/1.61  tff(c_1336, plain, $false, inference(resolution, [status(thm)], [c_6, c_1326])).
% 3.54/1.61  tff(c_1337, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1308])).
% 3.54/1.61  tff(c_328, plain, (![C_82, A_83, B_84]: (r1_tarski(C_82, k2_zfmisc_1(A_83, B_84)) | ~r1_tarski(k2_relat_1(C_82), B_84) | ~r1_tarski(k1_relat_1(C_82), A_83) | ~v1_relat_1(C_82))), inference(resolution, [status(thm)], [c_257, c_16])).
% 3.54/1.61  tff(c_376, plain, (![C_90, A_91]: (r1_tarski(C_90, k2_zfmisc_1(A_91, k2_relat_1(C_90))) | ~r1_tarski(k1_relat_1(C_90), A_91) | ~v1_relat_1(C_90))), inference(resolution, [status(thm)], [c_6, c_328])).
% 3.54/1.61  tff(c_393, plain, (![A_93, C_94]: (k1_relset_1(A_93, k2_relat_1(C_94), C_94)=k1_relat_1(C_94) | ~r1_tarski(k1_relat_1(C_94), A_93) | ~v1_relat_1(C_94))), inference(resolution, [status(thm)], [c_376, c_153])).
% 3.54/1.61  tff(c_401, plain, (![C_94]: (k1_relset_1(k1_relat_1(C_94), k2_relat_1(C_94), C_94)=k1_relat_1(C_94) | ~v1_relat_1(C_94))), inference(resolution, [status(thm)], [c_6, c_393])).
% 3.54/1.61  tff(c_24, plain, (![C_16, A_14, B_15]: (m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~r1_tarski(k2_relat_1(C_16), B_15) | ~r1_tarski(k1_relat_1(C_16), A_14) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.54/1.61  tff(c_333, plain, (![B_85, C_86, A_87]: (k1_xboole_0=B_85 | v1_funct_2(C_86, A_87, B_85) | k1_relset_1(A_87, B_85, C_86)!=A_87 | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_85))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.54/1.61  tff(c_581, plain, (![B_119, C_120, A_121]: (k1_xboole_0=B_119 | v1_funct_2(C_120, A_121, B_119) | k1_relset_1(A_121, B_119, C_120)!=A_121 | ~r1_tarski(k2_relat_1(C_120), B_119) | ~r1_tarski(k1_relat_1(C_120), A_121) | ~v1_relat_1(C_120))), inference(resolution, [status(thm)], [c_24, c_333])).
% 3.54/1.61  tff(c_590, plain, (![C_122, A_123]: (k2_relat_1(C_122)=k1_xboole_0 | v1_funct_2(C_122, A_123, k2_relat_1(C_122)) | k1_relset_1(A_123, k2_relat_1(C_122), C_122)!=A_123 | ~r1_tarski(k1_relat_1(C_122), A_123) | ~v1_relat_1(C_122))), inference(resolution, [status(thm)], [c_6, c_581])).
% 3.54/1.61  tff(c_608, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_590, c_86])).
% 3.54/1.61  tff(c_617, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6, c_608])).
% 3.54/1.61  tff(c_618, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_617])).
% 3.54/1.61  tff(c_621, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_401, c_618])).
% 3.54/1.61  tff(c_625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_621])).
% 3.54/1.61  tff(c_626, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_617])).
% 3.54/1.61  tff(c_391, plain, (![A_91, C_90]: (k2_zfmisc_1(A_91, k2_relat_1(C_90))=C_90 | ~r1_tarski(k2_zfmisc_1(A_91, k2_relat_1(C_90)), C_90) | ~r1_tarski(k1_relat_1(C_90), A_91) | ~v1_relat_1(C_90))), inference(resolution, [status(thm)], [c_376, c_2])).
% 3.54/1.61  tff(c_637, plain, (![A_91]: (k2_zfmisc_1(A_91, k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(A_91, k1_xboole_0), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), A_91) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_626, c_391])).
% 3.54/1.61  tff(c_657, plain, (![A_91]: (k1_xboole_0='#skF_1' | ~r1_tarski(k1_relat_1('#skF_1'), A_91))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_85, c_10, c_10, c_626, c_637])).
% 3.54/1.61  tff(c_670, plain, (![A_124]: (~r1_tarski(k1_relat_1('#skF_1'), A_124))), inference(splitLeft, [status(thm)], [c_657])).
% 3.54/1.61  tff(c_680, plain, $false, inference(resolution, [status(thm)], [c_6, c_670])).
% 3.54/1.61  tff(c_681, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_657])).
% 3.54/1.61  tff(c_154, plain, (![A_45, B_46]: (k1_relset_1(A_45, B_46, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_138])).
% 3.54/1.61  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.54/1.61  tff(c_30, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.54/1.61  tff(c_247, plain, (![C_65, B_66]: (v1_funct_2(C_65, k1_xboole_0, B_66) | k1_relset_1(k1_xboole_0, B_66, C_65)!=k1_xboole_0 | ~m1_subset_1(C_65, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_30])).
% 3.54/1.61  tff(c_253, plain, (![B_66]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_66) | k1_relset_1(k1_xboole_0, B_66, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_247])).
% 3.54/1.61  tff(c_256, plain, (![B_66]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_66) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_253])).
% 3.54/1.61  tff(c_275, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_256])).
% 3.54/1.61  tff(c_701, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_681, c_681, c_275])).
% 3.54/1.61  tff(c_26, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_17, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.54/1.61  tff(c_46, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_26])).
% 3.54/1.61  tff(c_867, plain, (![A_135]: (v1_funct_2('#skF_1', A_135, '#skF_1') | A_135='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_681, c_681, c_681, c_46])).
% 3.54/1.61  tff(c_628, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_626, c_86])).
% 3.54/1.61  tff(c_682, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_681, c_628])).
% 3.54/1.61  tff(c_870, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_867, c_682])).
% 3.54/1.61  tff(c_876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_701, c_870])).
% 3.54/1.61  tff(c_877, plain, (![B_66]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_66))), inference(splitRight, [status(thm)], [c_256])).
% 3.54/1.61  tff(c_1357, plain, (![B_66]: (v1_funct_2('#skF_1', '#skF_1', B_66))), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_1337, c_877])).
% 3.54/1.61  tff(c_878, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_256])).
% 3.54/1.61  tff(c_1358, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_1337, c_878])).
% 3.54/1.61  tff(c_1283, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1281, c_86])).
% 3.54/1.61  tff(c_1339, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1337, c_1283])).
% 3.54/1.61  tff(c_1459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1357, c_1358, c_1339])).
% 3.54/1.61  tff(c_1460, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_44])).
% 3.54/1.61  tff(c_1626, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1618, c_1460])).
% 3.54/1.61  tff(c_1641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_6, c_6, c_1626])).
% 3.54/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.54/1.61  
% 3.54/1.61  Inference rules
% 3.54/1.61  ----------------------
% 3.54/1.61  #Ref     : 0
% 3.54/1.61  #Sup     : 312
% 3.54/1.61  #Fact    : 0
% 3.54/1.61  #Define  : 0
% 3.54/1.61  #Split   : 6
% 3.54/1.61  #Chain   : 0
% 3.54/1.61  #Close   : 0
% 3.54/1.61  
% 3.54/1.61  Ordering : KBO
% 3.54/1.61  
% 3.54/1.61  Simplification rules
% 3.54/1.61  ----------------------
% 3.54/1.61  #Subsume      : 35
% 3.54/1.61  #Demod        : 397
% 3.54/1.61  #Tautology    : 146
% 3.54/1.61  #SimpNegUnit  : 9
% 3.54/1.61  #BackRed      : 75
% 3.54/1.61  
% 3.54/1.61  #Partial instantiations: 0
% 3.54/1.61  #Strategies tried      : 1
% 3.54/1.61  
% 3.54/1.61  Timing (in seconds)
% 3.54/1.61  ----------------------
% 3.54/1.61  Preprocessing        : 0.32
% 3.54/1.61  Parsing              : 0.17
% 3.54/1.61  CNF conversion       : 0.02
% 3.54/1.61  Main loop            : 0.51
% 3.54/1.61  Inferencing          : 0.18
% 3.54/1.61  Reduction            : 0.15
% 3.54/1.61  Demodulation         : 0.11
% 3.54/1.61  BG Simplification    : 0.03
% 3.54/1.61  Subsumption          : 0.11
% 3.54/1.61  Abstraction          : 0.03
% 3.54/1.61  MUC search           : 0.00
% 3.54/1.61  Cooper               : 0.00
% 3.54/1.61  Total                : 0.87
% 3.54/1.61  Index Insertion      : 0.00
% 3.54/1.61  Index Deletion       : 0.00
% 3.54/1.61  Index Matching       : 0.00
% 3.54/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
