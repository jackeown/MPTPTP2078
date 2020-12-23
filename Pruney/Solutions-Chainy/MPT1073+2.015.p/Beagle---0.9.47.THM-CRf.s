%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:59 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 130 expanded)
%              Number of leaves         :   38 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  137 ( 309 expanded)
%              Number of equality atoms :   27 (  68 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_54,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_76,plain,(
    ! [C_76,B_77,A_78] :
      ( v5_relat_1(C_76,B_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_80,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_76])).

tff(c_71,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_75,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_71])).

tff(c_58,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_10,plain,(
    ! [A_8,C_44] :
      ( k1_funct_1(A_8,'#skF_4'(A_8,k2_relat_1(A_8),C_44)) = C_44
      | ~ r2_hidden(C_44,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_87,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_91,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_87])).

tff(c_254,plain,(
    ! [B_125,A_126,C_127] :
      ( k1_xboole_0 = B_125
      | k1_relset_1(A_126,B_125,C_127) = A_126
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_257,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_254])).

tff(c_260,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_91,c_257])).

tff(c_261,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_171,plain,(
    ! [A_107,C_108] :
      ( r2_hidden('#skF_4'(A_107,k2_relat_1(A_107),C_108),k1_relat_1(A_107))
      | ~ r2_hidden(C_108,k2_relat_1(A_107))
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_178,plain,(
    ! [A_107,C_108] :
      ( m1_subset_1('#skF_4'(A_107,k2_relat_1(A_107),C_108),k1_relat_1(A_107))
      | ~ r2_hidden(C_108,k2_relat_1(A_107))
      | ~ v1_funct_1(A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(resolution,[status(thm)],[c_171,c_4])).

tff(c_272,plain,(
    ! [C_108] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_108),'#skF_6')
      | ~ r2_hidden(C_108,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_178])).

tff(c_301,plain,(
    ! [C_130] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_130),'#skF_6')
      | ~ r2_hidden(C_130,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_58,c_272])).

tff(c_50,plain,(
    ! [E_66] :
      ( k1_funct_1('#skF_8',E_66) != '#skF_5'
      | ~ m1_subset_1(E_66,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_306,plain,(
    ! [C_131] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_131)) != '#skF_5'
      | ~ r2_hidden(C_131,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_301,c_50])).

tff(c_310,plain,(
    ! [C_44] :
      ( C_44 != '#skF_5'
      | ~ r2_hidden(C_44,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_44,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_306])).

tff(c_313,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_58,c_310])).

tff(c_97,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_101,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_97])).

tff(c_52,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_104,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_52])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_313,c_104])).

tff(c_316,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_12,plain,(
    ! [A_8,C_44] :
      ( r2_hidden('#skF_4'(A_8,k2_relat_1(A_8),C_44),k1_relat_1(A_8))
      | ~ r2_hidden(C_44,k2_relat_1(A_8))
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_137,plain,(
    ! [A_95,D_96] :
      ( r2_hidden(k1_funct_1(A_95,D_96),k2_relat_1(A_95))
      | ~ r2_hidden(D_96,k1_relat_1(A_95))
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [C_7,A_4,B_5] :
      ( r2_hidden(C_7,A_4)
      | ~ r2_hidden(C_7,k2_relat_1(B_5))
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_180,plain,(
    ! [A_109,D_110,A_111] :
      ( r2_hidden(k1_funct_1(A_109,D_110),A_111)
      | ~ v5_relat_1(A_109,A_111)
      | ~ r2_hidden(D_110,k1_relat_1(A_109))
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(resolution,[status(thm)],[c_137,c_6])).

tff(c_26,plain,(
    ! [B_49,A_48] :
      ( ~ r1_tarski(B_49,A_48)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_211,plain,(
    ! [A_118,A_119,D_120] :
      ( ~ r1_tarski(A_118,k1_funct_1(A_119,D_120))
      | ~ v5_relat_1(A_119,A_118)
      | ~ r2_hidden(D_120,k1_relat_1(A_119))
      | ~ v1_funct_1(A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(resolution,[status(thm)],[c_180,c_26])).

tff(c_218,plain,(
    ! [A_121,D_122] :
      ( ~ v5_relat_1(A_121,k1_xboole_0)
      | ~ r2_hidden(D_122,k1_relat_1(A_121))
      | ~ v1_funct_1(A_121)
      | ~ v1_relat_1(A_121) ) ),
    inference(resolution,[status(thm)],[c_2,c_211])).

tff(c_233,plain,(
    ! [A_123,C_124] :
      ( ~ v5_relat_1(A_123,k1_xboole_0)
      | ~ r2_hidden(C_124,k2_relat_1(A_123))
      | ~ v1_funct_1(A_123)
      | ~ v1_relat_1(A_123) ) ),
    inference(resolution,[status(thm)],[c_12,c_218])).

tff(c_247,plain,
    ( ~ v5_relat_1('#skF_8',k1_xboole_0)
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_104,c_233])).

tff(c_253,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_58,c_247])).

tff(c_326,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_253])).

tff(c_336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.41  
% 2.65/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.42  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.65/1.42  
% 2.65/1.42  %Foreground sorts:
% 2.65/1.42  
% 2.65/1.42  
% 2.65/1.42  %Background operators:
% 2.65/1.42  
% 2.65/1.42  
% 2.65/1.42  %Foreground operators:
% 2.65/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.65/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.65/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.65/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.42  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.65/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.65/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.65/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.65/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.65/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.65/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.65/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.65/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.65/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.65/1.42  tff('#skF_8', type, '#skF_8': $i).
% 2.65/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.65/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.65/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.65/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.65/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.42  
% 2.65/1.43  tff(f_112, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 2.65/1.43  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.65/1.43  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.65/1.43  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.65/1.43  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.65/1.43  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.65/1.43  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.65/1.43  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.65/1.43  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.65/1.43  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 2.65/1.43  tff(f_60, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.65/1.43  tff(c_54, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.65/1.43  tff(c_76, plain, (![C_76, B_77, A_78]: (v5_relat_1(C_76, B_77) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_77))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.65/1.43  tff(c_80, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_76])).
% 2.65/1.43  tff(c_71, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.65/1.43  tff(c_75, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_71])).
% 2.65/1.43  tff(c_58, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.65/1.43  tff(c_10, plain, (![A_8, C_44]: (k1_funct_1(A_8, '#skF_4'(A_8, k2_relat_1(A_8), C_44))=C_44 | ~r2_hidden(C_44, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.65/1.43  tff(c_56, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.65/1.43  tff(c_87, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.65/1.43  tff(c_91, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_87])).
% 2.65/1.43  tff(c_254, plain, (![B_125, A_126, C_127]: (k1_xboole_0=B_125 | k1_relset_1(A_126, B_125, C_127)=A_126 | ~v1_funct_2(C_127, A_126, B_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.65/1.43  tff(c_257, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_254])).
% 2.65/1.43  tff(c_260, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_91, c_257])).
% 2.65/1.43  tff(c_261, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_260])).
% 2.65/1.43  tff(c_171, plain, (![A_107, C_108]: (r2_hidden('#skF_4'(A_107, k2_relat_1(A_107), C_108), k1_relat_1(A_107)) | ~r2_hidden(C_108, k2_relat_1(A_107)) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.65/1.43  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(A_2, B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.43  tff(c_178, plain, (![A_107, C_108]: (m1_subset_1('#skF_4'(A_107, k2_relat_1(A_107), C_108), k1_relat_1(A_107)) | ~r2_hidden(C_108, k2_relat_1(A_107)) | ~v1_funct_1(A_107) | ~v1_relat_1(A_107))), inference(resolution, [status(thm)], [c_171, c_4])).
% 2.65/1.43  tff(c_272, plain, (![C_108]: (m1_subset_1('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_108), '#skF_6') | ~r2_hidden(C_108, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_178])).
% 2.65/1.43  tff(c_301, plain, (![C_130]: (m1_subset_1('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_130), '#skF_6') | ~r2_hidden(C_130, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_58, c_272])).
% 2.65/1.43  tff(c_50, plain, (![E_66]: (k1_funct_1('#skF_8', E_66)!='#skF_5' | ~m1_subset_1(E_66, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.65/1.43  tff(c_306, plain, (![C_131]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_131))!='#skF_5' | ~r2_hidden(C_131, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_301, c_50])).
% 2.65/1.43  tff(c_310, plain, (![C_44]: (C_44!='#skF_5' | ~r2_hidden(C_44, k2_relat_1('#skF_8')) | ~r2_hidden(C_44, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_306])).
% 2.65/1.43  tff(c_313, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_58, c_310])).
% 2.65/1.43  tff(c_97, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.65/1.43  tff(c_101, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_97])).
% 2.65/1.43  tff(c_52, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.65/1.43  tff(c_104, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_52])).
% 2.65/1.43  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_313, c_104])).
% 2.65/1.43  tff(c_316, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_260])).
% 2.65/1.43  tff(c_12, plain, (![A_8, C_44]: (r2_hidden('#skF_4'(A_8, k2_relat_1(A_8), C_44), k1_relat_1(A_8)) | ~r2_hidden(C_44, k2_relat_1(A_8)) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.65/1.43  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.65/1.43  tff(c_137, plain, (![A_95, D_96]: (r2_hidden(k1_funct_1(A_95, D_96), k2_relat_1(A_95)) | ~r2_hidden(D_96, k1_relat_1(A_95)) | ~v1_funct_1(A_95) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.65/1.43  tff(c_6, plain, (![C_7, A_4, B_5]: (r2_hidden(C_7, A_4) | ~r2_hidden(C_7, k2_relat_1(B_5)) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.65/1.43  tff(c_180, plain, (![A_109, D_110, A_111]: (r2_hidden(k1_funct_1(A_109, D_110), A_111) | ~v5_relat_1(A_109, A_111) | ~r2_hidden(D_110, k1_relat_1(A_109)) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(resolution, [status(thm)], [c_137, c_6])).
% 2.65/1.43  tff(c_26, plain, (![B_49, A_48]: (~r1_tarski(B_49, A_48) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.65/1.43  tff(c_211, plain, (![A_118, A_119, D_120]: (~r1_tarski(A_118, k1_funct_1(A_119, D_120)) | ~v5_relat_1(A_119, A_118) | ~r2_hidden(D_120, k1_relat_1(A_119)) | ~v1_funct_1(A_119) | ~v1_relat_1(A_119))), inference(resolution, [status(thm)], [c_180, c_26])).
% 2.65/1.43  tff(c_218, plain, (![A_121, D_122]: (~v5_relat_1(A_121, k1_xboole_0) | ~r2_hidden(D_122, k1_relat_1(A_121)) | ~v1_funct_1(A_121) | ~v1_relat_1(A_121))), inference(resolution, [status(thm)], [c_2, c_211])).
% 2.65/1.43  tff(c_233, plain, (![A_123, C_124]: (~v5_relat_1(A_123, k1_xboole_0) | ~r2_hidden(C_124, k2_relat_1(A_123)) | ~v1_funct_1(A_123) | ~v1_relat_1(A_123))), inference(resolution, [status(thm)], [c_12, c_218])).
% 2.65/1.43  tff(c_247, plain, (~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_104, c_233])).
% 2.65/1.43  tff(c_253, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_58, c_247])).
% 2.65/1.43  tff(c_326, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_316, c_253])).
% 2.65/1.43  tff(c_336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_326])).
% 2.65/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.43  
% 2.65/1.43  Inference rules
% 2.65/1.43  ----------------------
% 2.65/1.43  #Ref     : 0
% 2.65/1.43  #Sup     : 57
% 2.65/1.43  #Fact    : 0
% 2.65/1.43  #Define  : 0
% 2.65/1.43  #Split   : 1
% 2.65/1.43  #Chain   : 0
% 2.65/1.43  #Close   : 0
% 2.65/1.43  
% 2.65/1.43  Ordering : KBO
% 2.65/1.43  
% 2.65/1.43  Simplification rules
% 2.65/1.43  ----------------------
% 2.65/1.43  #Subsume      : 10
% 2.65/1.43  #Demod        : 46
% 2.65/1.43  #Tautology    : 13
% 2.65/1.43  #SimpNegUnit  : 1
% 2.65/1.43  #BackRed      : 15
% 2.65/1.44  
% 2.65/1.44  #Partial instantiations: 0
% 2.65/1.44  #Strategies tried      : 1
% 2.65/1.44  
% 2.65/1.44  Timing (in seconds)
% 2.65/1.44  ----------------------
% 2.65/1.44  Preprocessing        : 0.36
% 2.65/1.44  Parsing              : 0.18
% 2.65/1.44  CNF conversion       : 0.03
% 2.65/1.44  Main loop            : 0.25
% 2.65/1.44  Inferencing          : 0.09
% 2.65/1.44  Reduction            : 0.07
% 2.65/1.44  Demodulation         : 0.05
% 2.65/1.44  BG Simplification    : 0.02
% 2.65/1.44  Subsumption          : 0.04
% 2.65/1.44  Abstraction          : 0.01
% 2.65/1.44  MUC search           : 0.00
% 2.65/1.44  Cooper               : 0.00
% 2.65/1.44  Total                : 0.64
% 2.65/1.44  Index Insertion      : 0.00
% 2.65/1.44  Index Deletion       : 0.00
% 2.65/1.44  Index Matching       : 0.00
% 2.65/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
