%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:11 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 149 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :    8
%              Number of atoms          :  111 ( 272 expanded)
%              Number of equality atoms :   25 (  69 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(c_34,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_405,plain,(
    ! [A_116,B_117,C_118] :
      ( k2_relset_1(A_116,B_117,C_118) = k2_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_414,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_405])).

tff(c_40,plain,
    ( k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7'
    | r2_hidden('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_69,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_415,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_69])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_179,plain,(
    ! [A_82,B_83,C_84] :
      ( k2_relset_1(A_82,B_83,C_84) = k2_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_188,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_179])).

tff(c_189,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_69])).

tff(c_42,plain,(
    ! [D_41] :
      ( r2_hidden(k4_tarski('#skF_9'(D_41),D_41),'#skF_8')
      | ~ r2_hidden(D_41,'#skF_7')
      | r2_hidden('#skF_10','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_84,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_111,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_120,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_111])).

tff(c_122,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_69])).

tff(c_46,plain,(
    ! [D_41] :
      ( r2_hidden(k4_tarski('#skF_9'(D_41),D_41),'#skF_8')
      | ~ r2_hidden(D_41,'#skF_7')
      | k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_138,plain,(
    ! [D_41] :
      ( r2_hidden(k4_tarski('#skF_9'(D_41),D_41),'#skF_8')
      | ~ r2_hidden(D_41,'#skF_7')
      | k2_relat_1('#skF_8') = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_46])).

tff(c_140,plain,(
    ! [D_77] :
      ( r2_hidden(k4_tarski('#skF_9'(D_77),D_77),'#skF_8')
      | ~ r2_hidden(D_77,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_138])).

tff(c_38,plain,(
    ! [D_41,E_44] :
      ( r2_hidden(k4_tarski('#skF_9'(D_41),D_41),'#skF_8')
      | ~ r2_hidden(D_41,'#skF_7')
      | ~ r2_hidden(k4_tarski(E_44,'#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_99,plain,(
    ! [E_44] : ~ r2_hidden(k4_tarski(E_44,'#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_144,plain,(
    ~ r2_hidden('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_140,c_99])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_144])).

tff(c_156,plain,(
    ! [D_78] :
      ( r2_hidden(k4_tarski('#skF_9'(D_78),D_78),'#skF_8')
      | ~ r2_hidden(D_78,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_20,plain,(
    ! [C_25,A_10,D_28] :
      ( r2_hidden(C_25,k2_relat_1(A_10))
      | ~ r2_hidden(k4_tarski(D_28,C_25),A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_164,plain,(
    ! [D_79] :
      ( r2_hidden(D_79,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_79,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_156,c_20])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_194,plain,(
    ! [A_85] :
      ( r1_tarski(A_85,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_85,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_164,c_4])).

tff(c_199,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_194])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_205,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_199,c_8])).

tff(c_211,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_205])).

tff(c_343,plain,(
    ! [A_106,B_107,C_108] :
      ( m1_subset_1(k2_relset_1(A_106,B_107,C_108),k1_zfmisc_1(B_107))
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_356,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_343])).

tff(c_360,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_356])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_363,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_360,c_14])).

tff(c_367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_363])).

tff(c_372,plain,(
    ! [D_110] :
      ( r2_hidden(k4_tarski('#skF_9'(D_110),D_110),'#skF_8')
      | ~ r2_hidden(D_110,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_385,plain,(
    ! [D_111] :
      ( r2_hidden(D_111,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_111,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_372,c_20])).

tff(c_420,plain,(
    ! [A_119] :
      ( r1_tarski(A_119,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_1'(A_119,k2_relat_1('#skF_8')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_385,c_4])).

tff(c_425,plain,(
    r1_tarski('#skF_7',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6,c_420])).

tff(c_429,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_425,c_8])).

tff(c_432,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_415,c_429])).

tff(c_467,plain,(
    ! [A_128,B_129,C_130] :
      ( m1_subset_1(k2_relset_1(A_128,B_129,C_130),k1_zfmisc_1(B_129))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_480,plain,
    ( m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_467])).

tff(c_484,plain,(
    m1_subset_1(k2_relat_1('#skF_8'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_480])).

tff(c_487,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_484,c_14])).

tff(c_491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_432,c_487])).

tff(c_492,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_493,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_540,plain,(
    ! [A_148,B_149,C_150] :
      ( k2_relset_1(A_148,B_149,C_150) = k2_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_547,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_34,c_540])).

tff(c_550,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_547])).

tff(c_648,plain,(
    ! [A_171,C_172] :
      ( r2_hidden(k4_tarski('#skF_5'(A_171,k2_relat_1(A_171),C_172),C_172),A_171)
      | ~ r2_hidden(C_172,k2_relat_1(A_171)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [E_44] :
      ( k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7'
      | ~ r2_hidden(k4_tarski(E_44,'#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_499,plain,(
    ! [E_44] : ~ r2_hidden(k4_tarski(E_44,'#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_36])).

tff(c_657,plain,(
    ~ r2_hidden('#skF_10',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_648,c_499])).

tff(c_666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_550,c_657])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.42  
% 2.44/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.42  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_9 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 2.44/1.42  
% 2.44/1.42  %Foreground sorts:
% 2.44/1.42  
% 2.44/1.42  
% 2.44/1.42  %Background operators:
% 2.44/1.42  
% 2.44/1.42  
% 2.44/1.42  %Foreground operators:
% 2.44/1.42  tff('#skF_9', type, '#skF_9': $i > $i).
% 2.44/1.42  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.44/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.44/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.44/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.44/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.42  tff('#skF_10', type, '#skF_10': $i).
% 2.44/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.44/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.44/1.42  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.44/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.44/1.42  tff('#skF_8', type, '#skF_8': $i).
% 2.44/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.44/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.44/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.44/1.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.44/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.42  
% 2.44/1.44  tff(f_71, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relset_1)).
% 2.44/1.44  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.44/1.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.44/1.44  tff(f_50, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.44/1.44  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.44/1.44  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.44/1.44  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.44/1.44  tff(c_34, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.44/1.44  tff(c_405, plain, (![A_116, B_117, C_118]: (k2_relset_1(A_116, B_117, C_118)=k2_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.44/1.44  tff(c_414, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_405])).
% 2.44/1.44  tff(c_40, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7' | r2_hidden('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.44/1.44  tff(c_69, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_40])).
% 2.44/1.44  tff(c_415, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_414, c_69])).
% 2.44/1.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.44/1.44  tff(c_179, plain, (![A_82, B_83, C_84]: (k2_relset_1(A_82, B_83, C_84)=k2_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.44/1.44  tff(c_188, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_179])).
% 2.44/1.44  tff(c_189, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_188, c_69])).
% 2.44/1.44  tff(c_42, plain, (![D_41]: (r2_hidden(k4_tarski('#skF_9'(D_41), D_41), '#skF_8') | ~r2_hidden(D_41, '#skF_7') | r2_hidden('#skF_10', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.44/1.44  tff(c_84, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitLeft, [status(thm)], [c_42])).
% 2.44/1.44  tff(c_111, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.44/1.44  tff(c_120, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_111])).
% 2.44/1.44  tff(c_122, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_69])).
% 2.44/1.44  tff(c_46, plain, (![D_41]: (r2_hidden(k4_tarski('#skF_9'(D_41), D_41), '#skF_8') | ~r2_hidden(D_41, '#skF_7') | k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.44/1.44  tff(c_138, plain, (![D_41]: (r2_hidden(k4_tarski('#skF_9'(D_41), D_41), '#skF_8') | ~r2_hidden(D_41, '#skF_7') | k2_relat_1('#skF_8')='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_46])).
% 2.44/1.44  tff(c_140, plain, (![D_77]: (r2_hidden(k4_tarski('#skF_9'(D_77), D_77), '#skF_8') | ~r2_hidden(D_77, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_122, c_138])).
% 2.44/1.44  tff(c_38, plain, (![D_41, E_44]: (r2_hidden(k4_tarski('#skF_9'(D_41), D_41), '#skF_8') | ~r2_hidden(D_41, '#skF_7') | ~r2_hidden(k4_tarski(E_44, '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.44/1.44  tff(c_99, plain, (![E_44]: (~r2_hidden(k4_tarski(E_44, '#skF_10'), '#skF_8'))), inference(splitLeft, [status(thm)], [c_38])).
% 2.44/1.44  tff(c_144, plain, (~r2_hidden('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_140, c_99])).
% 2.44/1.44  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_144])).
% 2.44/1.44  tff(c_156, plain, (![D_78]: (r2_hidden(k4_tarski('#skF_9'(D_78), D_78), '#skF_8') | ~r2_hidden(D_78, '#skF_7'))), inference(splitRight, [status(thm)], [c_38])).
% 2.44/1.44  tff(c_20, plain, (![C_25, A_10, D_28]: (r2_hidden(C_25, k2_relat_1(A_10)) | ~r2_hidden(k4_tarski(D_28, C_25), A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.44/1.44  tff(c_164, plain, (![D_79]: (r2_hidden(D_79, k2_relat_1('#skF_8')) | ~r2_hidden(D_79, '#skF_7'))), inference(resolution, [status(thm)], [c_156, c_20])).
% 2.44/1.44  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.44/1.44  tff(c_194, plain, (![A_85]: (r1_tarski(A_85, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_85, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_164, c_4])).
% 2.44/1.44  tff(c_199, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_194])).
% 2.44/1.44  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.44  tff(c_205, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_199, c_8])).
% 2.44/1.44  tff(c_211, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_189, c_205])).
% 2.44/1.44  tff(c_343, plain, (![A_106, B_107, C_108]: (m1_subset_1(k2_relset_1(A_106, B_107, C_108), k1_zfmisc_1(B_107)) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.44/1.44  tff(c_356, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_188, c_343])).
% 2.44/1.44  tff(c_360, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_356])).
% 2.44/1.44  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.44/1.44  tff(c_363, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_360, c_14])).
% 2.44/1.44  tff(c_367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_363])).
% 2.44/1.44  tff(c_372, plain, (![D_110]: (r2_hidden(k4_tarski('#skF_9'(D_110), D_110), '#skF_8') | ~r2_hidden(D_110, '#skF_7'))), inference(splitRight, [status(thm)], [c_42])).
% 2.44/1.44  tff(c_385, plain, (![D_111]: (r2_hidden(D_111, k2_relat_1('#skF_8')) | ~r2_hidden(D_111, '#skF_7'))), inference(resolution, [status(thm)], [c_372, c_20])).
% 2.44/1.44  tff(c_420, plain, (![A_119]: (r1_tarski(A_119, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_1'(A_119, k2_relat_1('#skF_8')), '#skF_7'))), inference(resolution, [status(thm)], [c_385, c_4])).
% 2.44/1.44  tff(c_425, plain, (r1_tarski('#skF_7', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6, c_420])).
% 2.44/1.44  tff(c_429, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_425, c_8])).
% 2.44/1.44  tff(c_432, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_415, c_429])).
% 2.44/1.44  tff(c_467, plain, (![A_128, B_129, C_130]: (m1_subset_1(k2_relset_1(A_128, B_129, C_130), k1_zfmisc_1(B_129)) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.44/1.44  tff(c_480, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_414, c_467])).
% 2.44/1.44  tff(c_484, plain, (m1_subset_1(k2_relat_1('#skF_8'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_480])).
% 2.44/1.44  tff(c_487, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_484, c_14])).
% 2.44/1.44  tff(c_491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_432, c_487])).
% 2.44/1.44  tff(c_492, plain, (r2_hidden('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_40])).
% 2.44/1.44  tff(c_493, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_40])).
% 2.44/1.44  tff(c_540, plain, (![A_148, B_149, C_150]: (k2_relset_1(A_148, B_149, C_150)=k2_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.44/1.44  tff(c_547, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_34, c_540])).
% 2.44/1.44  tff(c_550, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_493, c_547])).
% 2.44/1.44  tff(c_648, plain, (![A_171, C_172]: (r2_hidden(k4_tarski('#skF_5'(A_171, k2_relat_1(A_171), C_172), C_172), A_171) | ~r2_hidden(C_172, k2_relat_1(A_171)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.44/1.44  tff(c_36, plain, (![E_44]: (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7' | ~r2_hidden(k4_tarski(E_44, '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.44/1.44  tff(c_499, plain, (![E_44]: (~r2_hidden(k4_tarski(E_44, '#skF_10'), '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_493, c_36])).
% 2.44/1.44  tff(c_657, plain, (~r2_hidden('#skF_10', k2_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_648, c_499])).
% 2.44/1.44  tff(c_666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_492, c_550, c_657])).
% 2.44/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.44  
% 2.44/1.44  Inference rules
% 2.44/1.44  ----------------------
% 2.44/1.44  #Ref     : 0
% 2.44/1.44  #Sup     : 129
% 2.44/1.44  #Fact    : 0
% 2.44/1.44  #Define  : 0
% 2.44/1.44  #Split   : 10
% 2.44/1.44  #Chain   : 0
% 2.44/1.44  #Close   : 0
% 2.44/1.44  
% 2.44/1.44  Ordering : KBO
% 2.44/1.44  
% 2.44/1.44  Simplification rules
% 2.44/1.44  ----------------------
% 2.44/1.44  #Subsume      : 13
% 2.44/1.44  #Demod        : 35
% 2.44/1.44  #Tautology    : 39
% 2.44/1.44  #SimpNegUnit  : 7
% 2.44/1.44  #BackRed      : 3
% 2.44/1.44  
% 2.44/1.44  #Partial instantiations: 0
% 2.44/1.44  #Strategies tried      : 1
% 2.44/1.44  
% 2.44/1.44  Timing (in seconds)
% 2.44/1.44  ----------------------
% 2.44/1.44  Preprocessing        : 0.31
% 2.44/1.44  Parsing              : 0.16
% 2.44/1.44  CNF conversion       : 0.03
% 2.44/1.44  Main loop            : 0.31
% 2.44/1.44  Inferencing          : 0.12
% 2.44/1.44  Reduction            : 0.08
% 2.44/1.44  Demodulation         : 0.06
% 2.44/1.44  BG Simplification    : 0.02
% 2.44/1.44  Subsumption          : 0.06
% 2.44/1.44  Abstraction          : 0.02
% 2.44/1.44  MUC search           : 0.00
% 2.44/1.44  Cooper               : 0.00
% 2.44/1.44  Total                : 0.66
% 2.44/1.44  Index Insertion      : 0.00
% 2.44/1.44  Index Deletion       : 0.00
% 2.44/1.44  Index Matching       : 0.00
% 2.44/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
