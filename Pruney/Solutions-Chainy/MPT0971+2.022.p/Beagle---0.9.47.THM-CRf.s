%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:32 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 132 expanded)
%              Number of leaves         :   48 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  135 ( 260 expanded)
%              Number of equality atoms :   39 (  59 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_85,axiom,(
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

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
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

tff(c_42,plain,(
    ! [A_26,B_27] : v1_relat_1(k2_zfmisc_1(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_86,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_129,plain,(
    ! [B_102,A_103] :
      ( v1_relat_1(B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_103))
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_135,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_86,c_129])).

tff(c_139,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_135])).

tff(c_90,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    ! [A_28,C_64] :
      ( k1_funct_1(A_28,'#skF_6'(A_28,k2_relat_1(A_28),C_64)) = C_64
      | ~ r2_hidden(C_64,k2_relat_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_216,plain,(
    ! [C_116,B_117,A_118] :
      ( v5_relat_1(C_116,B_117)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_230,plain,(
    v5_relat_1('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_86,c_216])).

tff(c_349,plain,(
    ! [A_154,B_155,C_156] :
      ( k2_relset_1(A_154,B_155,C_156) = k2_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_363,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_86,c_349])).

tff(c_84,plain,(
    r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_366,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_363,c_84])).

tff(c_301,plain,(
    ! [B_141,A_142] :
      ( r1_tarski(k2_relat_1(B_141),A_142)
      | ~ v5_relat_1(B_141,A_142)
      | ~ v1_relat_1(B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,B_8) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_397,plain,(
    ! [B_160,A_161] :
      ( k2_xboole_0(k2_relat_1(B_160),A_161) = A_161
      | ~ v5_relat_1(B_160,A_161)
      | ~ v1_relat_1(B_160) ) ),
    inference(resolution,[status(thm)],[c_301,c_20])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_147,plain,(
    ! [A_106,B_107] :
      ( m1_subset_1(k1_tarski(A_106),k1_zfmisc_1(B_107))
      | ~ r2_hidden(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_166,plain,(
    ! [A_108,B_109] :
      ( r1_tarski(k1_tarski(A_108),B_109)
      | ~ r2_hidden(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_147,c_32])).

tff(c_185,plain,(
    ! [A_112,B_113] :
      ( k2_xboole_0(k1_tarski(A_112),B_113) = B_113
      | ~ r2_hidden(A_112,B_113) ) ),
    inference(resolution,[status(thm)],[c_166,c_20])).

tff(c_28,plain,(
    ! [A_15,B_16] : k2_xboole_0(k1_tarski(A_15),B_16) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_203,plain,(
    ! [B_114,A_115] :
      ( k1_xboole_0 != B_114
      | ~ r2_hidden(A_115,B_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_28])).

tff(c_214,plain,(
    ! [A_1,B_2,D_6] :
      ( k2_xboole_0(A_1,B_2) != k1_xboole_0
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(resolution,[status(thm)],[c_6,c_203])).

tff(c_494,plain,(
    ! [A_188,D_189,B_190] :
      ( k1_xboole_0 != A_188
      | ~ r2_hidden(D_189,k2_relat_1(B_190))
      | ~ v5_relat_1(B_190,A_188)
      | ~ v1_relat_1(B_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_214])).

tff(c_496,plain,(
    ! [A_188] :
      ( k1_xboole_0 != A_188
      | ~ v5_relat_1('#skF_10',A_188)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_366,c_494])).

tff(c_501,plain,(
    ! [A_191] :
      ( k1_xboole_0 != A_191
      | ~ v5_relat_1('#skF_10',A_191) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_496])).

tff(c_505,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(resolution,[status(thm)],[c_230,c_501])).

tff(c_88,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_378,plain,(
    ! [A_157,B_158,C_159] :
      ( k1_relset_1(A_157,B_158,C_159) = k1_relat_1(C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_392,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_86,c_378])).

tff(c_908,plain,(
    ! [B_272,A_273,C_274] :
      ( k1_xboole_0 = B_272
      | k1_relset_1(A_273,B_272,C_274) = A_273
      | ~ v1_funct_2(C_274,A_273,B_272)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_273,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_919,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_86,c_908])).

tff(c_924,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_392,c_919])).

tff(c_925,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_924])).

tff(c_48,plain,(
    ! [A_28,C_64] :
      ( r2_hidden('#skF_6'(A_28,k2_relat_1(A_28),C_64),k1_relat_1(A_28))
      | ~ r2_hidden(C_64,k2_relat_1(A_28))
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_931,plain,(
    ! [C_64] :
      ( r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_64),'#skF_7')
      | ~ r2_hidden(C_64,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_925,c_48])).

tff(c_961,plain,(
    ! [C_277] :
      ( r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_277),'#skF_7')
      | ~ r2_hidden(C_277,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_90,c_931])).

tff(c_82,plain,(
    ! [E_81] :
      ( k1_funct_1('#skF_10',E_81) != '#skF_9'
      | ~ r2_hidden(E_81,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_973,plain,(
    ! [C_278] :
      ( k1_funct_1('#skF_10','#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_278)) != '#skF_9'
      | ~ r2_hidden(C_278,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_961,c_82])).

tff(c_977,plain,(
    ! [C_64] :
      ( C_64 != '#skF_9'
      | ~ r2_hidden(C_64,k2_relat_1('#skF_10'))
      | ~ r2_hidden(C_64,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_973])).

tff(c_980,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_90,c_977])).

tff(c_982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_980,c_366])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:01:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.60  
% 3.42/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 3.42/1.61  
% 3.42/1.61  %Foreground sorts:
% 3.42/1.61  
% 3.42/1.61  
% 3.42/1.61  %Background operators:
% 3.42/1.61  
% 3.42/1.61  
% 3.42/1.61  %Foreground operators:
% 3.42/1.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.42/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.42/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.42/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.42/1.61  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.42/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.42/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.42/1.61  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.42/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.42/1.61  tff('#skF_10', type, '#skF_10': $i).
% 3.42/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.42/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.42/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.42/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.42/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.42/1.61  tff('#skF_9', type, '#skF_9': $i).
% 3.42/1.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.42/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.42/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.42/1.61  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.42/1.61  tff('#skF_8', type, '#skF_8': $i).
% 3.42/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.42/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.42/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.42/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.42/1.61  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.42/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.42/1.61  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.42/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.42/1.61  
% 3.70/1.62  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.70/1.62  tff(f_133, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 3.70/1.62  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.70/1.62  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.70/1.62  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.70/1.62  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.70/1.62  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.70/1.62  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.70/1.62  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.70/1.62  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 3.70/1.62  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.70/1.62  tff(f_47, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.70/1.62  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.70/1.62  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.70/1.62  tff(c_42, plain, (![A_26, B_27]: (v1_relat_1(k2_zfmisc_1(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.70/1.62  tff(c_86, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.70/1.62  tff(c_129, plain, (![B_102, A_103]: (v1_relat_1(B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(A_103)) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.70/1.62  tff(c_135, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_86, c_129])).
% 3.70/1.62  tff(c_139, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_135])).
% 3.70/1.62  tff(c_90, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.70/1.62  tff(c_46, plain, (![A_28, C_64]: (k1_funct_1(A_28, '#skF_6'(A_28, k2_relat_1(A_28), C_64))=C_64 | ~r2_hidden(C_64, k2_relat_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.70/1.62  tff(c_216, plain, (![C_116, B_117, A_118]: (v5_relat_1(C_116, B_117) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.70/1.62  tff(c_230, plain, (v5_relat_1('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_86, c_216])).
% 3.70/1.62  tff(c_349, plain, (![A_154, B_155, C_156]: (k2_relset_1(A_154, B_155, C_156)=k2_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.70/1.62  tff(c_363, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_86, c_349])).
% 3.70/1.62  tff(c_84, plain, (r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.70/1.62  tff(c_366, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_363, c_84])).
% 3.70/1.62  tff(c_301, plain, (![B_141, A_142]: (r1_tarski(k2_relat_1(B_141), A_142) | ~v5_relat_1(B_141, A_142) | ~v1_relat_1(B_141))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.70/1.62  tff(c_20, plain, (![A_7, B_8]: (k2_xboole_0(A_7, B_8)=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.70/1.62  tff(c_397, plain, (![B_160, A_161]: (k2_xboole_0(k2_relat_1(B_160), A_161)=A_161 | ~v5_relat_1(B_160, A_161) | ~v1_relat_1(B_160))), inference(resolution, [status(thm)], [c_301, c_20])).
% 3.70/1.62  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.70/1.62  tff(c_147, plain, (![A_106, B_107]: (m1_subset_1(k1_tarski(A_106), k1_zfmisc_1(B_107)) | ~r2_hidden(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.70/1.62  tff(c_32, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.70/1.62  tff(c_166, plain, (![A_108, B_109]: (r1_tarski(k1_tarski(A_108), B_109) | ~r2_hidden(A_108, B_109))), inference(resolution, [status(thm)], [c_147, c_32])).
% 3.70/1.62  tff(c_185, plain, (![A_112, B_113]: (k2_xboole_0(k1_tarski(A_112), B_113)=B_113 | ~r2_hidden(A_112, B_113))), inference(resolution, [status(thm)], [c_166, c_20])).
% 3.70/1.62  tff(c_28, plain, (![A_15, B_16]: (k2_xboole_0(k1_tarski(A_15), B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.70/1.62  tff(c_203, plain, (![B_114, A_115]: (k1_xboole_0!=B_114 | ~r2_hidden(A_115, B_114))), inference(superposition, [status(thm), theory('equality')], [c_185, c_28])).
% 3.70/1.62  tff(c_214, plain, (![A_1, B_2, D_6]: (k2_xboole_0(A_1, B_2)!=k1_xboole_0 | ~r2_hidden(D_6, A_1))), inference(resolution, [status(thm)], [c_6, c_203])).
% 3.70/1.62  tff(c_494, plain, (![A_188, D_189, B_190]: (k1_xboole_0!=A_188 | ~r2_hidden(D_189, k2_relat_1(B_190)) | ~v5_relat_1(B_190, A_188) | ~v1_relat_1(B_190))), inference(superposition, [status(thm), theory('equality')], [c_397, c_214])).
% 3.70/1.62  tff(c_496, plain, (![A_188]: (k1_xboole_0!=A_188 | ~v5_relat_1('#skF_10', A_188) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_366, c_494])).
% 3.70/1.62  tff(c_501, plain, (![A_191]: (k1_xboole_0!=A_191 | ~v5_relat_1('#skF_10', A_191))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_496])).
% 3.70/1.62  tff(c_505, plain, (k1_xboole_0!='#skF_8'), inference(resolution, [status(thm)], [c_230, c_501])).
% 3.70/1.62  tff(c_88, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.70/1.62  tff(c_378, plain, (![A_157, B_158, C_159]: (k1_relset_1(A_157, B_158, C_159)=k1_relat_1(C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.70/1.62  tff(c_392, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_86, c_378])).
% 3.70/1.62  tff(c_908, plain, (![B_272, A_273, C_274]: (k1_xboole_0=B_272 | k1_relset_1(A_273, B_272, C_274)=A_273 | ~v1_funct_2(C_274, A_273, B_272) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_273, B_272))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.70/1.62  tff(c_919, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_86, c_908])).
% 3.70/1.62  tff(c_924, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_392, c_919])).
% 3.70/1.62  tff(c_925, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_505, c_924])).
% 3.70/1.62  tff(c_48, plain, (![A_28, C_64]: (r2_hidden('#skF_6'(A_28, k2_relat_1(A_28), C_64), k1_relat_1(A_28)) | ~r2_hidden(C_64, k2_relat_1(A_28)) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.70/1.62  tff(c_931, plain, (![C_64]: (r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_64), '#skF_7') | ~r2_hidden(C_64, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_925, c_48])).
% 3.70/1.62  tff(c_961, plain, (![C_277]: (r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_277), '#skF_7') | ~r2_hidden(C_277, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_90, c_931])).
% 3.70/1.62  tff(c_82, plain, (![E_81]: (k1_funct_1('#skF_10', E_81)!='#skF_9' | ~r2_hidden(E_81, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.70/1.62  tff(c_973, plain, (![C_278]: (k1_funct_1('#skF_10', '#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_278))!='#skF_9' | ~r2_hidden(C_278, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_961, c_82])).
% 3.70/1.62  tff(c_977, plain, (![C_64]: (C_64!='#skF_9' | ~r2_hidden(C_64, k2_relat_1('#skF_10')) | ~r2_hidden(C_64, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_973])).
% 3.70/1.62  tff(c_980, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_90, c_977])).
% 3.70/1.62  tff(c_982, plain, $false, inference(negUnitSimplification, [status(thm)], [c_980, c_366])).
% 3.70/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.62  
% 3.70/1.62  Inference rules
% 3.70/1.62  ----------------------
% 3.70/1.62  #Ref     : 0
% 3.70/1.62  #Sup     : 196
% 3.70/1.62  #Fact    : 0
% 3.70/1.62  #Define  : 0
% 3.70/1.62  #Split   : 3
% 3.70/1.62  #Chain   : 0
% 3.70/1.62  #Close   : 0
% 3.70/1.62  
% 3.70/1.62  Ordering : KBO
% 3.70/1.62  
% 3.70/1.62  Simplification rules
% 3.70/1.62  ----------------------
% 3.70/1.62  #Subsume      : 33
% 3.70/1.62  #Demod        : 38
% 3.70/1.62  #Tautology    : 46
% 3.70/1.62  #SimpNegUnit  : 5
% 3.70/1.62  #BackRed      : 6
% 3.70/1.62  
% 3.70/1.62  #Partial instantiations: 0
% 3.70/1.62  #Strategies tried      : 1
% 3.70/1.62  
% 3.70/1.62  Timing (in seconds)
% 3.70/1.62  ----------------------
% 3.70/1.63  Preprocessing        : 0.34
% 3.70/1.63  Parsing              : 0.17
% 3.70/1.63  CNF conversion       : 0.03
% 3.70/1.63  Main loop            : 0.44
% 3.70/1.63  Inferencing          : 0.15
% 3.70/1.63  Reduction            : 0.13
% 3.70/1.63  Demodulation         : 0.09
% 3.70/1.63  BG Simplification    : 0.03
% 3.70/1.63  Subsumption          : 0.09
% 3.70/1.63  Abstraction          : 0.02
% 3.70/1.63  MUC search           : 0.00
% 3.70/1.63  Cooper               : 0.00
% 3.70/1.63  Total                : 0.81
% 3.70/1.63  Index Insertion      : 0.00
% 3.70/1.63  Index Deletion       : 0.00
% 3.70/1.63  Index Matching       : 0.00
% 3.70/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
