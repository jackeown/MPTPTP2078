%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:59 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 108 expanded)
%              Number of leaves         :   39 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 222 expanded)
%              Number of equality atoms :   32 (  50 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
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

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

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

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_54,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_77,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_81,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_77])).

tff(c_58,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_12,plain,(
    ! [A_11,C_47] :
      ( k1_funct_1(A_11,'#skF_4'(A_11,k2_relat_1(A_11),C_47)) = C_47
      | ~ r2_hidden(C_47,k2_relat_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_88,plain,(
    ! [C_80,B_81,A_82] :
      ( v5_relat_1(C_80,B_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_92,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_88])).

tff(c_109,plain,(
    ! [A_93,B_94,C_95] :
      ( k2_relset_1(A_93,B_94,C_95) = k2_relat_1(C_95)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_113,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_109])).

tff(c_52,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_116,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_52])).

tff(c_8,plain,(
    ! [C_10,A_7,B_8] :
      ( r2_hidden(C_10,A_7)
      | ~ r2_hidden(C_10,k2_relat_1(B_8))
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_123,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_5',A_7)
      | ~ v5_relat_1('#skF_8',A_7)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_116,c_8])).

tff(c_136,plain,(
    ! [A_98] :
      ( r2_hidden('#skF_5',A_98)
      | ~ v5_relat_1('#skF_8',A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_123])).

tff(c_140,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_92,c_136])).

tff(c_66,plain,(
    ! [A_73,B_74] :
      ( k2_xboole_0(k1_tarski(A_73),B_74) = B_74
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k1_tarski(A_3),B_4) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [B_74,A_73] :
      ( k1_xboole_0 != B_74
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_4])).

tff(c_147,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(resolution,[status(thm)],[c_140,c_71])).

tff(c_56,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_100,plain,(
    ! [A_90,B_91,C_92] :
      ( k1_relset_1(A_90,B_91,C_92) = k1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_104,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_100])).

tff(c_280,plain,(
    ! [B_131,A_132,C_133] :
      ( k1_xboole_0 = B_131
      | k1_relset_1(A_132,B_131,C_133) = A_132
      | ~ v1_funct_2(C_133,A_132,B_131)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_132,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_283,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_280])).

tff(c_286,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_104,c_283])).

tff(c_287,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_286])).

tff(c_165,plain,(
    ! [A_109,C_110] :
      ( r2_hidden('#skF_4'(A_109,k2_relat_1(A_109),C_110),k1_relat_1(A_109))
      | ~ r2_hidden(C_110,k2_relat_1(A_109))
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_177,plain,(
    ! [A_109,C_110] :
      ( m1_subset_1('#skF_4'(A_109,k2_relat_1(A_109),C_110),k1_relat_1(A_109))
      | ~ r2_hidden(C_110,k2_relat_1(A_109))
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(resolution,[status(thm)],[c_165,c_6])).

tff(c_295,plain,(
    ! [C_110] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_110),'#skF_6')
      | ~ r2_hidden(C_110,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_177])).

tff(c_326,plain,(
    ! [C_135] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_135),'#skF_6')
      | ~ r2_hidden(C_135,k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_58,c_295])).

tff(c_50,plain,(
    ! [E_67] :
      ( k1_funct_1('#skF_8',E_67) != '#skF_5'
      | ~ m1_subset_1(E_67,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_393,plain,(
    ! [C_138] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_138)) != '#skF_5'
      | ~ r2_hidden(C_138,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_326,c_50])).

tff(c_397,plain,(
    ! [C_47] :
      ( C_47 != '#skF_5'
      | ~ r2_hidden(C_47,k2_relat_1('#skF_8'))
      | ~ r2_hidden(C_47,k2_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_393])).

tff(c_447,plain,(
    ~ r2_hidden('#skF_5',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_58,c_397])).

tff(c_449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_447,c_116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:18:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.41  
% 2.66/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_1
% 2.66/1.41  
% 2.66/1.41  %Foreground sorts:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Background operators:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Foreground operators:
% 2.66/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.66/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.66/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.66/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.66/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.66/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.66/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.66/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.66/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.66/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.66/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.66/1.41  tff('#skF_8', type, '#skF_8': $i).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.66/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.66/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.66/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.41  
% 2.66/1.43  tff(f_112, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 2.66/1.43  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.66/1.43  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.66/1.43  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.66/1.43  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.66/1.43  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 2.66/1.43  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.66/1.43  tff(f_32, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.66/1.43  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.66/1.43  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.66/1.43  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 2.66/1.43  tff(c_54, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.66/1.43  tff(c_77, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.66/1.43  tff(c_81, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_77])).
% 2.66/1.43  tff(c_58, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.66/1.43  tff(c_12, plain, (![A_11, C_47]: (k1_funct_1(A_11, '#skF_4'(A_11, k2_relat_1(A_11), C_47))=C_47 | ~r2_hidden(C_47, k2_relat_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.66/1.43  tff(c_88, plain, (![C_80, B_81, A_82]: (v5_relat_1(C_80, B_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.66/1.43  tff(c_92, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_88])).
% 2.66/1.43  tff(c_109, plain, (![A_93, B_94, C_95]: (k2_relset_1(A_93, B_94, C_95)=k2_relat_1(C_95) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.66/1.43  tff(c_113, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_109])).
% 2.66/1.43  tff(c_52, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.66/1.43  tff(c_116, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_52])).
% 2.66/1.43  tff(c_8, plain, (![C_10, A_7, B_8]: (r2_hidden(C_10, A_7) | ~r2_hidden(C_10, k2_relat_1(B_8)) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.66/1.43  tff(c_123, plain, (![A_7]: (r2_hidden('#skF_5', A_7) | ~v5_relat_1('#skF_8', A_7) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_116, c_8])).
% 2.66/1.43  tff(c_136, plain, (![A_98]: (r2_hidden('#skF_5', A_98) | ~v5_relat_1('#skF_8', A_98))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_123])).
% 2.66/1.43  tff(c_140, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_92, c_136])).
% 2.66/1.43  tff(c_66, plain, (![A_73, B_74]: (k2_xboole_0(k1_tarski(A_73), B_74)=B_74 | ~r2_hidden(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.66/1.43  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k1_tarski(A_3), B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.66/1.43  tff(c_71, plain, (![B_74, A_73]: (k1_xboole_0!=B_74 | ~r2_hidden(A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_66, c_4])).
% 2.66/1.43  tff(c_147, plain, (k1_xboole_0!='#skF_7'), inference(resolution, [status(thm)], [c_140, c_71])).
% 2.66/1.43  tff(c_56, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.66/1.43  tff(c_100, plain, (![A_90, B_91, C_92]: (k1_relset_1(A_90, B_91, C_92)=k1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_90, B_91))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.66/1.43  tff(c_104, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_54, c_100])).
% 2.66/1.43  tff(c_280, plain, (![B_131, A_132, C_133]: (k1_xboole_0=B_131 | k1_relset_1(A_132, B_131, C_133)=A_132 | ~v1_funct_2(C_133, A_132, B_131) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_132, B_131))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.66/1.43  tff(c_283, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_280])).
% 2.66/1.43  tff(c_286, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_104, c_283])).
% 2.66/1.43  tff(c_287, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_147, c_286])).
% 2.66/1.43  tff(c_165, plain, (![A_109, C_110]: (r2_hidden('#skF_4'(A_109, k2_relat_1(A_109), C_110), k1_relat_1(A_109)) | ~r2_hidden(C_110, k2_relat_1(A_109)) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.66/1.43  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.66/1.43  tff(c_177, plain, (![A_109, C_110]: (m1_subset_1('#skF_4'(A_109, k2_relat_1(A_109), C_110), k1_relat_1(A_109)) | ~r2_hidden(C_110, k2_relat_1(A_109)) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(resolution, [status(thm)], [c_165, c_6])).
% 2.66/1.43  tff(c_295, plain, (![C_110]: (m1_subset_1('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_110), '#skF_6') | ~r2_hidden(C_110, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_287, c_177])).
% 2.66/1.43  tff(c_326, plain, (![C_135]: (m1_subset_1('#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_135), '#skF_6') | ~r2_hidden(C_135, k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_58, c_295])).
% 2.66/1.43  tff(c_50, plain, (![E_67]: (k1_funct_1('#skF_8', E_67)!='#skF_5' | ~m1_subset_1(E_67, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.66/1.43  tff(c_393, plain, (![C_138]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', k2_relat_1('#skF_8'), C_138))!='#skF_5' | ~r2_hidden(C_138, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_326, c_50])).
% 2.66/1.43  tff(c_397, plain, (![C_47]: (C_47!='#skF_5' | ~r2_hidden(C_47, k2_relat_1('#skF_8')) | ~r2_hidden(C_47, k2_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_393])).
% 2.66/1.43  tff(c_447, plain, (~r2_hidden('#skF_5', k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_58, c_397])).
% 2.66/1.43  tff(c_449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_447, c_116])).
% 2.66/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.43  
% 2.66/1.43  Inference rules
% 2.66/1.43  ----------------------
% 2.66/1.43  #Ref     : 0
% 2.66/1.43  #Sup     : 84
% 2.66/1.43  #Fact    : 0
% 2.66/1.43  #Define  : 0
% 2.66/1.43  #Split   : 0
% 2.66/1.43  #Chain   : 0
% 2.66/1.43  #Close   : 0
% 2.66/1.43  
% 2.66/1.43  Ordering : KBO
% 2.66/1.43  
% 2.66/1.43  Simplification rules
% 2.66/1.43  ----------------------
% 2.66/1.43  #Subsume      : 12
% 2.66/1.43  #Demod        : 29
% 2.66/1.43  #Tautology    : 15
% 2.66/1.43  #SimpNegUnit  : 3
% 2.66/1.43  #BackRed      : 6
% 2.66/1.43  
% 2.66/1.43  #Partial instantiations: 0
% 2.66/1.43  #Strategies tried      : 1
% 2.66/1.43  
% 2.66/1.43  Timing (in seconds)
% 2.66/1.43  ----------------------
% 2.66/1.43  Preprocessing        : 0.32
% 2.66/1.43  Parsing              : 0.16
% 2.66/1.43  CNF conversion       : 0.03
% 2.66/1.43  Main loop            : 0.28
% 2.66/1.43  Inferencing          : 0.11
% 2.66/1.43  Reduction            : 0.08
% 2.66/1.43  Demodulation         : 0.05
% 2.66/1.43  BG Simplification    : 0.02
% 2.66/1.43  Subsumption          : 0.05
% 2.66/1.43  Abstraction          : 0.02
% 2.66/1.43  MUC search           : 0.00
% 2.66/1.43  Cooper               : 0.00
% 2.66/1.43  Total                : 0.64
% 2.66/1.43  Index Insertion      : 0.00
% 2.66/1.43  Index Deletion       : 0.00
% 2.66/1.43  Index Matching       : 0.00
% 2.66/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
