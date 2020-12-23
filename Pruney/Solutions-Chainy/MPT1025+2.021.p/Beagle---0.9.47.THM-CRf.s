%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:33 EST 2020

% Result     : Theorem 4.83s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 194 expanded)
%              Number of leaves         :   44 (  87 expanded)
%              Depth                    :    8
%              Number of atoms          :  156 ( 475 expanded)
%              Number of equality atoms :   31 (  88 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_138,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_101,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_110,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_101])).

tff(c_275,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( k7_relset_1(A_154,B_155,C_156,D_157) = k9_relat_1(C_156,D_157)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_282,plain,(
    ! [D_157] : k7_relset_1('#skF_7','#skF_8','#skF_10',D_157) = k9_relat_1('#skF_10',D_157) ),
    inference(resolution,[status(thm)],[c_70,c_275])).

tff(c_68,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_285,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_68])).

tff(c_216,plain,(
    ! [A_135,B_136,C_137] :
      ( r2_hidden('#skF_2'(A_135,B_136,C_137),k1_relat_1(C_137))
      | ~ r2_hidden(A_135,k9_relat_1(C_137,B_136))
      | ~ v1_relat_1(C_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_224,plain,(
    ! [C_137,A_135,B_136] :
      ( ~ v1_xboole_0(k1_relat_1(C_137))
      | ~ r2_hidden(A_135,k9_relat_1(C_137,B_136))
      | ~ v1_relat_1(C_137) ) ),
    inference(resolution,[status(thm)],[c_216,c_2])).

tff(c_318,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_285,c_224])).

tff(c_338,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_318])).

tff(c_74,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_111,plain,(
    ! [C_91,B_92,A_93] :
      ( v5_relat_1(C_91,B_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_120,plain,(
    v5_relat_1('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_111])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_749,plain,(
    ! [B_220,C_221,A_222] :
      ( r2_hidden(k1_funct_1(B_220,C_221),A_222)
      | ~ r2_hidden(C_221,k1_relat_1(B_220))
      | ~ v1_funct_1(B_220)
      | ~ v5_relat_1(B_220,A_222)
      | ~ v1_relat_1(B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_827,plain,(
    ! [A_223,C_224,B_225] :
      ( ~ v1_xboole_0(A_223)
      | ~ r2_hidden(C_224,k1_relat_1(B_225))
      | ~ v1_funct_1(B_225)
      | ~ v5_relat_1(B_225,A_223)
      | ~ v1_relat_1(B_225) ) ),
    inference(resolution,[status(thm)],[c_749,c_2])).

tff(c_851,plain,(
    ! [A_226,B_227] :
      ( ~ v1_xboole_0(A_226)
      | ~ v1_funct_1(B_227)
      | ~ v5_relat_1(B_227,A_226)
      | ~ v1_relat_1(B_227)
      | v1_xboole_0(k1_relat_1(B_227)) ) ),
    inference(resolution,[status(thm)],[c_4,c_827])).

tff(c_855,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_120,c_851])).

tff(c_859,plain,
    ( ~ v1_xboole_0('#skF_8')
    | v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_74,c_855])).

tff(c_860,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_338,c_859])).

tff(c_149,plain,(
    ! [A_105,B_106,C_107] :
      ( r2_hidden('#skF_2'(A_105,B_106,C_107),B_106)
      | ~ r2_hidden(A_105,k9_relat_1(C_107,B_106))
      | ~ v1_relat_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_66,plain,(
    ! [F_80] :
      ( k1_funct_1('#skF_10',F_80) != '#skF_11'
      | ~ r2_hidden(F_80,'#skF_9')
      | ~ m1_subset_1(F_80,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_160,plain,(
    ! [A_105,C_107] :
      ( k1_funct_1('#skF_10','#skF_2'(A_105,'#skF_9',C_107)) != '#skF_11'
      | ~ m1_subset_1('#skF_2'(A_105,'#skF_9',C_107),'#skF_7')
      | ~ r2_hidden(A_105,k9_relat_1(C_107,'#skF_9'))
      | ~ v1_relat_1(C_107) ) ),
    inference(resolution,[status(thm)],[c_149,c_66])).

tff(c_323,plain,
    ( k1_funct_1('#skF_10','#skF_2'('#skF_11','#skF_9','#skF_10')) != '#skF_11'
    | ~ m1_subset_1('#skF_2'('#skF_11','#skF_9','#skF_10'),'#skF_7')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_285,c_160])).

tff(c_344,plain,
    ( k1_funct_1('#skF_10','#skF_2'('#skF_11','#skF_9','#skF_10')) != '#skF_11'
    | ~ m1_subset_1('#skF_2'('#skF_11','#skF_9','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_323])).

tff(c_565,plain,(
    ~ m1_subset_1('#skF_2'('#skF_11','#skF_9','#skF_10'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_72,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_133,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_142,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_133])).

tff(c_1244,plain,(
    ! [B_288,A_289,C_290] :
      ( k1_xboole_0 = B_288
      | k1_relset_1(A_289,B_288,C_290) = A_289
      | ~ v1_funct_2(C_290,A_289,B_288)
      | ~ m1_subset_1(C_290,k1_zfmisc_1(k2_zfmisc_1(A_289,B_288))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1263,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_1244])).

tff(c_1270,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_142,c_1263])).

tff(c_1271,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1270])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_223,plain,(
    ! [A_135,B_136,C_137] :
      ( m1_subset_1('#skF_2'(A_135,B_136,C_137),k1_relat_1(C_137))
      | ~ r2_hidden(A_135,k9_relat_1(C_137,B_136))
      | ~ v1_relat_1(C_137) ) ),
    inference(resolution,[status(thm)],[c_216,c_8])).

tff(c_1306,plain,(
    ! [A_135,B_136] :
      ( m1_subset_1('#skF_2'(A_135,B_136,'#skF_10'),'#skF_7')
      | ~ r2_hidden(A_135,k9_relat_1('#skF_10',B_136))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1271,c_223])).

tff(c_1371,plain,(
    ! [A_294,B_295] :
      ( m1_subset_1('#skF_2'(A_294,B_295,'#skF_10'),'#skF_7')
      | ~ r2_hidden(A_294,k9_relat_1('#skF_10',B_295)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1306])).

tff(c_1386,plain,(
    m1_subset_1('#skF_2'('#skF_11','#skF_9','#skF_10'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_285,c_1371])).

tff(c_1401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_565,c_1386])).

tff(c_1402,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1270])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1409,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1402,c_6])).

tff(c_1411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_860,c_1409])).

tff(c_1412,plain,(
    k1_funct_1('#skF_10','#skF_2'('#skF_11','#skF_9','#skF_10')) != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_465,plain,(
    ! [A_169,B_170,C_171] :
      ( r2_hidden(k4_tarski('#skF_2'(A_169,B_170,C_171),A_169),C_171)
      | ~ r2_hidden(A_169,k9_relat_1(C_171,B_170))
      | ~ v1_relat_1(C_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40,plain,(
    ! [C_59,A_57,B_58] :
      ( k1_funct_1(C_59,A_57) = B_58
      | ~ r2_hidden(k4_tarski(A_57,B_58),C_59)
      | ~ v1_funct_1(C_59)
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2093,plain,(
    ! [C_409,A_410,B_411] :
      ( k1_funct_1(C_409,'#skF_2'(A_410,B_411,C_409)) = A_410
      | ~ v1_funct_1(C_409)
      | ~ r2_hidden(A_410,k9_relat_1(C_409,B_411))
      | ~ v1_relat_1(C_409) ) ),
    inference(resolution,[status(thm)],[c_465,c_40])).

tff(c_2104,plain,
    ( k1_funct_1('#skF_10','#skF_2'('#skF_11','#skF_9','#skF_10')) = '#skF_11'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_285,c_2093])).

tff(c_2116,plain,(
    k1_funct_1('#skF_10','#skF_2'('#skF_11','#skF_9','#skF_10')) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_74,c_2104])).

tff(c_2118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1412,c_2116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:05:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.83/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.84  
% 4.83/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.85  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 4.83/1.85  
% 4.83/1.85  %Foreground sorts:
% 4.83/1.85  
% 4.83/1.85  
% 4.83/1.85  %Background operators:
% 4.83/1.85  
% 4.83/1.85  
% 4.83/1.85  %Foreground operators:
% 4.83/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.83/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.83/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.83/1.85  tff('#skF_11', type, '#skF_11': $i).
% 4.83/1.85  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.83/1.85  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.83/1.85  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.83/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.83/1.85  tff('#skF_7', type, '#skF_7': $i).
% 4.83/1.85  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.83/1.85  tff('#skF_10', type, '#skF_10': $i).
% 4.83/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.83/1.85  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.83/1.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.83/1.85  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.83/1.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.83/1.85  tff('#skF_9', type, '#skF_9': $i).
% 4.83/1.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.83/1.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.83/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.83/1.85  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.83/1.85  tff('#skF_8', type, '#skF_8': $i).
% 4.83/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.83/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.83/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.83/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.83/1.85  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.83/1.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.83/1.85  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.83/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.83/1.85  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.83/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.83/1.85  
% 4.83/1.86  tff(f_138, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 4.83/1.86  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.83/1.86  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.83/1.86  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 4.83/1.86  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.83/1.86  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.83/1.86  tff(f_73, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 4.83/1.86  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.83/1.86  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.83/1.86  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 4.83/1.86  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.83/1.86  tff(f_83, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.83/1.86  tff(c_70, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.83/1.86  tff(c_101, plain, (![C_88, A_89, B_90]: (v1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.83/1.86  tff(c_110, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_70, c_101])).
% 4.83/1.86  tff(c_275, plain, (![A_154, B_155, C_156, D_157]: (k7_relset_1(A_154, B_155, C_156, D_157)=k9_relat_1(C_156, D_157) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.83/1.86  tff(c_282, plain, (![D_157]: (k7_relset_1('#skF_7', '#skF_8', '#skF_10', D_157)=k9_relat_1('#skF_10', D_157))), inference(resolution, [status(thm)], [c_70, c_275])).
% 4.83/1.86  tff(c_68, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.83/1.86  tff(c_285, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_68])).
% 4.83/1.86  tff(c_216, plain, (![A_135, B_136, C_137]: (r2_hidden('#skF_2'(A_135, B_136, C_137), k1_relat_1(C_137)) | ~r2_hidden(A_135, k9_relat_1(C_137, B_136)) | ~v1_relat_1(C_137))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.83/1.86  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.83/1.86  tff(c_224, plain, (![C_137, A_135, B_136]: (~v1_xboole_0(k1_relat_1(C_137)) | ~r2_hidden(A_135, k9_relat_1(C_137, B_136)) | ~v1_relat_1(C_137))), inference(resolution, [status(thm)], [c_216, c_2])).
% 4.83/1.86  tff(c_318, plain, (~v1_xboole_0(k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_285, c_224])).
% 4.83/1.86  tff(c_338, plain, (~v1_xboole_0(k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_318])).
% 4.83/1.86  tff(c_74, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.83/1.86  tff(c_111, plain, (![C_91, B_92, A_93]: (v5_relat_1(C_91, B_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_92))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.83/1.86  tff(c_120, plain, (v5_relat_1('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_70, c_111])).
% 4.83/1.86  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.83/1.86  tff(c_749, plain, (![B_220, C_221, A_222]: (r2_hidden(k1_funct_1(B_220, C_221), A_222) | ~r2_hidden(C_221, k1_relat_1(B_220)) | ~v1_funct_1(B_220) | ~v5_relat_1(B_220, A_222) | ~v1_relat_1(B_220))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.83/1.86  tff(c_827, plain, (![A_223, C_224, B_225]: (~v1_xboole_0(A_223) | ~r2_hidden(C_224, k1_relat_1(B_225)) | ~v1_funct_1(B_225) | ~v5_relat_1(B_225, A_223) | ~v1_relat_1(B_225))), inference(resolution, [status(thm)], [c_749, c_2])).
% 4.83/1.86  tff(c_851, plain, (![A_226, B_227]: (~v1_xboole_0(A_226) | ~v1_funct_1(B_227) | ~v5_relat_1(B_227, A_226) | ~v1_relat_1(B_227) | v1_xboole_0(k1_relat_1(B_227)))), inference(resolution, [status(thm)], [c_4, c_827])).
% 4.83/1.86  tff(c_855, plain, (~v1_xboole_0('#skF_8') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | v1_xboole_0(k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_120, c_851])).
% 4.83/1.86  tff(c_859, plain, (~v1_xboole_0('#skF_8') | v1_xboole_0(k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_74, c_855])).
% 4.83/1.86  tff(c_860, plain, (~v1_xboole_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_338, c_859])).
% 4.83/1.86  tff(c_149, plain, (![A_105, B_106, C_107]: (r2_hidden('#skF_2'(A_105, B_106, C_107), B_106) | ~r2_hidden(A_105, k9_relat_1(C_107, B_106)) | ~v1_relat_1(C_107))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.83/1.86  tff(c_66, plain, (![F_80]: (k1_funct_1('#skF_10', F_80)!='#skF_11' | ~r2_hidden(F_80, '#skF_9') | ~m1_subset_1(F_80, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.83/1.86  tff(c_160, plain, (![A_105, C_107]: (k1_funct_1('#skF_10', '#skF_2'(A_105, '#skF_9', C_107))!='#skF_11' | ~m1_subset_1('#skF_2'(A_105, '#skF_9', C_107), '#skF_7') | ~r2_hidden(A_105, k9_relat_1(C_107, '#skF_9')) | ~v1_relat_1(C_107))), inference(resolution, [status(thm)], [c_149, c_66])).
% 4.83/1.86  tff(c_323, plain, (k1_funct_1('#skF_10', '#skF_2'('#skF_11', '#skF_9', '#skF_10'))!='#skF_11' | ~m1_subset_1('#skF_2'('#skF_11', '#skF_9', '#skF_10'), '#skF_7') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_285, c_160])).
% 4.83/1.86  tff(c_344, plain, (k1_funct_1('#skF_10', '#skF_2'('#skF_11', '#skF_9', '#skF_10'))!='#skF_11' | ~m1_subset_1('#skF_2'('#skF_11', '#skF_9', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_323])).
% 4.83/1.86  tff(c_565, plain, (~m1_subset_1('#skF_2'('#skF_11', '#skF_9', '#skF_10'), '#skF_7')), inference(splitLeft, [status(thm)], [c_344])).
% 4.83/1.86  tff(c_72, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.83/1.86  tff(c_133, plain, (![A_99, B_100, C_101]: (k1_relset_1(A_99, B_100, C_101)=k1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.83/1.86  tff(c_142, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_70, c_133])).
% 4.83/1.86  tff(c_1244, plain, (![B_288, A_289, C_290]: (k1_xboole_0=B_288 | k1_relset_1(A_289, B_288, C_290)=A_289 | ~v1_funct_2(C_290, A_289, B_288) | ~m1_subset_1(C_290, k1_zfmisc_1(k2_zfmisc_1(A_289, B_288))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.83/1.86  tff(c_1263, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_70, c_1244])).
% 4.83/1.86  tff(c_1270, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_142, c_1263])).
% 4.83/1.86  tff(c_1271, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_1270])).
% 4.83/1.86  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.83/1.86  tff(c_223, plain, (![A_135, B_136, C_137]: (m1_subset_1('#skF_2'(A_135, B_136, C_137), k1_relat_1(C_137)) | ~r2_hidden(A_135, k9_relat_1(C_137, B_136)) | ~v1_relat_1(C_137))), inference(resolution, [status(thm)], [c_216, c_8])).
% 4.83/1.86  tff(c_1306, plain, (![A_135, B_136]: (m1_subset_1('#skF_2'(A_135, B_136, '#skF_10'), '#skF_7') | ~r2_hidden(A_135, k9_relat_1('#skF_10', B_136)) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1271, c_223])).
% 4.83/1.86  tff(c_1371, plain, (![A_294, B_295]: (m1_subset_1('#skF_2'(A_294, B_295, '#skF_10'), '#skF_7') | ~r2_hidden(A_294, k9_relat_1('#skF_10', B_295)))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1306])).
% 4.83/1.86  tff(c_1386, plain, (m1_subset_1('#skF_2'('#skF_11', '#skF_9', '#skF_10'), '#skF_7')), inference(resolution, [status(thm)], [c_285, c_1371])).
% 4.83/1.86  tff(c_1401, plain, $false, inference(negUnitSimplification, [status(thm)], [c_565, c_1386])).
% 4.83/1.86  tff(c_1402, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1270])).
% 4.83/1.86  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.83/1.86  tff(c_1409, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1402, c_6])).
% 4.83/1.86  tff(c_1411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_860, c_1409])).
% 4.83/1.86  tff(c_1412, plain, (k1_funct_1('#skF_10', '#skF_2'('#skF_11', '#skF_9', '#skF_10'))!='#skF_11'), inference(splitRight, [status(thm)], [c_344])).
% 4.83/1.86  tff(c_465, plain, (![A_169, B_170, C_171]: (r2_hidden(k4_tarski('#skF_2'(A_169, B_170, C_171), A_169), C_171) | ~r2_hidden(A_169, k9_relat_1(C_171, B_170)) | ~v1_relat_1(C_171))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.83/1.86  tff(c_40, plain, (![C_59, A_57, B_58]: (k1_funct_1(C_59, A_57)=B_58 | ~r2_hidden(k4_tarski(A_57, B_58), C_59) | ~v1_funct_1(C_59) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.83/1.86  tff(c_2093, plain, (![C_409, A_410, B_411]: (k1_funct_1(C_409, '#skF_2'(A_410, B_411, C_409))=A_410 | ~v1_funct_1(C_409) | ~r2_hidden(A_410, k9_relat_1(C_409, B_411)) | ~v1_relat_1(C_409))), inference(resolution, [status(thm)], [c_465, c_40])).
% 4.83/1.86  tff(c_2104, plain, (k1_funct_1('#skF_10', '#skF_2'('#skF_11', '#skF_9', '#skF_10'))='#skF_11' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_285, c_2093])).
% 4.83/1.86  tff(c_2116, plain, (k1_funct_1('#skF_10', '#skF_2'('#skF_11', '#skF_9', '#skF_10'))='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_74, c_2104])).
% 4.83/1.86  tff(c_2118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1412, c_2116])).
% 4.83/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/1.86  
% 4.83/1.86  Inference rules
% 4.83/1.86  ----------------------
% 4.83/1.86  #Ref     : 0
% 4.83/1.86  #Sup     : 403
% 4.83/1.86  #Fact    : 0
% 4.83/1.86  #Define  : 0
% 4.83/1.86  #Split   : 5
% 4.83/1.86  #Chain   : 0
% 4.83/1.86  #Close   : 0
% 4.83/1.86  
% 4.83/1.86  Ordering : KBO
% 4.83/1.86  
% 4.83/1.86  Simplification rules
% 4.83/1.86  ----------------------
% 4.83/1.86  #Subsume      : 43
% 4.83/1.86  #Demod        : 99
% 4.83/1.86  #Tautology    : 20
% 4.83/1.86  #SimpNegUnit  : 5
% 4.83/1.86  #BackRed      : 11
% 4.83/1.86  
% 4.83/1.86  #Partial instantiations: 0
% 4.83/1.86  #Strategies tried      : 1
% 4.83/1.86  
% 4.83/1.86  Timing (in seconds)
% 4.83/1.86  ----------------------
% 4.83/1.87  Preprocessing        : 0.37
% 4.83/1.87  Parsing              : 0.19
% 4.83/1.87  CNF conversion       : 0.03
% 4.83/1.87  Main loop            : 0.72
% 4.83/1.87  Inferencing          : 0.26
% 4.83/1.87  Reduction            : 0.18
% 4.83/1.87  Demodulation         : 0.13
% 4.83/1.87  BG Simplification    : 0.03
% 4.83/1.87  Subsumption          : 0.19
% 4.83/1.87  Abstraction          : 0.03
% 4.83/1.87  MUC search           : 0.00
% 4.83/1.87  Cooper               : 0.00
% 4.83/1.87  Total                : 1.14
% 4.83/1.87  Index Insertion      : 0.00
% 4.83/1.87  Index Deletion       : 0.00
% 4.83/1.87  Index Matching       : 0.00
% 4.83/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
