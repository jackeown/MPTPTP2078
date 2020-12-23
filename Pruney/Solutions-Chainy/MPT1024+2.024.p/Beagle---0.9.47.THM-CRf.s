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
% DateTime   : Thu Dec  3 10:16:25 EST 2020

% Result     : Theorem 6.28s
% Output     : CNFRefutation 6.56s
% Verified   : 
% Statistics : Number of formulae       :  178 (1956 expanded)
%              Number of leaves         :   37 ( 694 expanded)
%              Depth                    :   12
%              Number of atoms          :  332 (6542 expanded)
%              Number of equality atoms :  114 (2390 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_68,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_79,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_83,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_79])).

tff(c_72,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_22,plain,(
    ! [A_16,B_39,D_54] :
      ( k1_funct_1(A_16,'#skF_5'(A_16,B_39,k9_relat_1(A_16,B_39),D_54)) = D_54
      | ~ r2_hidden(D_54,k9_relat_1(A_16,B_39))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_16,B_39,D_54] :
      ( r2_hidden('#skF_5'(A_16,B_39,k9_relat_1(A_16,B_39),D_54),B_39)
      | ~ r2_hidden(D_54,k9_relat_1(A_16,B_39))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_70,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_93,plain,(
    ! [A_98,B_99,C_100] :
      ( k1_relset_1(A_98,B_99,C_100) = k1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_97,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_93])).

tff(c_4629,plain,(
    ! [B_730,A_731,C_732] :
      ( k1_xboole_0 = B_730
      | k1_relset_1(A_731,B_730,C_732) = A_731
      | ~ v1_funct_2(C_732,A_731,B_730)
      | ~ m1_subset_1(C_732,k1_zfmisc_1(k2_zfmisc_1(A_731,B_730))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4632,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_4629])).

tff(c_4635,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_97,c_4632])).

tff(c_4636,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4635])).

tff(c_5003,plain,(
    ! [A_756,B_757,D_758] :
      ( r2_hidden('#skF_5'(A_756,B_757,k9_relat_1(A_756,B_757),D_758),k1_relat_1(A_756))
      | ~ r2_hidden(D_758,k9_relat_1(A_756,B_757))
      | ~ v1_funct_1(A_756)
      | ~ v1_relat_1(A_756) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5014,plain,(
    ! [B_757,D_758] :
      ( r2_hidden('#skF_5'('#skF_9',B_757,k9_relat_1('#skF_9',B_757),D_758),'#skF_6')
      | ~ r2_hidden(D_758,k9_relat_1('#skF_9',B_757))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4636,c_5003])).

tff(c_5020,plain,(
    ! [B_759,D_760] :
      ( r2_hidden('#skF_5'('#skF_9',B_759,k9_relat_1('#skF_9',B_759),D_760),'#skF_6')
      | ~ r2_hidden(D_760,k9_relat_1('#skF_9',B_759)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_72,c_5014])).

tff(c_64,plain,(
    ! [F_77] :
      ( k1_funct_1('#skF_9',F_77) != '#skF_10'
      | ~ r2_hidden(F_77,'#skF_8')
      | ~ r2_hidden(F_77,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_5046,plain,(
    ! [B_766,D_767] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',B_766,k9_relat_1('#skF_9',B_766),D_767)) != '#skF_10'
      | ~ r2_hidden('#skF_5'('#skF_9',B_766,k9_relat_1('#skF_9',B_766),D_767),'#skF_8')
      | ~ r2_hidden(D_767,k9_relat_1('#skF_9',B_766)) ) ),
    inference(resolution,[status(thm)],[c_5020,c_64])).

tff(c_5050,plain,(
    ! [D_54] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_54)) != '#skF_10'
      | ~ r2_hidden(D_54,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_24,c_5046])).

tff(c_5083,plain,(
    ! [D_776] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_776)) != '#skF_10'
      | ~ r2_hidden(D_776,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_72,c_5050])).

tff(c_5087,plain,(
    ! [D_54] :
      ( D_54 != '#skF_10'
      | ~ r2_hidden(D_54,k9_relat_1('#skF_9','#skF_8'))
      | ~ r2_hidden(D_54,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5083])).

tff(c_5090,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_72,c_5087])).

tff(c_150,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k7_relset_1(A_122,B_123,C_124,D_125) = k9_relat_1(C_124,D_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_153,plain,(
    ! [D_125] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_125) = k9_relat_1('#skF_9',D_125) ),
    inference(resolution,[status(thm)],[c_68,c_150])).

tff(c_66,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_157,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_66])).

tff(c_5092,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5090,c_157])).

tff(c_5094,plain,(
    k1_relat_1('#skF_9') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4635])).

tff(c_5093,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_4635])).

tff(c_54,plain,(
    ! [C_72,A_70] :
      ( k1_xboole_0 = C_72
      | ~ v1_funct_2(C_72,A_70,k1_xboole_0)
      | k1_xboole_0 = A_70
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6091,plain,(
    ! [C_890,A_891] :
      ( C_890 = '#skF_7'
      | ~ v1_funct_2(C_890,A_891,'#skF_7')
      | A_891 = '#skF_7'
      | ~ m1_subset_1(C_890,k1_zfmisc_1(k2_zfmisc_1(A_891,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5093,c_5093,c_5093,c_5093,c_54])).

tff(c_6094,plain,
    ( '#skF_7' = '#skF_9'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_68,c_6091])).

tff(c_6097,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6094])).

tff(c_6098,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6097])).

tff(c_6137,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6098,c_70])).

tff(c_6135,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_9') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6098,c_97])).

tff(c_6136,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6098,c_68])).

tff(c_60,plain,(
    ! [B_71,C_72] :
      ( k1_relset_1(k1_xboole_0,B_71,C_72) = k1_xboole_0
      | ~ v1_funct_2(C_72,k1_xboole_0,B_71)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_5106,plain,(
    ! [B_71,C_72] :
      ( k1_relset_1('#skF_7',B_71,C_72) = '#skF_7'
      | ~ v1_funct_2(C_72,'#skF_7',B_71)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_71))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5093,c_5093,c_5093,c_5093,c_60])).

tff(c_6945,plain,(
    ! [B_964,C_965] :
      ( k1_relset_1('#skF_6',B_964,C_965) = '#skF_6'
      | ~ v1_funct_2(C_965,'#skF_6',B_964)
      | ~ m1_subset_1(C_965,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_964))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6098,c_6098,c_6098,c_6098,c_5106])).

tff(c_6948,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_6136,c_6945])).

tff(c_6951,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6137,c_6135,c_6948])).

tff(c_6953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5094,c_6951])).

tff(c_6954,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_6097])).

tff(c_185,plain,(
    ! [A_138,B_139,C_140] :
      ( r2_hidden(k4_tarski('#skF_1'(A_138,B_139,C_140),A_138),C_140)
      | ~ r2_hidden(A_138,k9_relat_1(C_140,B_139))
      | ~ v1_relat_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_216,plain,(
    ! [A_138,B_139] :
      ( k1_funct_1('#skF_9',k4_tarski('#skF_1'(A_138,B_139,'#skF_6'),A_138)) != '#skF_10'
      | ~ r2_hidden(k4_tarski('#skF_1'(A_138,B_139,'#skF_6'),A_138),'#skF_8')
      | ~ r2_hidden(A_138,k9_relat_1('#skF_6',B_139))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_185,c_64])).

tff(c_247,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_1475,plain,(
    ! [B_331,A_332,C_333] :
      ( k1_xboole_0 = B_331
      | k1_relset_1(A_332,B_331,C_333) = A_332
      | ~ v1_funct_2(C_333,A_332,B_331)
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_332,B_331))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1478,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_1475])).

tff(c_1481,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_97,c_1478])).

tff(c_1482,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1481])).

tff(c_2573,plain,(
    ! [A_449,B_450,D_451] :
      ( r2_hidden('#skF_5'(A_449,B_450,k9_relat_1(A_449,B_450),D_451),k1_relat_1(A_449))
      | ~ r2_hidden(D_451,k9_relat_1(A_449,B_450))
      | ~ v1_funct_1(A_449)
      | ~ v1_relat_1(A_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2588,plain,(
    ! [B_450,D_451] :
      ( r2_hidden('#skF_5'('#skF_9',B_450,k9_relat_1('#skF_9',B_450),D_451),'#skF_6')
      | ~ r2_hidden(D_451,k9_relat_1('#skF_9',B_450))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1482,c_2573])).

tff(c_2596,plain,(
    ! [B_452,D_453] :
      ( r2_hidden('#skF_5'('#skF_9',B_452,k9_relat_1('#skF_9',B_452),D_453),'#skF_6')
      | ~ r2_hidden(D_453,k9_relat_1('#skF_9',B_452)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_72,c_2588])).

tff(c_2616,plain,(
    ! [B_456,D_457] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',B_456,k9_relat_1('#skF_9',B_456),D_457)) != '#skF_10'
      | ~ r2_hidden('#skF_5'('#skF_9',B_456,k9_relat_1('#skF_9',B_456),D_457),'#skF_8')
      | ~ r2_hidden(D_457,k9_relat_1('#skF_9',B_456)) ) ),
    inference(resolution,[status(thm)],[c_2596,c_64])).

tff(c_2620,plain,(
    ! [D_54] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_54)) != '#skF_10'
      | ~ r2_hidden(D_54,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_24,c_2616])).

tff(c_2624,plain,(
    ! [D_458] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_458)) != '#skF_10'
      | ~ r2_hidden(D_458,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_72,c_2620])).

tff(c_2628,plain,(
    ! [D_54] :
      ( D_54 != '#skF_10'
      | ~ r2_hidden(D_54,k9_relat_1('#skF_9','#skF_8'))
      | ~ r2_hidden(D_54,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2624])).

tff(c_2631,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_72,c_2628])).

tff(c_2633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2631,c_157])).

tff(c_2634,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1481])).

tff(c_3222,plain,(
    ! [C_538,A_539] :
      ( C_538 = '#skF_7'
      | ~ v1_funct_2(C_538,A_539,'#skF_7')
      | A_539 = '#skF_7'
      | ~ m1_subset_1(C_538,k1_zfmisc_1(k2_zfmisc_1(A_539,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2634,c_2634,c_2634,c_2634,c_54])).

tff(c_3225,plain,
    ( '#skF_7' = '#skF_9'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_68,c_3222])).

tff(c_3228,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_3225])).

tff(c_3229,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3228])).

tff(c_1001,plain,(
    ! [A_262,B_263,D_264] :
      ( k1_funct_1(A_262,'#skF_5'(A_262,B_263,k9_relat_1(A_262,B_263),D_264)) = D_264
      | ~ r2_hidden(D_264,k9_relat_1(A_262,B_263))
      | ~ v1_funct_1(A_262)
      | ~ v1_relat_1(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_266,plain,(
    ! [B_160,A_161,C_162] :
      ( k1_xboole_0 = B_160
      | k1_relset_1(A_161,B_160,C_162) = A_161
      | ~ v1_funct_2(C_162,A_161,B_160)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_269,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_266])).

tff(c_272,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_97,c_269])).

tff(c_273,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_272])).

tff(c_817,plain,(
    ! [A_227,B_228,D_229] :
      ( r2_hidden('#skF_5'(A_227,B_228,k9_relat_1(A_227,B_228),D_229),k1_relat_1(A_227))
      | ~ r2_hidden(D_229,k9_relat_1(A_227,B_228))
      | ~ v1_funct_1(A_227)
      | ~ v1_relat_1(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_830,plain,(
    ! [B_228,D_229] :
      ( r2_hidden('#skF_5'('#skF_9',B_228,k9_relat_1('#skF_9',B_228),D_229),'#skF_6')
      | ~ r2_hidden(D_229,k9_relat_1('#skF_9',B_228))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_817])).

tff(c_837,plain,(
    ! [B_230,D_231] :
      ( r2_hidden('#skF_5'('#skF_9',B_230,k9_relat_1('#skF_9',B_230),D_231),'#skF_6')
      | ~ r2_hidden(D_231,k9_relat_1('#skF_9',B_230)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_72,c_830])).

tff(c_884,plain,(
    ! [B_238,D_239] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',B_238,k9_relat_1('#skF_9',B_238),D_239)) != '#skF_10'
      | ~ r2_hidden('#skF_5'('#skF_9',B_238,k9_relat_1('#skF_9',B_238),D_239),'#skF_8')
      | ~ r2_hidden(D_239,k9_relat_1('#skF_9',B_238)) ) ),
    inference(resolution,[status(thm)],[c_837,c_64])).

tff(c_888,plain,(
    ! [D_54] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_54)) != '#skF_10'
      | ~ r2_hidden(D_54,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_24,c_884])).

tff(c_891,plain,(
    ! [D_54] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_54)) != '#skF_10'
      | ~ r2_hidden(D_54,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_72,c_888])).

tff(c_1008,plain,(
    ! [D_264] :
      ( D_264 != '#skF_10'
      | ~ r2_hidden(D_264,k9_relat_1('#skF_9','#skF_8'))
      | ~ r2_hidden(D_264,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1001,c_891])).

tff(c_1031,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_72,c_1008])).

tff(c_1033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1031,c_157])).

tff(c_1035,plain,(
    k1_relat_1('#skF_9') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_1034,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_1177,plain,(
    ! [C_283,A_284] :
      ( C_283 = '#skF_7'
      | ~ v1_funct_2(C_283,A_284,'#skF_7')
      | A_284 = '#skF_7'
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_284,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_1034,c_1034,c_1034,c_54])).

tff(c_1180,plain,
    ( '#skF_7' = '#skF_9'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_68,c_1177])).

tff(c_1183,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1180])).

tff(c_1184,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1183])).

tff(c_1197,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_70])).

tff(c_1195,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_9') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_97])).

tff(c_1196,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_68])).

tff(c_1042,plain,(
    ! [B_71,C_72] :
      ( k1_relset_1('#skF_7',B_71,C_72) = '#skF_7'
      | ~ v1_funct_2(C_72,'#skF_7',B_71)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1('#skF_7',B_71))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_1034,c_1034,c_1034,c_60])).

tff(c_1385,plain,(
    ! [B_310,C_311] :
      ( k1_relset_1('#skF_6',B_310,C_311) = '#skF_6'
      | ~ v1_funct_2(C_311,'#skF_6',B_310)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_310))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_1184,c_1184,c_1184,c_1042])).

tff(c_1388,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_1196,c_1385])).

tff(c_1391,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1197,c_1195,c_1388])).

tff(c_1393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1035,c_1391])).

tff(c_1394,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1183])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [B_59,A_58] :
      ( ~ r1_tarski(B_59,A_58)
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_241,plain,(
    ! [C_150,A_151,B_152] :
      ( ~ r1_tarski(C_150,k4_tarski('#skF_1'(A_151,B_152,C_150),A_151))
      | ~ r2_hidden(A_151,k9_relat_1(C_150,B_152))
      | ~ v1_relat_1(C_150) ) ),
    inference(resolution,[status(thm)],[c_185,c_44])).

tff(c_246,plain,(
    ! [A_151,B_152] :
      ( ~ r2_hidden(A_151,k9_relat_1(k1_xboole_0,B_152))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_241])).

tff(c_248,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_1039,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_248])).

tff(c_1403,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1394,c_1039])).

tff(c_1411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_1403])).

tff(c_1413,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_2643,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2634,c_1413])).

tff(c_3246,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3229,c_2643])).

tff(c_3253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_3246])).

tff(c_3254,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_3228])).

tff(c_1412,plain,(
    ! [A_151,B_152] : ~ r2_hidden(A_151,k9_relat_1(k1_xboole_0,B_152)) ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_2641,plain,(
    ! [A_151,B_152] : ~ r2_hidden(A_151,k9_relat_1('#skF_7',B_152)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2634,c_1412])).

tff(c_3270,plain,(
    ! [A_151,B_152] : ~ r2_hidden(A_151,k9_relat_1('#skF_9',B_152)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3254,c_2641])).

tff(c_3325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3270,c_157])).

tff(c_3327,plain,(
    v1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_3329,plain,(
    ! [B_544,A_545,C_546] :
      ( k1_xboole_0 = B_544
      | k1_relset_1(A_545,B_544,C_546) = A_545
      | ~ v1_funct_2(C_546,A_545,B_544)
      | ~ m1_subset_1(C_546,k1_zfmisc_1(k2_zfmisc_1(A_545,B_544))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3332,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_3329])).

tff(c_3335,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_97,c_3332])).

tff(c_3336,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_3335])).

tff(c_4131,plain,(
    ! [A_661,B_662,D_663] :
      ( r2_hidden('#skF_5'(A_661,B_662,k9_relat_1(A_661,B_662),D_663),k1_relat_1(A_661))
      | ~ r2_hidden(D_663,k9_relat_1(A_661,B_662))
      | ~ v1_funct_1(A_661)
      | ~ v1_relat_1(A_661) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4144,plain,(
    ! [B_662,D_663] :
      ( r2_hidden('#skF_5'('#skF_9',B_662,k9_relat_1('#skF_9',B_662),D_663),'#skF_6')
      | ~ r2_hidden(D_663,k9_relat_1('#skF_9',B_662))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3336,c_4131])).

tff(c_4151,plain,(
    ! [B_664,D_665] :
      ( r2_hidden('#skF_5'('#skF_9',B_664,k9_relat_1('#skF_9',B_664),D_665),'#skF_6')
      | ~ r2_hidden(D_665,k9_relat_1('#skF_9',B_664)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_72,c_4144])).

tff(c_4375,plain,(
    ! [B_680,D_681] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',B_680,k9_relat_1('#skF_9',B_680),D_681)) != '#skF_10'
      | ~ r2_hidden('#skF_5'('#skF_9',B_680,k9_relat_1('#skF_9',B_680),D_681),'#skF_8')
      | ~ r2_hidden(D_681,k9_relat_1('#skF_9',B_680)) ) ),
    inference(resolution,[status(thm)],[c_4151,c_64])).

tff(c_4383,plain,(
    ! [D_54] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_54)) != '#skF_10'
      | ~ r2_hidden(D_54,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_24,c_4375])).

tff(c_4388,plain,(
    ! [D_682] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_682)) != '#skF_10'
      | ~ r2_hidden(D_682,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_72,c_4383])).

tff(c_4392,plain,(
    ! [D_54] :
      ( D_54 != '#skF_10'
      | ~ r2_hidden(D_54,k9_relat_1('#skF_9','#skF_8'))
      | ~ r2_hidden(D_54,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_4388])).

tff(c_4395,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_72,c_4392])).

tff(c_4397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4395,c_157])).

tff(c_4398,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3335])).

tff(c_4510,plain,(
    ! [C_703,A_704] :
      ( C_703 = '#skF_7'
      | ~ v1_funct_2(C_703,A_704,'#skF_7')
      | A_704 = '#skF_7'
      | ~ m1_subset_1(C_703,k1_zfmisc_1(k2_zfmisc_1(A_704,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4398,c_4398,c_4398,c_4398,c_54])).

tff(c_4513,plain,
    ( '#skF_7' = '#skF_9'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_68,c_4510])).

tff(c_4516,plain,
    ( '#skF_7' = '#skF_9'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4513])).

tff(c_4517,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4516])).

tff(c_3328,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_4401,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4398,c_3328])).

tff(c_4526,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4517,c_4401])).

tff(c_4534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3327,c_4526])).

tff(c_4535,plain,(
    '#skF_7' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_4516])).

tff(c_4545,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4535,c_4401])).

tff(c_4553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_4545])).

tff(c_4554,plain,(
    ! [A_151,B_152] : ~ r2_hidden(A_151,k9_relat_1(k1_xboole_0,B_152)) ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_5102,plain,(
    ! [A_151,B_152] : ~ r2_hidden(A_151,k9_relat_1('#skF_7',B_152)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5093,c_4554])).

tff(c_6969,plain,(
    ! [A_151,B_152] : ~ r2_hidden(A_151,k9_relat_1('#skF_9',B_152)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6954,c_5102])).

tff(c_7012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6969,c_157])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.28/2.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.28/2.39  
% 6.28/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.28/2.40  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 6.28/2.40  
% 6.28/2.40  %Foreground sorts:
% 6.28/2.40  
% 6.28/2.40  
% 6.28/2.40  %Background operators:
% 6.28/2.40  
% 6.28/2.40  
% 6.28/2.40  %Foreground operators:
% 6.28/2.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.28/2.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.28/2.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.28/2.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.28/2.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.28/2.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.28/2.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.28/2.40  tff('#skF_7', type, '#skF_7': $i).
% 6.28/2.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.28/2.40  tff('#skF_10', type, '#skF_10': $i).
% 6.28/2.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.28/2.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.28/2.40  tff('#skF_6', type, '#skF_6': $i).
% 6.28/2.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.28/2.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.28/2.40  tff('#skF_9', type, '#skF_9': $i).
% 6.28/2.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.28/2.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.28/2.40  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.28/2.40  tff('#skF_8', type, '#skF_8': $i).
% 6.28/2.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.28/2.40  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 6.28/2.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.28/2.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.28/2.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.28/2.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.28/2.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.28/2.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.28/2.40  
% 6.56/2.42  tff(f_122, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 6.56/2.42  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.56/2.42  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 6.56/2.42  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.56/2.42  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.56/2.42  tff(f_85, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.56/2.42  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 6.56/2.42  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.56/2.42  tff(f_73, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.56/2.42  tff(c_68, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.56/2.42  tff(c_79, plain, (![C_81, A_82, B_83]: (v1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.56/2.42  tff(c_83, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_68, c_79])).
% 6.56/2.42  tff(c_72, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.56/2.42  tff(c_22, plain, (![A_16, B_39, D_54]: (k1_funct_1(A_16, '#skF_5'(A_16, B_39, k9_relat_1(A_16, B_39), D_54))=D_54 | ~r2_hidden(D_54, k9_relat_1(A_16, B_39)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.56/2.42  tff(c_24, plain, (![A_16, B_39, D_54]: (r2_hidden('#skF_5'(A_16, B_39, k9_relat_1(A_16, B_39), D_54), B_39) | ~r2_hidden(D_54, k9_relat_1(A_16, B_39)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.56/2.42  tff(c_70, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.56/2.42  tff(c_93, plain, (![A_98, B_99, C_100]: (k1_relset_1(A_98, B_99, C_100)=k1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.56/2.42  tff(c_97, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_68, c_93])).
% 6.56/2.42  tff(c_4629, plain, (![B_730, A_731, C_732]: (k1_xboole_0=B_730 | k1_relset_1(A_731, B_730, C_732)=A_731 | ~v1_funct_2(C_732, A_731, B_730) | ~m1_subset_1(C_732, k1_zfmisc_1(k2_zfmisc_1(A_731, B_730))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.56/2.42  tff(c_4632, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_4629])).
% 6.56/2.42  tff(c_4635, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_97, c_4632])).
% 6.56/2.42  tff(c_4636, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_4635])).
% 6.56/2.42  tff(c_5003, plain, (![A_756, B_757, D_758]: (r2_hidden('#skF_5'(A_756, B_757, k9_relat_1(A_756, B_757), D_758), k1_relat_1(A_756)) | ~r2_hidden(D_758, k9_relat_1(A_756, B_757)) | ~v1_funct_1(A_756) | ~v1_relat_1(A_756))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.56/2.42  tff(c_5014, plain, (![B_757, D_758]: (r2_hidden('#skF_5'('#skF_9', B_757, k9_relat_1('#skF_9', B_757), D_758), '#skF_6') | ~r2_hidden(D_758, k9_relat_1('#skF_9', B_757)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_4636, c_5003])).
% 6.56/2.42  tff(c_5020, plain, (![B_759, D_760]: (r2_hidden('#skF_5'('#skF_9', B_759, k9_relat_1('#skF_9', B_759), D_760), '#skF_6') | ~r2_hidden(D_760, k9_relat_1('#skF_9', B_759)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_72, c_5014])).
% 6.56/2.42  tff(c_64, plain, (![F_77]: (k1_funct_1('#skF_9', F_77)!='#skF_10' | ~r2_hidden(F_77, '#skF_8') | ~r2_hidden(F_77, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.56/2.42  tff(c_5046, plain, (![B_766, D_767]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', B_766, k9_relat_1('#skF_9', B_766), D_767))!='#skF_10' | ~r2_hidden('#skF_5'('#skF_9', B_766, k9_relat_1('#skF_9', B_766), D_767), '#skF_8') | ~r2_hidden(D_767, k9_relat_1('#skF_9', B_766)))), inference(resolution, [status(thm)], [c_5020, c_64])).
% 6.56/2.42  tff(c_5050, plain, (![D_54]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_54))!='#skF_10' | ~r2_hidden(D_54, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_24, c_5046])).
% 6.56/2.42  tff(c_5083, plain, (![D_776]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_776))!='#skF_10' | ~r2_hidden(D_776, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_72, c_5050])).
% 6.56/2.42  tff(c_5087, plain, (![D_54]: (D_54!='#skF_10' | ~r2_hidden(D_54, k9_relat_1('#skF_9', '#skF_8')) | ~r2_hidden(D_54, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5083])).
% 6.56/2.42  tff(c_5090, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_72, c_5087])).
% 6.56/2.42  tff(c_150, plain, (![A_122, B_123, C_124, D_125]: (k7_relset_1(A_122, B_123, C_124, D_125)=k9_relat_1(C_124, D_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.56/2.42  tff(c_153, plain, (![D_125]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_125)=k9_relat_1('#skF_9', D_125))), inference(resolution, [status(thm)], [c_68, c_150])).
% 6.56/2.42  tff(c_66, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.56/2.42  tff(c_157, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_66])).
% 6.56/2.42  tff(c_5092, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5090, c_157])).
% 6.56/2.42  tff(c_5094, plain, (k1_relat_1('#skF_9')!='#skF_6'), inference(splitRight, [status(thm)], [c_4635])).
% 6.56/2.42  tff(c_5093, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_4635])).
% 6.56/2.42  tff(c_54, plain, (![C_72, A_70]: (k1_xboole_0=C_72 | ~v1_funct_2(C_72, A_70, k1_xboole_0) | k1_xboole_0=A_70 | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.56/2.42  tff(c_6091, plain, (![C_890, A_891]: (C_890='#skF_7' | ~v1_funct_2(C_890, A_891, '#skF_7') | A_891='#skF_7' | ~m1_subset_1(C_890, k1_zfmisc_1(k2_zfmisc_1(A_891, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_5093, c_5093, c_5093, c_5093, c_54])).
% 6.56/2.42  tff(c_6094, plain, ('#skF_7'='#skF_9' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_68, c_6091])).
% 6.56/2.42  tff(c_6097, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6094])).
% 6.56/2.42  tff(c_6098, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_6097])).
% 6.56/2.42  tff(c_6137, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6098, c_70])).
% 6.56/2.42  tff(c_6135, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_9')=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6098, c_97])).
% 6.56/2.42  tff(c_6136, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_6098, c_68])).
% 6.56/2.42  tff(c_60, plain, (![B_71, C_72]: (k1_relset_1(k1_xboole_0, B_71, C_72)=k1_xboole_0 | ~v1_funct_2(C_72, k1_xboole_0, B_71) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_71))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.56/2.42  tff(c_5106, plain, (![B_71, C_72]: (k1_relset_1('#skF_7', B_71, C_72)='#skF_7' | ~v1_funct_2(C_72, '#skF_7', B_71) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_71))))), inference(demodulation, [status(thm), theory('equality')], [c_5093, c_5093, c_5093, c_5093, c_60])).
% 6.56/2.42  tff(c_6945, plain, (![B_964, C_965]: (k1_relset_1('#skF_6', B_964, C_965)='#skF_6' | ~v1_funct_2(C_965, '#skF_6', B_964) | ~m1_subset_1(C_965, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_964))))), inference(demodulation, [status(thm), theory('equality')], [c_6098, c_6098, c_6098, c_6098, c_5106])).
% 6.56/2.42  tff(c_6948, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_6136, c_6945])).
% 6.56/2.42  tff(c_6951, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6137, c_6135, c_6948])).
% 6.56/2.42  tff(c_6953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5094, c_6951])).
% 6.56/2.42  tff(c_6954, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_6097])).
% 6.56/2.42  tff(c_185, plain, (![A_138, B_139, C_140]: (r2_hidden(k4_tarski('#skF_1'(A_138, B_139, C_140), A_138), C_140) | ~r2_hidden(A_138, k9_relat_1(C_140, B_139)) | ~v1_relat_1(C_140))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.56/2.42  tff(c_216, plain, (![A_138, B_139]: (k1_funct_1('#skF_9', k4_tarski('#skF_1'(A_138, B_139, '#skF_6'), A_138))!='#skF_10' | ~r2_hidden(k4_tarski('#skF_1'(A_138, B_139, '#skF_6'), A_138), '#skF_8') | ~r2_hidden(A_138, k9_relat_1('#skF_6', B_139)) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_185, c_64])).
% 6.56/2.42  tff(c_247, plain, (~v1_relat_1('#skF_6')), inference(splitLeft, [status(thm)], [c_216])).
% 6.56/2.42  tff(c_1475, plain, (![B_331, A_332, C_333]: (k1_xboole_0=B_331 | k1_relset_1(A_332, B_331, C_333)=A_332 | ~v1_funct_2(C_333, A_332, B_331) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_332, B_331))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.56/2.42  tff(c_1478, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_1475])).
% 6.56/2.42  tff(c_1481, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_97, c_1478])).
% 6.56/2.42  tff(c_1482, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_1481])).
% 6.56/2.42  tff(c_2573, plain, (![A_449, B_450, D_451]: (r2_hidden('#skF_5'(A_449, B_450, k9_relat_1(A_449, B_450), D_451), k1_relat_1(A_449)) | ~r2_hidden(D_451, k9_relat_1(A_449, B_450)) | ~v1_funct_1(A_449) | ~v1_relat_1(A_449))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.56/2.42  tff(c_2588, plain, (![B_450, D_451]: (r2_hidden('#skF_5'('#skF_9', B_450, k9_relat_1('#skF_9', B_450), D_451), '#skF_6') | ~r2_hidden(D_451, k9_relat_1('#skF_9', B_450)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1482, c_2573])).
% 6.56/2.42  tff(c_2596, plain, (![B_452, D_453]: (r2_hidden('#skF_5'('#skF_9', B_452, k9_relat_1('#skF_9', B_452), D_453), '#skF_6') | ~r2_hidden(D_453, k9_relat_1('#skF_9', B_452)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_72, c_2588])).
% 6.56/2.42  tff(c_2616, plain, (![B_456, D_457]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', B_456, k9_relat_1('#skF_9', B_456), D_457))!='#skF_10' | ~r2_hidden('#skF_5'('#skF_9', B_456, k9_relat_1('#skF_9', B_456), D_457), '#skF_8') | ~r2_hidden(D_457, k9_relat_1('#skF_9', B_456)))), inference(resolution, [status(thm)], [c_2596, c_64])).
% 6.56/2.42  tff(c_2620, plain, (![D_54]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_54))!='#skF_10' | ~r2_hidden(D_54, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_24, c_2616])).
% 6.56/2.42  tff(c_2624, plain, (![D_458]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_458))!='#skF_10' | ~r2_hidden(D_458, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_72, c_2620])).
% 6.56/2.42  tff(c_2628, plain, (![D_54]: (D_54!='#skF_10' | ~r2_hidden(D_54, k9_relat_1('#skF_9', '#skF_8')) | ~r2_hidden(D_54, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2624])).
% 6.56/2.42  tff(c_2631, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_72, c_2628])).
% 6.56/2.42  tff(c_2633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2631, c_157])).
% 6.56/2.42  tff(c_2634, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1481])).
% 6.56/2.42  tff(c_3222, plain, (![C_538, A_539]: (C_538='#skF_7' | ~v1_funct_2(C_538, A_539, '#skF_7') | A_539='#skF_7' | ~m1_subset_1(C_538, k1_zfmisc_1(k2_zfmisc_1(A_539, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_2634, c_2634, c_2634, c_2634, c_54])).
% 6.56/2.42  tff(c_3225, plain, ('#skF_7'='#skF_9' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_68, c_3222])).
% 6.56/2.42  tff(c_3228, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_3225])).
% 6.56/2.42  tff(c_3229, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_3228])).
% 6.56/2.42  tff(c_1001, plain, (![A_262, B_263, D_264]: (k1_funct_1(A_262, '#skF_5'(A_262, B_263, k9_relat_1(A_262, B_263), D_264))=D_264 | ~r2_hidden(D_264, k9_relat_1(A_262, B_263)) | ~v1_funct_1(A_262) | ~v1_relat_1(A_262))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.56/2.42  tff(c_266, plain, (![B_160, A_161, C_162]: (k1_xboole_0=B_160 | k1_relset_1(A_161, B_160, C_162)=A_161 | ~v1_funct_2(C_162, A_161, B_160) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.56/2.42  tff(c_269, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_266])).
% 6.56/2.42  tff(c_272, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_97, c_269])).
% 6.56/2.42  tff(c_273, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_272])).
% 6.56/2.42  tff(c_817, plain, (![A_227, B_228, D_229]: (r2_hidden('#skF_5'(A_227, B_228, k9_relat_1(A_227, B_228), D_229), k1_relat_1(A_227)) | ~r2_hidden(D_229, k9_relat_1(A_227, B_228)) | ~v1_funct_1(A_227) | ~v1_relat_1(A_227))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.56/2.42  tff(c_830, plain, (![B_228, D_229]: (r2_hidden('#skF_5'('#skF_9', B_228, k9_relat_1('#skF_9', B_228), D_229), '#skF_6') | ~r2_hidden(D_229, k9_relat_1('#skF_9', B_228)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_273, c_817])).
% 6.56/2.42  tff(c_837, plain, (![B_230, D_231]: (r2_hidden('#skF_5'('#skF_9', B_230, k9_relat_1('#skF_9', B_230), D_231), '#skF_6') | ~r2_hidden(D_231, k9_relat_1('#skF_9', B_230)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_72, c_830])).
% 6.56/2.42  tff(c_884, plain, (![B_238, D_239]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', B_238, k9_relat_1('#skF_9', B_238), D_239))!='#skF_10' | ~r2_hidden('#skF_5'('#skF_9', B_238, k9_relat_1('#skF_9', B_238), D_239), '#skF_8') | ~r2_hidden(D_239, k9_relat_1('#skF_9', B_238)))), inference(resolution, [status(thm)], [c_837, c_64])).
% 6.56/2.42  tff(c_888, plain, (![D_54]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_54))!='#skF_10' | ~r2_hidden(D_54, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_24, c_884])).
% 6.56/2.42  tff(c_891, plain, (![D_54]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_54))!='#skF_10' | ~r2_hidden(D_54, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_72, c_888])).
% 6.56/2.42  tff(c_1008, plain, (![D_264]: (D_264!='#skF_10' | ~r2_hidden(D_264, k9_relat_1('#skF_9', '#skF_8')) | ~r2_hidden(D_264, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1001, c_891])).
% 6.56/2.42  tff(c_1031, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_72, c_1008])).
% 6.56/2.42  tff(c_1033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1031, c_157])).
% 6.56/2.42  tff(c_1035, plain, (k1_relat_1('#skF_9')!='#skF_6'), inference(splitRight, [status(thm)], [c_272])).
% 6.56/2.42  tff(c_1034, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_272])).
% 6.56/2.42  tff(c_1177, plain, (![C_283, A_284]: (C_283='#skF_7' | ~v1_funct_2(C_283, A_284, '#skF_7') | A_284='#skF_7' | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_284, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_1034, c_1034, c_1034, c_1034, c_54])).
% 6.56/2.42  tff(c_1180, plain, ('#skF_7'='#skF_9' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_68, c_1177])).
% 6.56/2.42  tff(c_1183, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1180])).
% 6.56/2.42  tff(c_1184, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_1183])).
% 6.56/2.42  tff(c_1197, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_70])).
% 6.56/2.42  tff(c_1195, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_9')=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_97])).
% 6.56/2.42  tff(c_1196, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_68])).
% 6.56/2.42  tff(c_1042, plain, (![B_71, C_72]: (k1_relset_1('#skF_7', B_71, C_72)='#skF_7' | ~v1_funct_2(C_72, '#skF_7', B_71) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1('#skF_7', B_71))))), inference(demodulation, [status(thm), theory('equality')], [c_1034, c_1034, c_1034, c_1034, c_60])).
% 6.56/2.42  tff(c_1385, plain, (![B_310, C_311]: (k1_relset_1('#skF_6', B_310, C_311)='#skF_6' | ~v1_funct_2(C_311, '#skF_6', B_310) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_310))))), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_1184, c_1184, c_1184, c_1042])).
% 6.56/2.42  tff(c_1388, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_1196, c_1385])).
% 6.56/2.42  tff(c_1391, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1197, c_1195, c_1388])).
% 6.56/2.42  tff(c_1393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1035, c_1391])).
% 6.56/2.42  tff(c_1394, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_1183])).
% 6.56/2.42  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.56/2.42  tff(c_44, plain, (![B_59, A_58]: (~r1_tarski(B_59, A_58) | ~r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.56/2.42  tff(c_241, plain, (![C_150, A_151, B_152]: (~r1_tarski(C_150, k4_tarski('#skF_1'(A_151, B_152, C_150), A_151)) | ~r2_hidden(A_151, k9_relat_1(C_150, B_152)) | ~v1_relat_1(C_150))), inference(resolution, [status(thm)], [c_185, c_44])).
% 6.56/2.42  tff(c_246, plain, (![A_151, B_152]: (~r2_hidden(A_151, k9_relat_1(k1_xboole_0, B_152)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_241])).
% 6.56/2.42  tff(c_248, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_246])).
% 6.56/2.42  tff(c_1039, plain, (~v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1034, c_248])).
% 6.56/2.42  tff(c_1403, plain, (~v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1394, c_1039])).
% 6.56/2.42  tff(c_1411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_1403])).
% 6.56/2.42  tff(c_1413, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_246])).
% 6.56/2.42  tff(c_2643, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2634, c_1413])).
% 6.56/2.42  tff(c_3246, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3229, c_2643])).
% 6.56/2.42  tff(c_3253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_247, c_3246])).
% 6.56/2.42  tff(c_3254, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_3228])).
% 6.56/2.42  tff(c_1412, plain, (![A_151, B_152]: (~r2_hidden(A_151, k9_relat_1(k1_xboole_0, B_152)))), inference(splitRight, [status(thm)], [c_246])).
% 6.56/2.42  tff(c_2641, plain, (![A_151, B_152]: (~r2_hidden(A_151, k9_relat_1('#skF_7', B_152)))), inference(demodulation, [status(thm), theory('equality')], [c_2634, c_1412])).
% 6.56/2.42  tff(c_3270, plain, (![A_151, B_152]: (~r2_hidden(A_151, k9_relat_1('#skF_9', B_152)))), inference(demodulation, [status(thm), theory('equality')], [c_3254, c_2641])).
% 6.56/2.42  tff(c_3325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3270, c_157])).
% 6.56/2.42  tff(c_3327, plain, (v1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_216])).
% 6.56/2.42  tff(c_3329, plain, (![B_544, A_545, C_546]: (k1_xboole_0=B_544 | k1_relset_1(A_545, B_544, C_546)=A_545 | ~v1_funct_2(C_546, A_545, B_544) | ~m1_subset_1(C_546, k1_zfmisc_1(k2_zfmisc_1(A_545, B_544))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.56/2.42  tff(c_3332, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_3329])).
% 6.56/2.42  tff(c_3335, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_97, c_3332])).
% 6.56/2.42  tff(c_3336, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_3335])).
% 6.56/2.42  tff(c_4131, plain, (![A_661, B_662, D_663]: (r2_hidden('#skF_5'(A_661, B_662, k9_relat_1(A_661, B_662), D_663), k1_relat_1(A_661)) | ~r2_hidden(D_663, k9_relat_1(A_661, B_662)) | ~v1_funct_1(A_661) | ~v1_relat_1(A_661))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.56/2.42  tff(c_4144, plain, (![B_662, D_663]: (r2_hidden('#skF_5'('#skF_9', B_662, k9_relat_1('#skF_9', B_662), D_663), '#skF_6') | ~r2_hidden(D_663, k9_relat_1('#skF_9', B_662)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_3336, c_4131])).
% 6.56/2.42  tff(c_4151, plain, (![B_664, D_665]: (r2_hidden('#skF_5'('#skF_9', B_664, k9_relat_1('#skF_9', B_664), D_665), '#skF_6') | ~r2_hidden(D_665, k9_relat_1('#skF_9', B_664)))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_72, c_4144])).
% 6.56/2.42  tff(c_4375, plain, (![B_680, D_681]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', B_680, k9_relat_1('#skF_9', B_680), D_681))!='#skF_10' | ~r2_hidden('#skF_5'('#skF_9', B_680, k9_relat_1('#skF_9', B_680), D_681), '#skF_8') | ~r2_hidden(D_681, k9_relat_1('#skF_9', B_680)))), inference(resolution, [status(thm)], [c_4151, c_64])).
% 6.56/2.42  tff(c_4383, plain, (![D_54]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_54))!='#skF_10' | ~r2_hidden(D_54, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_24, c_4375])).
% 6.56/2.42  tff(c_4388, plain, (![D_682]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_682))!='#skF_10' | ~r2_hidden(D_682, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_72, c_4383])).
% 6.56/2.42  tff(c_4392, plain, (![D_54]: (D_54!='#skF_10' | ~r2_hidden(D_54, k9_relat_1('#skF_9', '#skF_8')) | ~r2_hidden(D_54, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_4388])).
% 6.56/2.42  tff(c_4395, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_72, c_4392])).
% 6.56/2.42  tff(c_4397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4395, c_157])).
% 6.56/2.42  tff(c_4398, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_3335])).
% 6.56/2.42  tff(c_4510, plain, (![C_703, A_704]: (C_703='#skF_7' | ~v1_funct_2(C_703, A_704, '#skF_7') | A_704='#skF_7' | ~m1_subset_1(C_703, k1_zfmisc_1(k2_zfmisc_1(A_704, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_4398, c_4398, c_4398, c_4398, c_54])).
% 6.56/2.42  tff(c_4513, plain, ('#skF_7'='#skF_9' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_68, c_4510])).
% 6.56/2.42  tff(c_4516, plain, ('#skF_7'='#skF_9' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4513])).
% 6.56/2.42  tff(c_4517, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_4516])).
% 6.56/2.42  tff(c_3328, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_246])).
% 6.56/2.42  tff(c_4401, plain, (~v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4398, c_3328])).
% 6.56/2.42  tff(c_4526, plain, (~v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4517, c_4401])).
% 6.56/2.42  tff(c_4534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3327, c_4526])).
% 6.56/2.42  tff(c_4535, plain, ('#skF_7'='#skF_9'), inference(splitRight, [status(thm)], [c_4516])).
% 6.56/2.42  tff(c_4545, plain, (~v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4535, c_4401])).
% 6.56/2.42  tff(c_4553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_4545])).
% 6.56/2.42  tff(c_4554, plain, (![A_151, B_152]: (~r2_hidden(A_151, k9_relat_1(k1_xboole_0, B_152)))), inference(splitRight, [status(thm)], [c_246])).
% 6.56/2.42  tff(c_5102, plain, (![A_151, B_152]: (~r2_hidden(A_151, k9_relat_1('#skF_7', B_152)))), inference(demodulation, [status(thm), theory('equality')], [c_5093, c_4554])).
% 6.56/2.42  tff(c_6969, plain, (![A_151, B_152]: (~r2_hidden(A_151, k9_relat_1('#skF_9', B_152)))), inference(demodulation, [status(thm), theory('equality')], [c_6954, c_5102])).
% 6.56/2.42  tff(c_7012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6969, c_157])).
% 6.56/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.56/2.42  
% 6.56/2.42  Inference rules
% 6.56/2.42  ----------------------
% 6.56/2.42  #Ref     : 0
% 6.56/2.42  #Sup     : 1352
% 6.56/2.42  #Fact    : 0
% 6.56/2.42  #Define  : 0
% 6.56/2.42  #Split   : 44
% 6.56/2.42  #Chain   : 0
% 6.56/2.42  #Close   : 0
% 6.56/2.42  
% 6.56/2.42  Ordering : KBO
% 6.56/2.42  
% 6.56/2.42  Simplification rules
% 6.56/2.42  ----------------------
% 6.56/2.42  #Subsume      : 351
% 6.56/2.42  #Demod        : 694
% 6.56/2.42  #Tautology    : 111
% 6.56/2.42  #SimpNegUnit  : 24
% 6.56/2.42  #BackRed      : 295
% 6.56/2.42  
% 6.56/2.42  #Partial instantiations: 0
% 6.56/2.42  #Strategies tried      : 1
% 6.56/2.42  
% 6.56/2.42  Timing (in seconds)
% 6.56/2.42  ----------------------
% 6.56/2.42  Preprocessing        : 0.34
% 6.56/2.42  Parsing              : 0.17
% 6.56/2.42  CNF conversion       : 0.03
% 6.56/2.42  Main loop            : 1.19
% 6.56/2.42  Inferencing          : 0.42
% 6.56/2.42  Reduction            : 0.30
% 6.56/2.42  Demodulation         : 0.21
% 6.56/2.42  BG Simplification    : 0.05
% 6.56/2.42  Subsumption          : 0.31
% 6.56/2.42  Abstraction          : 0.06
% 6.56/2.43  MUC search           : 0.00
% 6.56/2.43  Cooper               : 0.00
% 6.56/2.43  Total                : 1.58
% 6.56/2.43  Index Insertion      : 0.00
% 6.56/2.43  Index Deletion       : 0.00
% 6.56/2.43  Index Matching       : 0.00
% 6.56/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
