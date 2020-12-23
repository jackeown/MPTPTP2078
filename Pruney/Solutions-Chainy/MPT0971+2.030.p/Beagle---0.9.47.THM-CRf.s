%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:33 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 130 expanded)
%              Number of leaves         :   37 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  117 ( 281 expanded)
%              Number of equality atoms :   27 (  66 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

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

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
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

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_54,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_91,plain,(
    ! [A_79,B_80,C_81] :
      ( k2_relset_1(A_79,B_80,C_81) = k2_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_95,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_91])).

tff(c_52,plain,(
    r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ~ v1_xboole_0(k2_relset_1('#skF_6','#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_96,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_64])).

tff(c_141,plain,(
    ! [A_92,B_93,C_94] :
      ( m1_subset_1(k2_relset_1(A_92,B_93,C_94),k1_zfmisc_1(B_93))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_162,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_141])).

tff(c_169,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_162])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [C_76,A_77,B_78] :
      ( r2_hidden(C_76,A_77)
      | ~ r2_hidden(C_76,B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_111,plain,(
    ! [A_83,A_84] :
      ( r2_hidden('#skF_1'(A_83),A_84)
      | ~ m1_subset_1(A_83,k1_zfmisc_1(A_84))
      | v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_4,c_84])).

tff(c_123,plain,(
    ! [A_84,A_83] :
      ( ~ v1_xboole_0(A_84)
      | ~ m1_subset_1(A_83,k1_zfmisc_1(A_84))
      | v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_111,c_2])).

tff(c_172,plain,
    ( ~ v1_xboole_0('#skF_7')
    | v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_169,c_123])).

tff(c_181,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_172])).

tff(c_12,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_77,plain,(
    ! [B_74,A_75] :
      ( v1_relat_1(B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_54,c_77])).

tff(c_83,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_80])).

tff(c_58,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_16,plain,(
    ! [A_14,C_50] :
      ( k1_funct_1(A_14,'#skF_5'(A_14,k2_relat_1(A_14),C_50)) = C_50
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_56,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_130,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_134,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_130])).

tff(c_365,plain,(
    ! [B_138,A_139,C_140] :
      ( k1_xboole_0 = B_138
      | k1_relset_1(A_139,B_138,C_140) = A_139
      | ~ v1_funct_2(C_140,A_139,B_138)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_372,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_365])).

tff(c_376,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_134,c_372])).

tff(c_377,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_376])).

tff(c_18,plain,(
    ! [A_14,C_50] :
      ( r2_hidden('#skF_5'(A_14,k2_relat_1(A_14),C_50),k1_relat_1(A_14))
      | ~ r2_hidden(C_50,k2_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_383,plain,(
    ! [C_50] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_50),'#skF_6')
      | ~ r2_hidden(C_50,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_18])).

tff(c_403,plain,(
    ! [C_141] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_141),'#skF_6')
      | ~ r2_hidden(C_141,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_58,c_383])).

tff(c_50,plain,(
    ! [E_67] :
      ( k1_funct_1('#skF_9',E_67) != '#skF_8'
      | ~ r2_hidden(E_67,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_415,plain,(
    ! [C_142] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_142)) != '#skF_8'
      | ~ r2_hidden(C_142,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_403,c_50])).

tff(c_419,plain,(
    ! [C_50] :
      ( C_50 != '#skF_8'
      | ~ r2_hidden(C_50,k2_relat_1('#skF_9'))
      | ~ r2_hidden(C_50,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_415])).

tff(c_458,plain,(
    ~ r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_58,c_419])).

tff(c_97,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_52])).

tff(c_460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_97])).

tff(c_461,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_469,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_6])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_181,c_469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:56:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.39  
% 2.61/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.39  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 2.61/1.39  
% 2.61/1.39  %Foreground sorts:
% 2.61/1.39  
% 2.61/1.39  
% 2.61/1.39  %Background operators:
% 2.61/1.39  
% 2.61/1.39  
% 2.61/1.39  %Foreground operators:
% 2.61/1.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.61/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.61/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.61/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.61/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.61/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.61/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.61/1.39  tff('#skF_9', type, '#skF_9': $i).
% 2.61/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.61/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.61/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.61/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.61/1.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.61/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.39  
% 2.83/1.41  tff(f_109, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 2.83/1.41  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.83/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.83/1.41  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.83/1.41  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 2.83/1.41  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.83/1.41  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.83/1.41  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.83/1.41  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.83/1.41  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.83/1.41  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.83/1.41  tff(c_54, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.83/1.41  tff(c_91, plain, (![A_79, B_80, C_81]: (k2_relset_1(A_79, B_80, C_81)=k2_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.83/1.41  tff(c_95, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_54, c_91])).
% 2.83/1.41  tff(c_52, plain, (r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.83/1.41  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.41  tff(c_64, plain, (~v1_xboole_0(k2_relset_1('#skF_6', '#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_52, c_2])).
% 2.83/1.41  tff(c_96, plain, (~v1_xboole_0(k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_64])).
% 2.83/1.41  tff(c_141, plain, (![A_92, B_93, C_94]: (m1_subset_1(k2_relset_1(A_92, B_93, C_94), k1_zfmisc_1(B_93)) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.83/1.41  tff(c_162, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_95, c_141])).
% 2.83/1.41  tff(c_169, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_162])).
% 2.83/1.41  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.83/1.41  tff(c_84, plain, (![C_76, A_77, B_78]: (r2_hidden(C_76, A_77) | ~r2_hidden(C_76, B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.83/1.41  tff(c_111, plain, (![A_83, A_84]: (r2_hidden('#skF_1'(A_83), A_84) | ~m1_subset_1(A_83, k1_zfmisc_1(A_84)) | v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_4, c_84])).
% 2.83/1.41  tff(c_123, plain, (![A_84, A_83]: (~v1_xboole_0(A_84) | ~m1_subset_1(A_83, k1_zfmisc_1(A_84)) | v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_111, c_2])).
% 2.83/1.41  tff(c_172, plain, (~v1_xboole_0('#skF_7') | v1_xboole_0(k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_169, c_123])).
% 2.83/1.41  tff(c_181, plain, (~v1_xboole_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_96, c_172])).
% 2.83/1.41  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.83/1.41  tff(c_77, plain, (![B_74, A_75]: (v1_relat_1(B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.83/1.41  tff(c_80, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_54, c_77])).
% 2.83/1.41  tff(c_83, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_80])).
% 2.83/1.41  tff(c_58, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.83/1.41  tff(c_16, plain, (![A_14, C_50]: (k1_funct_1(A_14, '#skF_5'(A_14, k2_relat_1(A_14), C_50))=C_50 | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.83/1.41  tff(c_56, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.83/1.41  tff(c_130, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.83/1.41  tff(c_134, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_54, c_130])).
% 2.83/1.41  tff(c_365, plain, (![B_138, A_139, C_140]: (k1_xboole_0=B_138 | k1_relset_1(A_139, B_138, C_140)=A_139 | ~v1_funct_2(C_140, A_139, B_138) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.83/1.41  tff(c_372, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_365])).
% 2.83/1.41  tff(c_376, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_134, c_372])).
% 2.83/1.41  tff(c_377, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_376])).
% 2.83/1.41  tff(c_18, plain, (![A_14, C_50]: (r2_hidden('#skF_5'(A_14, k2_relat_1(A_14), C_50), k1_relat_1(A_14)) | ~r2_hidden(C_50, k2_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.83/1.41  tff(c_383, plain, (![C_50]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_50), '#skF_6') | ~r2_hidden(C_50, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_377, c_18])).
% 2.83/1.41  tff(c_403, plain, (![C_141]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_141), '#skF_6') | ~r2_hidden(C_141, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_58, c_383])).
% 2.83/1.41  tff(c_50, plain, (![E_67]: (k1_funct_1('#skF_9', E_67)!='#skF_8' | ~r2_hidden(E_67, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.83/1.41  tff(c_415, plain, (![C_142]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_142))!='#skF_8' | ~r2_hidden(C_142, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_403, c_50])).
% 2.83/1.41  tff(c_419, plain, (![C_50]: (C_50!='#skF_8' | ~r2_hidden(C_50, k2_relat_1('#skF_9')) | ~r2_hidden(C_50, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_415])).
% 2.83/1.41  tff(c_458, plain, (~r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_58, c_419])).
% 2.83/1.41  tff(c_97, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_52])).
% 2.83/1.41  tff(c_460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_458, c_97])).
% 2.83/1.41  tff(c_461, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_376])).
% 2.83/1.41  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.41  tff(c_469, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_461, c_6])).
% 2.83/1.41  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_181, c_469])).
% 2.83/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.41  
% 2.83/1.41  Inference rules
% 2.83/1.41  ----------------------
% 2.83/1.41  #Ref     : 0
% 2.83/1.41  #Sup     : 84
% 2.83/1.41  #Fact    : 0
% 2.83/1.41  #Define  : 0
% 2.83/1.41  #Split   : 4
% 2.83/1.41  #Chain   : 0
% 2.83/1.41  #Close   : 0
% 2.83/1.41  
% 2.83/1.41  Ordering : KBO
% 2.83/1.41  
% 2.83/1.41  Simplification rules
% 2.83/1.41  ----------------------
% 2.83/1.41  #Subsume      : 12
% 2.83/1.41  #Demod        : 47
% 2.83/1.41  #Tautology    : 14
% 2.83/1.41  #SimpNegUnit  : 4
% 2.83/1.41  #BackRed      : 12
% 2.83/1.41  
% 2.83/1.41  #Partial instantiations: 0
% 2.83/1.41  #Strategies tried      : 1
% 2.83/1.41  
% 2.83/1.41  Timing (in seconds)
% 2.83/1.41  ----------------------
% 2.83/1.41  Preprocessing        : 0.34
% 2.83/1.41  Parsing              : 0.18
% 2.83/1.41  CNF conversion       : 0.03
% 2.83/1.41  Main loop            : 0.29
% 2.83/1.41  Inferencing          : 0.10
% 2.83/1.41  Reduction            : 0.08
% 2.83/1.41  Demodulation         : 0.06
% 2.83/1.41  BG Simplification    : 0.02
% 2.83/1.41  Subsumption          : 0.06
% 2.83/1.41  Abstraction          : 0.02
% 2.83/1.41  MUC search           : 0.00
% 2.83/1.41  Cooper               : 0.00
% 2.83/1.41  Total                : 0.66
% 2.83/1.41  Index Insertion      : 0.00
% 2.83/1.41  Index Deletion       : 0.00
% 2.83/1.41  Index Matching       : 0.00
% 2.83/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
