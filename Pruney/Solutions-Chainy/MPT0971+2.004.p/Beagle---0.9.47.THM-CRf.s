%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:30 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 120 expanded)
%              Number of leaves         :   38 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 259 expanded)
%              Number of equality atoms :   27 (  63 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( r2_hidden(C,k2_relat_1(B))
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
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
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_54,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_81,plain,(
    ! [C_73,B_74,A_75] :
      ( v5_relat_1(C_73,B_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_75,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_85,plain,(
    v5_relat_1('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_81])).

tff(c_76,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_80,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_76])).

tff(c_92,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_96,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_92])).

tff(c_52,plain,(
    r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_98,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_52])).

tff(c_116,plain,(
    ! [C_86,A_87,B_88] :
      ( r2_hidden(C_86,A_87)
      | ~ r2_hidden(C_86,k2_relat_1(B_88))
      | ~ v5_relat_1(B_88,A_87)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,(
    ! [A_87] :
      ( r2_hidden('#skF_8',A_87)
      | ~ v5_relat_1('#skF_9',A_87)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_98,c_116])).

tff(c_127,plain,(
    ! [A_91] :
      ( r2_hidden('#skF_8',A_91)
      | ~ v5_relat_1('#skF_9',A_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_118])).

tff(c_131,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_85,c_127])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_131,c_2])).

tff(c_58,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_12,plain,(
    ! [A_9,C_45] :
      ( k1_funct_1(A_9,'#skF_5'(A_9,k2_relat_1(A_9),C_45)) = C_45
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_107,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_111,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_107])).

tff(c_267,plain,(
    ! [B_121,A_122,C_123] :
      ( k1_xboole_0 = B_121
      | k1_relset_1(A_122,B_121,C_123) = A_122
      | ~ v1_funct_2(C_123,A_122,B_121)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_270,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_267])).

tff(c_273,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_111,c_270])).

tff(c_274,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_14,plain,(
    ! [A_9,C_45] :
      ( r2_hidden('#skF_5'(A_9,k2_relat_1(A_9),C_45),k1_relat_1(A_9))
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_280,plain,(
    ! [C_45] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_45),'#skF_6')
      | ~ r2_hidden(C_45,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_14])).

tff(c_320,plain,(
    ! [C_126] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_126),'#skF_6')
      | ~ r2_hidden(C_126,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_58,c_280])).

tff(c_50,plain,(
    ! [E_65] :
      ( k1_funct_1('#skF_9',E_65) != '#skF_8'
      | ~ r2_hidden(E_65,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_330,plain,(
    ! [C_127] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_127)) != '#skF_8'
      | ~ r2_hidden(C_127,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_320,c_50])).

tff(c_334,plain,(
    ! [C_45] :
      ( C_45 != '#skF_8'
      | ~ r2_hidden(C_45,k2_relat_1('#skF_9'))
      | ~ r2_hidden(C_45,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_330])).

tff(c_344,plain,(
    ~ r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_58,c_334])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_98])).

tff(c_347,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_354,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_6])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.31  
% 2.23/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.32  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 2.23/1.32  
% 2.23/1.32  %Foreground sorts:
% 2.23/1.32  
% 2.23/1.32  
% 2.23/1.32  %Background operators:
% 2.23/1.32  
% 2.23/1.32  
% 2.23/1.32  %Foreground operators:
% 2.23/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.23/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.23/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.23/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.23/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.23/1.32  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.23/1.32  tff('#skF_9', type, '#skF_9': $i).
% 2.23/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.23/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.23/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.23/1.32  tff('#skF_8', type, '#skF_8': $i).
% 2.23/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.23/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.32  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.23/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.32  
% 2.23/1.33  tff(f_108, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 2.23/1.33  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.23/1.33  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.23/1.33  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.23/1.33  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (r2_hidden(C, k2_relat_1(B)) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t202_relat_1)).
% 2.23/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.23/1.33  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.23/1.33  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.23/1.33  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.23/1.33  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.23/1.33  tff(c_54, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.23/1.33  tff(c_81, plain, (![C_73, B_74, A_75]: (v5_relat_1(C_73, B_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_75, B_74))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.23/1.33  tff(c_85, plain, (v5_relat_1('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_81])).
% 2.23/1.33  tff(c_76, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.33  tff(c_80, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_54, c_76])).
% 2.23/1.33  tff(c_92, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.23/1.33  tff(c_96, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_54, c_92])).
% 2.23/1.33  tff(c_52, plain, (r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.23/1.33  tff(c_98, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_52])).
% 2.23/1.33  tff(c_116, plain, (![C_86, A_87, B_88]: (r2_hidden(C_86, A_87) | ~r2_hidden(C_86, k2_relat_1(B_88)) | ~v5_relat_1(B_88, A_87) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.23/1.33  tff(c_118, plain, (![A_87]: (r2_hidden('#skF_8', A_87) | ~v5_relat_1('#skF_9', A_87) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_98, c_116])).
% 2.23/1.33  tff(c_127, plain, (![A_91]: (r2_hidden('#skF_8', A_91) | ~v5_relat_1('#skF_9', A_91))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_118])).
% 2.23/1.33  tff(c_131, plain, (r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_85, c_127])).
% 2.23/1.33  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.33  tff(c_135, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_131, c_2])).
% 2.23/1.33  tff(c_58, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.23/1.33  tff(c_12, plain, (![A_9, C_45]: (k1_funct_1(A_9, '#skF_5'(A_9, k2_relat_1(A_9), C_45))=C_45 | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.33  tff(c_56, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.23/1.33  tff(c_107, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.33  tff(c_111, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_54, c_107])).
% 2.23/1.33  tff(c_267, plain, (![B_121, A_122, C_123]: (k1_xboole_0=B_121 | k1_relset_1(A_122, B_121, C_123)=A_122 | ~v1_funct_2(C_123, A_122, B_121) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.23/1.33  tff(c_270, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_267])).
% 2.23/1.33  tff(c_273, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_111, c_270])).
% 2.23/1.33  tff(c_274, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_273])).
% 2.23/1.33  tff(c_14, plain, (![A_9, C_45]: (r2_hidden('#skF_5'(A_9, k2_relat_1(A_9), C_45), k1_relat_1(A_9)) | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.33  tff(c_280, plain, (![C_45]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_45), '#skF_6') | ~r2_hidden(C_45, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_274, c_14])).
% 2.23/1.33  tff(c_320, plain, (![C_126]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_126), '#skF_6') | ~r2_hidden(C_126, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_58, c_280])).
% 2.23/1.33  tff(c_50, plain, (![E_65]: (k1_funct_1('#skF_9', E_65)!='#skF_8' | ~r2_hidden(E_65, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.23/1.33  tff(c_330, plain, (![C_127]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_127))!='#skF_8' | ~r2_hidden(C_127, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_320, c_50])).
% 2.23/1.33  tff(c_334, plain, (![C_45]: (C_45!='#skF_8' | ~r2_hidden(C_45, k2_relat_1('#skF_9')) | ~r2_hidden(C_45, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_330])).
% 2.23/1.33  tff(c_344, plain, (~r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_58, c_334])).
% 2.23/1.33  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_344, c_98])).
% 2.23/1.33  tff(c_347, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_273])).
% 2.23/1.33  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.33  tff(c_354, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_347, c_6])).
% 2.23/1.33  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_354])).
% 2.23/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.33  
% 2.23/1.33  Inference rules
% 2.23/1.33  ----------------------
% 2.23/1.33  #Ref     : 0
% 2.23/1.33  #Sup     : 59
% 2.23/1.33  #Fact    : 0
% 2.23/1.33  #Define  : 0
% 2.23/1.33  #Split   : 3
% 2.23/1.33  #Chain   : 0
% 2.23/1.33  #Close   : 0
% 2.23/1.33  
% 2.23/1.33  Ordering : KBO
% 2.23/1.33  
% 2.23/1.33  Simplification rules
% 2.23/1.33  ----------------------
% 2.23/1.33  #Subsume      : 9
% 2.23/1.33  #Demod        : 43
% 2.23/1.33  #Tautology    : 14
% 2.23/1.33  #SimpNegUnit  : 3
% 2.23/1.33  #BackRed      : 11
% 2.23/1.33  
% 2.23/1.33  #Partial instantiations: 0
% 2.23/1.33  #Strategies tried      : 1
% 2.23/1.33  
% 2.23/1.33  Timing (in seconds)
% 2.23/1.33  ----------------------
% 2.64/1.33  Preprocessing        : 0.32
% 2.64/1.33  Parsing              : 0.16
% 2.64/1.33  CNF conversion       : 0.03
% 2.64/1.33  Main loop            : 0.24
% 2.64/1.34  Inferencing          : 0.09
% 2.64/1.34  Reduction            : 0.07
% 2.64/1.34  Demodulation         : 0.05
% 2.64/1.34  BG Simplification    : 0.02
% 2.64/1.34  Subsumption          : 0.04
% 2.64/1.34  Abstraction          : 0.01
% 2.64/1.34  MUC search           : 0.00
% 2.64/1.34  Cooper               : 0.00
% 2.64/1.34  Total                : 0.59
% 2.64/1.34  Index Insertion      : 0.00
% 2.64/1.34  Index Deletion       : 0.00
% 2.64/1.34  Index Matching       : 0.00
% 2.64/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
