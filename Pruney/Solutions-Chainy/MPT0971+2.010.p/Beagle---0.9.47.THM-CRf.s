%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:30 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 124 expanded)
%              Number of leaves         :   36 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 269 expanded)
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

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
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

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
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

tff(c_52,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_99,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_103,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_99])).

tff(c_50,plain,(
    r2_hidden('#skF_8',k2_relset_1('#skF_6','#skF_7','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ~ v1_xboole_0(k2_relset_1('#skF_6','#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_104,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_61])).

tff(c_136,plain,(
    ! [A_89,B_90,C_91] :
      ( m1_subset_1(k2_relset_1(A_89,B_90,C_91),k1_zfmisc_1(B_90))
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_158,plain,
    ( m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_136])).

tff(c_165,plain,(
    m1_subset_1(k2_relat_1('#skF_9'),k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_158])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [C_73,A_74,B_75] :
      ( r2_hidden(C_73,A_74)
      | ~ r2_hidden(C_73,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_86,plain,(
    ! [A_76,A_77] :
      ( r2_hidden('#skF_1'(A_76),A_77)
      | ~ m1_subset_1(A_76,k1_zfmisc_1(A_77))
      | v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_4,c_79])).

tff(c_98,plain,(
    ! [A_77,A_76] :
      ( ~ v1_xboole_0(A_77)
      | ~ m1_subset_1(A_76,k1_zfmisc_1(A_77))
      | v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_86,c_2])).

tff(c_174,plain,
    ( ~ v1_xboole_0('#skF_7')
    | v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_165,c_98])).

tff(c_180,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_174])).

tff(c_74,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_78,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_74])).

tff(c_56,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_12,plain,(
    ! [A_9,C_45] :
      ( k1_funct_1(A_9,'#skF_5'(A_9,k2_relat_1(A_9),C_45)) = C_45
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_54,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_126,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_130,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_52,c_126])).

tff(c_341,plain,(
    ! [B_136,A_137,C_138] :
      ( k1_xboole_0 = B_136
      | k1_relset_1(A_137,B_136,C_138) = A_137
      | ~ v1_funct_2(C_138,A_137,B_136)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_137,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_348,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_341])).

tff(c_352,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_130,c_348])).

tff(c_353,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_14,plain,(
    ! [A_9,C_45] :
      ( r2_hidden('#skF_5'(A_9,k2_relat_1(A_9),C_45),k1_relat_1(A_9))
      | ~ r2_hidden(C_45,k2_relat_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_359,plain,(
    ! [C_45] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_45),'#skF_6')
      | ~ r2_hidden(C_45,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_14])).

tff(c_379,plain,(
    ! [C_139] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_139),'#skF_6')
      | ~ r2_hidden(C_139,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_359])).

tff(c_48,plain,(
    ! [E_65] :
      ( k1_funct_1('#skF_9',E_65) != '#skF_8'
      | ~ r2_hidden(E_65,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_391,plain,(
    ! [C_140] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_140)) != '#skF_8'
      | ~ r2_hidden(C_140,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_379,c_48])).

tff(c_395,plain,(
    ! [C_45] :
      ( C_45 != '#skF_8'
      | ~ r2_hidden(C_45,k2_relat_1('#skF_9'))
      | ~ r2_hidden(C_45,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_391])).

tff(c_398,plain,(
    ~ r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_56,c_395])).

tff(c_105,plain,(
    r2_hidden('#skF_8',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_50])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_398,c_105])).

tff(c_401,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_408,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_6])).

tff(c_410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_408])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:44:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.35  
% 2.74/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.35  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 2.74/1.35  
% 2.74/1.35  %Foreground sorts:
% 2.74/1.35  
% 2.74/1.35  
% 2.74/1.35  %Background operators:
% 2.74/1.35  
% 2.74/1.35  
% 2.74/1.35  %Foreground operators:
% 2.74/1.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.74/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.74/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.74/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.74/1.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.74/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.74/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.35  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.74/1.35  tff('#skF_9', type, '#skF_9': $i).
% 2.74/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.74/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.74/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.74/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.74/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.74/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.74/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.35  
% 2.74/1.36  tff(f_104, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_funct_2)).
% 2.74/1.36  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.74/1.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.74/1.36  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.74/1.36  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.74/1.36  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.74/1.36  tff(f_54, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 2.74/1.36  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.74/1.36  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.74/1.36  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.74/1.36  tff(c_52, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.74/1.36  tff(c_99, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.74/1.36  tff(c_103, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_99])).
% 2.74/1.36  tff(c_50, plain, (r2_hidden('#skF_8', k2_relset_1('#skF_6', '#skF_7', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.74/1.36  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.36  tff(c_61, plain, (~v1_xboole_0(k2_relset_1('#skF_6', '#skF_7', '#skF_9'))), inference(resolution, [status(thm)], [c_50, c_2])).
% 2.74/1.36  tff(c_104, plain, (~v1_xboole_0(k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_61])).
% 2.74/1.36  tff(c_136, plain, (![A_89, B_90, C_91]: (m1_subset_1(k2_relset_1(A_89, B_90, C_91), k1_zfmisc_1(B_90)) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.74/1.36  tff(c_158, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_103, c_136])).
% 2.74/1.36  tff(c_165, plain, (m1_subset_1(k2_relat_1('#skF_9'), k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_158])).
% 2.74/1.36  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.36  tff(c_79, plain, (![C_73, A_74, B_75]: (r2_hidden(C_73, A_74) | ~r2_hidden(C_73, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.36  tff(c_86, plain, (![A_76, A_77]: (r2_hidden('#skF_1'(A_76), A_77) | ~m1_subset_1(A_76, k1_zfmisc_1(A_77)) | v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_4, c_79])).
% 2.74/1.36  tff(c_98, plain, (![A_77, A_76]: (~v1_xboole_0(A_77) | ~m1_subset_1(A_76, k1_zfmisc_1(A_77)) | v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_86, c_2])).
% 2.74/1.36  tff(c_174, plain, (~v1_xboole_0('#skF_7') | v1_xboole_0(k2_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_165, c_98])).
% 2.74/1.36  tff(c_180, plain, (~v1_xboole_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_104, c_174])).
% 2.74/1.36  tff(c_74, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.74/1.36  tff(c_78, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_74])).
% 2.74/1.36  tff(c_56, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.74/1.36  tff(c_12, plain, (![A_9, C_45]: (k1_funct_1(A_9, '#skF_5'(A_9, k2_relat_1(A_9), C_45))=C_45 | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.74/1.36  tff(c_54, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.74/1.36  tff(c_126, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.74/1.36  tff(c_130, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_52, c_126])).
% 2.74/1.36  tff(c_341, plain, (![B_136, A_137, C_138]: (k1_xboole_0=B_136 | k1_relset_1(A_137, B_136, C_138)=A_137 | ~v1_funct_2(C_138, A_137, B_136) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_137, B_136))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.74/1.36  tff(c_348, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_52, c_341])).
% 2.74/1.36  tff(c_352, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_130, c_348])).
% 2.74/1.36  tff(c_353, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_352])).
% 2.74/1.36  tff(c_14, plain, (![A_9, C_45]: (r2_hidden('#skF_5'(A_9, k2_relat_1(A_9), C_45), k1_relat_1(A_9)) | ~r2_hidden(C_45, k2_relat_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.74/1.36  tff(c_359, plain, (![C_45]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_45), '#skF_6') | ~r2_hidden(C_45, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_353, c_14])).
% 2.74/1.36  tff(c_379, plain, (![C_139]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_139), '#skF_6') | ~r2_hidden(C_139, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_56, c_359])).
% 2.74/1.36  tff(c_48, plain, (![E_65]: (k1_funct_1('#skF_9', E_65)!='#skF_8' | ~r2_hidden(E_65, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.74/1.36  tff(c_391, plain, (![C_140]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_140))!='#skF_8' | ~r2_hidden(C_140, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_379, c_48])).
% 2.74/1.36  tff(c_395, plain, (![C_45]: (C_45!='#skF_8' | ~r2_hidden(C_45, k2_relat_1('#skF_9')) | ~r2_hidden(C_45, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_391])).
% 2.74/1.36  tff(c_398, plain, (~r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_56, c_395])).
% 2.74/1.36  tff(c_105, plain, (r2_hidden('#skF_8', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_50])).
% 2.74/1.36  tff(c_400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_398, c_105])).
% 2.74/1.36  tff(c_401, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_352])).
% 2.74/1.36  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.36  tff(c_408, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_401, c_6])).
% 2.74/1.36  tff(c_410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_180, c_408])).
% 2.74/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.36  
% 2.74/1.36  Inference rules
% 2.74/1.36  ----------------------
% 2.74/1.36  #Ref     : 0
% 2.74/1.36  #Sup     : 72
% 2.74/1.36  #Fact    : 0
% 2.74/1.36  #Define  : 0
% 2.74/1.36  #Split   : 3
% 2.74/1.36  #Chain   : 0
% 2.74/1.36  #Close   : 0
% 2.74/1.36  
% 2.74/1.36  Ordering : KBO
% 2.74/1.36  
% 2.74/1.36  Simplification rules
% 2.74/1.36  ----------------------
% 2.84/1.36  #Subsume      : 11
% 2.84/1.36  #Demod        : 40
% 2.84/1.37  #Tautology    : 13
% 2.84/1.37  #SimpNegUnit  : 4
% 2.84/1.37  #BackRed      : 11
% 2.84/1.37  
% 2.84/1.37  #Partial instantiations: 0
% 2.84/1.37  #Strategies tried      : 1
% 2.84/1.37  
% 2.84/1.37  Timing (in seconds)
% 2.84/1.37  ----------------------
% 2.84/1.37  Preprocessing        : 0.34
% 2.84/1.37  Parsing              : 0.18
% 2.84/1.37  CNF conversion       : 0.03
% 2.84/1.37  Main loop            : 0.27
% 2.84/1.37  Inferencing          : 0.10
% 2.84/1.37  Reduction            : 0.08
% 2.84/1.37  Demodulation         : 0.05
% 2.84/1.37  BG Simplification    : 0.02
% 2.84/1.37  Subsumption          : 0.06
% 2.84/1.37  Abstraction          : 0.02
% 2.84/1.37  MUC search           : 0.00
% 2.84/1.37  Cooper               : 0.00
% 2.84/1.37  Total                : 0.65
% 2.84/1.37  Index Insertion      : 0.00
% 2.84/1.37  Index Deletion       : 0.00
% 2.84/1.37  Index Matching       : 0.00
% 2.84/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
