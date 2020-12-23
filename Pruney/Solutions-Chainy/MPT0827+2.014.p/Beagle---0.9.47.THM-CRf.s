%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:16 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 111 expanded)
%              Number of leaves         :   35 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  116 ( 178 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(C),D)
         => ( r1_tarski(C,k1_relset_1(A,B,D))
            & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2076,plain,(
    ! [A_203,B_204,C_205] :
      ( k2_relset_1(A_203,B_204,C_205) = k2_relat_1(C_205)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2085,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_2076])).

tff(c_22,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_101,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_107,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_101])).

tff(c_111,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_107])).

tff(c_24,plain,(
    ! [A_19] :
      ( r1_tarski(A_19,k2_zfmisc_1(k1_relat_1(A_19),k2_relat_1(A_19)))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_69,plain,(
    ! [A_39,B_40] :
      ( k2_xboole_0(A_39,B_40) = B_40
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    k2_xboole_0(k6_relat_1('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_69])).

tff(c_148,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(A_51,C_52)
      | ~ r1_tarski(k2_xboole_0(A_51,B_53),C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_154,plain,(
    ! [C_52] :
      ( r1_tarski(k6_relat_1('#skF_3'),C_52)
      | ~ r1_tarski('#skF_4',C_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_148])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_414,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_458,plain,(
    ! [A_82,A_83,B_84] :
      ( v4_relat_1(A_82,A_83)
      | ~ r1_tarski(A_82,k2_zfmisc_1(A_83,B_84)) ) ),
    inference(resolution,[status(thm)],[c_10,c_414])).

tff(c_819,plain,(
    ! [A_109,B_110] :
      ( v4_relat_1(k6_relat_1('#skF_3'),A_109)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_109,B_110)) ) ),
    inference(resolution,[status(thm)],[c_154,c_458])).

tff(c_822,plain,
    ( v4_relat_1(k6_relat_1('#skF_3'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_819])).

tff(c_827,plain,(
    v4_relat_1(k6_relat_1('#skF_3'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_822])).

tff(c_30,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_597,plain,(
    ! [B_97,A_98] :
      ( r1_tarski(k1_relat_1(B_97),A_98)
      | ~ v4_relat_1(B_97,A_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_614,plain,(
    ! [A_20,A_98] :
      ( r1_tarski(A_20,A_98)
      | ~ v4_relat_1(k6_relat_1(A_20),A_98)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_597])).

tff(c_620,plain,(
    ! [A_20,A_98] :
      ( r1_tarski(A_20,A_98)
      | ~ v4_relat_1(k6_relat_1(A_20),A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_614])).

tff(c_833,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_827,c_620])).

tff(c_1001,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1010,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1001])).

tff(c_42,plain,
    ( ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_78,plain,(
    ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_1012,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_78])).

tff(c_1015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_1012])).

tff(c_1016,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2087,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2085,c_1016])).

tff(c_1066,plain,(
    ! [B_132,A_133] :
      ( v1_relat_1(B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_133))
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1072,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_1066])).

tff(c_1076,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1072])).

tff(c_1044,plain,(
    ! [A_126,C_127,B_128] :
      ( r1_tarski(A_126,C_127)
      | ~ r1_tarski(k2_xboole_0(A_126,B_128),C_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1047,plain,(
    ! [C_127] :
      ( r1_tarski(k6_relat_1('#skF_3'),C_127)
      | ~ r1_tarski('#skF_4',C_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_1044])).

tff(c_1832,plain,(
    ! [C_188,B_189,A_190] :
      ( v5_relat_1(C_188,B_189)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_190,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2159,plain,(
    ! [A_210,B_211,A_212] :
      ( v5_relat_1(A_210,B_211)
      | ~ r1_tarski(A_210,k2_zfmisc_1(A_212,B_211)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1832])).

tff(c_2244,plain,(
    ! [B_215,A_216] :
      ( v5_relat_1(k6_relat_1('#skF_3'),B_215)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_216,B_215)) ) ),
    inference(resolution,[status(thm)],[c_1047,c_2159])).

tff(c_2247,plain,
    ( v5_relat_1(k6_relat_1('#skF_3'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_2244])).

tff(c_2252,plain,(
    v5_relat_1(k6_relat_1('#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1076,c_2247])).

tff(c_28,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1199,plain,(
    ! [B_142,A_143] :
      ( r1_tarski(k2_relat_1(B_142),A_143)
      | ~ v5_relat_1(B_142,A_143)
      | ~ v1_relat_1(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1208,plain,(
    ! [A_20,A_143] :
      ( r1_tarski(A_20,A_143)
      | ~ v5_relat_1(k6_relat_1(A_20),A_143)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1199])).

tff(c_1212,plain,(
    ! [A_20,A_143] :
      ( r1_tarski(A_20,A_143)
      | ~ v5_relat_1(k6_relat_1(A_20),A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1208])).

tff(c_2286,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2252,c_1212])).

tff(c_2290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2087,c_2286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.68  
% 3.81/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.68  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.81/1.68  
% 3.81/1.68  %Foreground sorts:
% 3.81/1.68  
% 3.81/1.68  
% 3.81/1.68  %Background operators:
% 3.81/1.68  
% 3.81/1.68  
% 3.81/1.68  %Foreground operators:
% 3.81/1.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.81/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.81/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.81/1.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.81/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.81/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.81/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.81/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.81/1.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.81/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.81/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.81/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.81/1.68  tff('#skF_4', type, '#skF_4': $i).
% 3.81/1.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.81/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.81/1.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.81/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.81/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.81/1.68  
% 3.81/1.70  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 3.81/1.70  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.81/1.70  tff(f_60, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.81/1.70  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.81/1.70  tff(f_64, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.81/1.70  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.81/1.70  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.81/1.70  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.81/1.70  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.81/1.70  tff(f_72, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.81/1.70  tff(f_68, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.81/1.70  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.81/1.70  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.81/1.70  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.81/1.70  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.81/1.70  tff(c_2076, plain, (![A_203, B_204, C_205]: (k2_relset_1(A_203, B_204, C_205)=k2_relat_1(C_205) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.81/1.70  tff(c_2085, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_2076])).
% 3.81/1.70  tff(c_22, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.81/1.70  tff(c_101, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.81/1.70  tff(c_107, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_101])).
% 3.81/1.70  tff(c_111, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_107])).
% 3.81/1.70  tff(c_24, plain, (![A_19]: (r1_tarski(A_19, k2_zfmisc_1(k1_relat_1(A_19), k2_relat_1(A_19))) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.81/1.70  tff(c_44, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.81/1.70  tff(c_69, plain, (![A_39, B_40]: (k2_xboole_0(A_39, B_40)=B_40 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.81/1.70  tff(c_77, plain, (k2_xboole_0(k6_relat_1('#skF_3'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_44, c_69])).
% 3.81/1.70  tff(c_148, plain, (![A_51, C_52, B_53]: (r1_tarski(A_51, C_52) | ~r1_tarski(k2_xboole_0(A_51, B_53), C_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.81/1.70  tff(c_154, plain, (![C_52]: (r1_tarski(k6_relat_1('#skF_3'), C_52) | ~r1_tarski('#skF_4', C_52))), inference(superposition, [status(thm), theory('equality')], [c_77, c_148])).
% 3.81/1.70  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.81/1.70  tff(c_414, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.81/1.70  tff(c_458, plain, (![A_82, A_83, B_84]: (v4_relat_1(A_82, A_83) | ~r1_tarski(A_82, k2_zfmisc_1(A_83, B_84)))), inference(resolution, [status(thm)], [c_10, c_414])).
% 3.81/1.70  tff(c_819, plain, (![A_109, B_110]: (v4_relat_1(k6_relat_1('#skF_3'), A_109) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_109, B_110)))), inference(resolution, [status(thm)], [c_154, c_458])).
% 3.81/1.70  tff(c_822, plain, (v4_relat_1(k6_relat_1('#skF_3'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_819])).
% 3.81/1.70  tff(c_827, plain, (v4_relat_1(k6_relat_1('#skF_3'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_822])).
% 3.81/1.70  tff(c_30, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.81/1.70  tff(c_26, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.81/1.70  tff(c_597, plain, (![B_97, A_98]: (r1_tarski(k1_relat_1(B_97), A_98) | ~v4_relat_1(B_97, A_98) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.81/1.70  tff(c_614, plain, (![A_20, A_98]: (r1_tarski(A_20, A_98) | ~v4_relat_1(k6_relat_1(A_20), A_98) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_597])).
% 3.81/1.70  tff(c_620, plain, (![A_20, A_98]: (r1_tarski(A_20, A_98) | ~v4_relat_1(k6_relat_1(A_20), A_98))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_614])).
% 3.81/1.70  tff(c_833, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_827, c_620])).
% 3.81/1.70  tff(c_1001, plain, (![A_119, B_120, C_121]: (k1_relset_1(A_119, B_120, C_121)=k1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.81/1.70  tff(c_1010, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1001])).
% 3.81/1.70  tff(c_42, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.81/1.70  tff(c_78, plain, (~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_42])).
% 3.81/1.70  tff(c_1012, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_78])).
% 3.81/1.70  tff(c_1015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_833, c_1012])).
% 3.81/1.70  tff(c_1016, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_42])).
% 3.81/1.70  tff(c_2087, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2085, c_1016])).
% 3.81/1.70  tff(c_1066, plain, (![B_132, A_133]: (v1_relat_1(B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(A_133)) | ~v1_relat_1(A_133))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.81/1.70  tff(c_1072, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_1066])).
% 3.81/1.70  tff(c_1076, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1072])).
% 3.81/1.70  tff(c_1044, plain, (![A_126, C_127, B_128]: (r1_tarski(A_126, C_127) | ~r1_tarski(k2_xboole_0(A_126, B_128), C_127))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.81/1.70  tff(c_1047, plain, (![C_127]: (r1_tarski(k6_relat_1('#skF_3'), C_127) | ~r1_tarski('#skF_4', C_127))), inference(superposition, [status(thm), theory('equality')], [c_77, c_1044])).
% 3.81/1.70  tff(c_1832, plain, (![C_188, B_189, A_190]: (v5_relat_1(C_188, B_189) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_190, B_189))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.81/1.70  tff(c_2159, plain, (![A_210, B_211, A_212]: (v5_relat_1(A_210, B_211) | ~r1_tarski(A_210, k2_zfmisc_1(A_212, B_211)))), inference(resolution, [status(thm)], [c_10, c_1832])).
% 3.81/1.70  tff(c_2244, plain, (![B_215, A_216]: (v5_relat_1(k6_relat_1('#skF_3'), B_215) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_216, B_215)))), inference(resolution, [status(thm)], [c_1047, c_2159])).
% 3.81/1.70  tff(c_2247, plain, (v5_relat_1(k6_relat_1('#skF_3'), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_2244])).
% 3.81/1.70  tff(c_2252, plain, (v5_relat_1(k6_relat_1('#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1076, c_2247])).
% 3.81/1.70  tff(c_28, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.81/1.70  tff(c_1199, plain, (![B_142, A_143]: (r1_tarski(k2_relat_1(B_142), A_143) | ~v5_relat_1(B_142, A_143) | ~v1_relat_1(B_142))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.81/1.70  tff(c_1208, plain, (![A_20, A_143]: (r1_tarski(A_20, A_143) | ~v5_relat_1(k6_relat_1(A_20), A_143) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1199])).
% 3.81/1.70  tff(c_1212, plain, (![A_20, A_143]: (r1_tarski(A_20, A_143) | ~v5_relat_1(k6_relat_1(A_20), A_143))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1208])).
% 3.81/1.70  tff(c_2286, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2252, c_1212])).
% 3.81/1.70  tff(c_2290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2087, c_2286])).
% 3.81/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.70  
% 3.81/1.70  Inference rules
% 3.81/1.70  ----------------------
% 3.81/1.70  #Ref     : 0
% 3.81/1.70  #Sup     : 495
% 3.81/1.70  #Fact    : 0
% 3.81/1.70  #Define  : 0
% 3.81/1.70  #Split   : 11
% 3.81/1.70  #Chain   : 0
% 3.81/1.70  #Close   : 0
% 3.81/1.70  
% 3.81/1.70  Ordering : KBO
% 3.81/1.70  
% 3.81/1.70  Simplification rules
% 3.81/1.70  ----------------------
% 3.81/1.70  #Subsume      : 53
% 3.81/1.70  #Demod        : 254
% 3.81/1.70  #Tautology    : 232
% 3.81/1.70  #SimpNegUnit  : 1
% 3.81/1.70  #BackRed      : 10
% 3.81/1.70  
% 3.81/1.70  #Partial instantiations: 0
% 3.81/1.70  #Strategies tried      : 1
% 3.81/1.70  
% 3.81/1.70  Timing (in seconds)
% 3.81/1.70  ----------------------
% 3.81/1.70  Preprocessing        : 0.30
% 3.81/1.70  Parsing              : 0.16
% 3.81/1.70  CNF conversion       : 0.02
% 3.81/1.70  Main loop            : 0.57
% 3.81/1.70  Inferencing          : 0.21
% 3.81/1.70  Reduction            : 0.20
% 3.81/1.70  Demodulation         : 0.14
% 3.81/1.70  BG Simplification    : 0.02
% 3.81/1.70  Subsumption          : 0.09
% 3.81/1.70  Abstraction          : 0.03
% 3.81/1.70  MUC search           : 0.00
% 3.81/1.70  Cooper               : 0.00
% 3.81/1.70  Total                : 0.91
% 3.81/1.70  Index Insertion      : 0.00
% 3.81/1.70  Index Deletion       : 0.00
% 3.81/1.70  Index Matching       : 0.00
% 3.81/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
