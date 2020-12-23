%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:16 EST 2020

% Result     : Theorem 4.44s
% Output     : CNFRefutation 4.44s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 111 expanded)
%              Number of leaves         :   35 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  121 ( 178 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(C),D)
         => ( r1_tarski(C,k1_relset_1(A,B,D))
            & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2338,plain,(
    ! [A_217,B_218,C_219] :
      ( k2_relset_1(A_217,B_218,C_219) = k2_relat_1(C_219)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2347,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_2338])).

tff(c_26,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_239,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_245,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_239])).

tff(c_249,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_245])).

tff(c_741,plain,(
    ! [A_99] :
      ( r1_tarski(A_99,k2_zfmisc_1(k1_relat_1(A_99),k2_relat_1(A_99)))
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_80,plain,(
    ! [A_40,B_41] :
      ( k2_xboole_0(A_40,B_41) = B_41
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    k2_xboole_0(k6_relat_1('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_80])).

tff(c_111,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,C_46)
      | ~ r1_tarski(k2_xboole_0(A_45,B_47),C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_114,plain,(
    ! [C_46] :
      ( r1_tarski(k6_relat_1('#skF_3'),C_46)
      | ~ r1_tarski('#skF_4',C_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_111])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_648,plain,(
    ! [C_83,A_84,B_85] :
      ( v4_relat_1(C_83,A_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_663,plain,(
    ! [A_88,A_89,B_90] :
      ( v4_relat_1(A_88,A_89)
      | ~ r1_tarski(A_88,k2_zfmisc_1(A_89,B_90)) ) ),
    inference(resolution,[status(thm)],[c_14,c_648])).

tff(c_684,plain,(
    ! [A_89,B_90] :
      ( v4_relat_1(k6_relat_1('#skF_3'),A_89)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_89,B_90)) ) ),
    inference(resolution,[status(thm)],[c_114,c_663])).

tff(c_744,plain,
    ( v4_relat_1(k6_relat_1('#skF_3'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_741,c_684])).

tff(c_776,plain,(
    v4_relat_1(k6_relat_1('#skF_3'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_744])).

tff(c_34,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1060,plain,(
    ! [B_118,A_119] :
      ( r1_tarski(k1_relat_1(B_118),A_119)
      | ~ v4_relat_1(B_118,A_119)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1086,plain,(
    ! [A_20,A_119] :
      ( r1_tarski(A_20,A_119)
      | ~ v4_relat_1(k6_relat_1(A_20),A_119)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1060])).

tff(c_1167,plain,(
    ! [A_126,A_127] :
      ( r1_tarski(A_126,A_127)
      | ~ v4_relat_1(k6_relat_1(A_126),A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1086])).

tff(c_1190,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_776,c_1167])).

tff(c_1262,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_relset_1(A_131,B_132,C_133) = k1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1271,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1262])).

tff(c_46,plain,
    ( ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_79,plain,(
    ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_1295,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1271,c_79])).

tff(c_1298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_1295])).

tff(c_1299,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2372,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2347,c_1299])).

tff(c_1432,plain,(
    ! [B_152,A_153] :
      ( v1_relat_1(B_152)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_153))
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1438,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_1432])).

tff(c_1442,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1438])).

tff(c_28,plain,(
    ! [A_19] :
      ( r1_tarski(A_19,k2_zfmisc_1(k1_relat_1(A_19),k2_relat_1(A_19)))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1301,plain,(
    ! [A_135,B_136] :
      ( k2_xboole_0(A_135,B_136) = B_136
      | ~ r1_tarski(A_135,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1316,plain,(
    k2_xboole_0(k6_relat_1('#skF_3'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48,c_1301])).

tff(c_1353,plain,(
    ! [A_142,C_143,B_144] :
      ( r1_tarski(A_142,C_143)
      | ~ r1_tarski(k2_xboole_0(A_142,B_144),C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1356,plain,(
    ! [C_143] :
      ( r1_tarski(k6_relat_1('#skF_3'),C_143)
      | ~ r1_tarski('#skF_4',C_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1316,c_1353])).

tff(c_1755,plain,(
    ! [C_168,B_169,A_170] :
      ( v5_relat_1(C_168,B_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_170,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1775,plain,(
    ! [A_174,B_175,A_176] :
      ( v5_relat_1(A_174,B_175)
      | ~ r1_tarski(A_174,k2_zfmisc_1(A_176,B_175)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1755])).

tff(c_3305,plain,(
    ! [B_270,A_271] :
      ( v5_relat_1(k6_relat_1('#skF_3'),B_270)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_271,B_270)) ) ),
    inference(resolution,[status(thm)],[c_1356,c_1775])).

tff(c_3308,plain,
    ( v5_relat_1(k6_relat_1('#skF_3'),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_3305])).

tff(c_3313,plain,(
    v5_relat_1(k6_relat_1('#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1442,c_3308])).

tff(c_32,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2195,plain,(
    ! [B_211,A_212] :
      ( r1_tarski(k2_relat_1(B_211),A_212)
      | ~ v5_relat_1(B_211,A_212)
      | ~ v1_relat_1(B_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2217,plain,(
    ! [A_20,A_212] :
      ( r1_tarski(A_20,A_212)
      | ~ v5_relat_1(k6_relat_1(A_20),A_212)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_2195])).

tff(c_2225,plain,(
    ! [A_20,A_212] :
      ( r1_tarski(A_20,A_212)
      | ~ v5_relat_1(k6_relat_1(A_20),A_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2217])).

tff(c_3321,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3313,c_2225])).

tff(c_3326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2372,c_3321])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.44/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.44/1.85  
% 4.44/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.44/1.85  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.44/1.85  
% 4.44/1.85  %Foreground sorts:
% 4.44/1.85  
% 4.44/1.85  
% 4.44/1.85  %Background operators:
% 4.44/1.85  
% 4.44/1.85  
% 4.44/1.85  %Foreground operators:
% 4.44/1.85  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.44/1.85  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.44/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.44/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.44/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.44/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.44/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.44/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.44/1.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.44/1.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.44/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.44/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.44/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.44/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.44/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.44/1.85  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.44/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.44/1.85  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.44/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.44/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.44/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.44/1.85  
% 4.44/1.87  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 4.44/1.87  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.44/1.87  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.44/1.87  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.44/1.87  tff(f_68, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 4.44/1.87  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.44/1.87  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.44/1.87  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.44/1.87  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.44/1.87  tff(f_76, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 4.44/1.87  tff(f_72, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.44/1.87  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.44/1.87  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.44/1.87  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.44/1.87  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.44/1.87  tff(c_2338, plain, (![A_217, B_218, C_219]: (k2_relset_1(A_217, B_218, C_219)=k2_relat_1(C_219) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.44/1.87  tff(c_2347, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_2338])).
% 4.44/1.87  tff(c_26, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.44/1.87  tff(c_239, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.44/1.87  tff(c_245, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_239])).
% 4.44/1.87  tff(c_249, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_245])).
% 4.44/1.87  tff(c_741, plain, (![A_99]: (r1_tarski(A_99, k2_zfmisc_1(k1_relat_1(A_99), k2_relat_1(A_99))) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.44/1.87  tff(c_48, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.44/1.87  tff(c_80, plain, (![A_40, B_41]: (k2_xboole_0(A_40, B_41)=B_41 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.44/1.87  tff(c_91, plain, (k2_xboole_0(k6_relat_1('#skF_3'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_48, c_80])).
% 4.44/1.87  tff(c_111, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, C_46) | ~r1_tarski(k2_xboole_0(A_45, B_47), C_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.44/1.87  tff(c_114, plain, (![C_46]: (r1_tarski(k6_relat_1('#skF_3'), C_46) | ~r1_tarski('#skF_4', C_46))), inference(superposition, [status(thm), theory('equality')], [c_91, c_111])).
% 4.44/1.87  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.44/1.87  tff(c_648, plain, (![C_83, A_84, B_85]: (v4_relat_1(C_83, A_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.44/1.87  tff(c_663, plain, (![A_88, A_89, B_90]: (v4_relat_1(A_88, A_89) | ~r1_tarski(A_88, k2_zfmisc_1(A_89, B_90)))), inference(resolution, [status(thm)], [c_14, c_648])).
% 4.44/1.87  tff(c_684, plain, (![A_89, B_90]: (v4_relat_1(k6_relat_1('#skF_3'), A_89) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_89, B_90)))), inference(resolution, [status(thm)], [c_114, c_663])).
% 4.44/1.87  tff(c_744, plain, (v4_relat_1(k6_relat_1('#skF_3'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_741, c_684])).
% 4.44/1.87  tff(c_776, plain, (v4_relat_1(k6_relat_1('#skF_3'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_744])).
% 4.44/1.87  tff(c_34, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.44/1.87  tff(c_30, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.44/1.87  tff(c_1060, plain, (![B_118, A_119]: (r1_tarski(k1_relat_1(B_118), A_119) | ~v4_relat_1(B_118, A_119) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.44/1.87  tff(c_1086, plain, (![A_20, A_119]: (r1_tarski(A_20, A_119) | ~v4_relat_1(k6_relat_1(A_20), A_119) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1060])).
% 4.44/1.87  tff(c_1167, plain, (![A_126, A_127]: (r1_tarski(A_126, A_127) | ~v4_relat_1(k6_relat_1(A_126), A_127))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1086])).
% 4.44/1.87  tff(c_1190, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_776, c_1167])).
% 4.44/1.87  tff(c_1262, plain, (![A_131, B_132, C_133]: (k1_relset_1(A_131, B_132, C_133)=k1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.44/1.87  tff(c_1271, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1262])).
% 4.44/1.87  tff(c_46, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.44/1.87  tff(c_79, plain, (~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_46])).
% 4.44/1.87  tff(c_1295, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1271, c_79])).
% 4.44/1.87  tff(c_1298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1190, c_1295])).
% 4.44/1.87  tff(c_1299, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_46])).
% 4.44/1.87  tff(c_2372, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2347, c_1299])).
% 4.44/1.87  tff(c_1432, plain, (![B_152, A_153]: (v1_relat_1(B_152) | ~m1_subset_1(B_152, k1_zfmisc_1(A_153)) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.44/1.87  tff(c_1438, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_1432])).
% 4.44/1.87  tff(c_1442, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1438])).
% 4.44/1.87  tff(c_28, plain, (![A_19]: (r1_tarski(A_19, k2_zfmisc_1(k1_relat_1(A_19), k2_relat_1(A_19))) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.44/1.87  tff(c_1301, plain, (![A_135, B_136]: (k2_xboole_0(A_135, B_136)=B_136 | ~r1_tarski(A_135, B_136))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.44/1.87  tff(c_1316, plain, (k2_xboole_0(k6_relat_1('#skF_3'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_48, c_1301])).
% 4.44/1.87  tff(c_1353, plain, (![A_142, C_143, B_144]: (r1_tarski(A_142, C_143) | ~r1_tarski(k2_xboole_0(A_142, B_144), C_143))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.44/1.87  tff(c_1356, plain, (![C_143]: (r1_tarski(k6_relat_1('#skF_3'), C_143) | ~r1_tarski('#skF_4', C_143))), inference(superposition, [status(thm), theory('equality')], [c_1316, c_1353])).
% 4.44/1.87  tff(c_1755, plain, (![C_168, B_169, A_170]: (v5_relat_1(C_168, B_169) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_170, B_169))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.44/1.87  tff(c_1775, plain, (![A_174, B_175, A_176]: (v5_relat_1(A_174, B_175) | ~r1_tarski(A_174, k2_zfmisc_1(A_176, B_175)))), inference(resolution, [status(thm)], [c_14, c_1755])).
% 4.44/1.87  tff(c_3305, plain, (![B_270, A_271]: (v5_relat_1(k6_relat_1('#skF_3'), B_270) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_271, B_270)))), inference(resolution, [status(thm)], [c_1356, c_1775])).
% 4.44/1.87  tff(c_3308, plain, (v5_relat_1(k6_relat_1('#skF_3'), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_3305])).
% 4.44/1.87  tff(c_3313, plain, (v5_relat_1(k6_relat_1('#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1442, c_3308])).
% 4.44/1.87  tff(c_32, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.44/1.87  tff(c_2195, plain, (![B_211, A_212]: (r1_tarski(k2_relat_1(B_211), A_212) | ~v5_relat_1(B_211, A_212) | ~v1_relat_1(B_211))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.44/1.87  tff(c_2217, plain, (![A_20, A_212]: (r1_tarski(A_20, A_212) | ~v5_relat_1(k6_relat_1(A_20), A_212) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_2195])).
% 4.44/1.87  tff(c_2225, plain, (![A_20, A_212]: (r1_tarski(A_20, A_212) | ~v5_relat_1(k6_relat_1(A_20), A_212))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2217])).
% 4.44/1.87  tff(c_3321, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_3313, c_2225])).
% 4.44/1.87  tff(c_3326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2372, c_3321])).
% 4.44/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.44/1.87  
% 4.44/1.87  Inference rules
% 4.44/1.87  ----------------------
% 4.44/1.87  #Ref     : 0
% 4.44/1.87  #Sup     : 733
% 4.44/1.87  #Fact    : 0
% 4.44/1.87  #Define  : 0
% 4.44/1.87  #Split   : 24
% 4.44/1.87  #Chain   : 0
% 4.44/1.87  #Close   : 0
% 4.44/1.87  
% 4.44/1.87  Ordering : KBO
% 4.44/1.87  
% 4.44/1.87  Simplification rules
% 4.44/1.87  ----------------------
% 4.44/1.87  #Subsume      : 91
% 4.44/1.87  #Demod        : 354
% 4.44/1.87  #Tautology    : 317
% 4.44/1.87  #SimpNegUnit  : 1
% 4.44/1.87  #BackRed      : 9
% 4.44/1.87  
% 4.44/1.87  #Partial instantiations: 0
% 4.44/1.87  #Strategies tried      : 1
% 4.44/1.87  
% 4.44/1.87  Timing (in seconds)
% 4.44/1.87  ----------------------
% 4.44/1.87  Preprocessing        : 0.33
% 4.44/1.87  Parsing              : 0.18
% 4.44/1.87  CNF conversion       : 0.02
% 4.44/1.87  Main loop            : 0.77
% 4.44/1.87  Inferencing          : 0.28
% 4.44/1.87  Reduction            : 0.26
% 4.44/1.87  Demodulation         : 0.19
% 4.44/1.87  BG Simplification    : 0.03
% 4.44/1.87  Subsumption          : 0.13
% 4.44/1.87  Abstraction          : 0.05
% 4.44/1.87  MUC search           : 0.00
% 4.44/1.87  Cooper               : 0.00
% 4.44/1.87  Total                : 1.14
% 4.44/1.87  Index Insertion      : 0.00
% 4.44/1.87  Index Deletion       : 0.00
% 4.44/1.87  Index Matching       : 0.00
% 4.44/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
