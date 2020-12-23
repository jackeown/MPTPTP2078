%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:24 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 126 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :    8
%              Number of atoms          :  116 ( 241 expanded)
%              Number of equality atoms :   19 (  35 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_601,plain,(
    ! [A_140,B_141,C_142] :
      ( k2_relset_1(A_140,B_141,C_142) = k2_relat_1(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_610,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_601])).

tff(c_253,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_262,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_253])).

tff(c_36,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_72,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_263,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_72])).

tff(c_18,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_87,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_93,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_87])).

tff(c_97,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_93])).

tff(c_38,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    ! [A_41,B_42] :
      ( v1_relat_1(A_41)
      | ~ v1_relat_1(B_42)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_10,c_87])).

tff(c_117,plain,
    ( v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_111])).

tff(c_126,plain,(
    v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_117])).

tff(c_24,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_294,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(k1_relat_1(A_81),k1_relat_1(B_82))
      | ~ r1_tarski(A_81,B_82)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_434,plain,(
    ! [A_106,B_107] :
      ( r1_tarski(A_106,k1_relat_1(B_107))
      | ~ r1_tarski(k6_relat_1(A_106),B_107)
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(k6_relat_1(A_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_294])).

tff(c_437,plain,
    ( r1_tarski('#skF_2',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_434])).

tff(c_444,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_97,c_437])).

tff(c_446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_444])).

tff(c_447,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_611,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_447])).

tff(c_466,plain,(
    ! [B_110,A_111] :
      ( v1_relat_1(B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_111))
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_472,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_466])).

tff(c_476,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_472])).

tff(c_498,plain,(
    ! [C_114,B_115,A_116] :
      ( v5_relat_1(C_114,B_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_116,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_507,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_498])).

tff(c_477,plain,(
    ! [A_112,B_113] :
      ( v1_relat_1(A_112)
      | ~ v1_relat_1(B_113)
      | ~ r1_tarski(A_112,B_113) ) ),
    inference(resolution,[status(thm)],[c_10,c_466])).

tff(c_486,plain,
    ( v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_477])).

tff(c_496,plain,(
    v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_486])).

tff(c_26,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_781,plain,(
    ! [A_174,B_175] :
      ( r1_tarski(k2_relat_1(A_174),k2_relat_1(B_175))
      | ~ r1_tarski(A_174,B_175)
      | ~ v1_relat_1(B_175)
      | ~ v1_relat_1(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_866,plain,(
    ! [A_184,B_185] :
      ( r1_tarski(A_184,k2_relat_1(B_185))
      | ~ r1_tarski(k6_relat_1(A_184),B_185)
      | ~ v1_relat_1(B_185)
      | ~ v1_relat_1(k6_relat_1(A_184)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_781])).

tff(c_869,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_866])).

tff(c_876,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_476,c_869])).

tff(c_532,plain,(
    ! [B_125,A_126] :
      ( r1_tarski(k2_relat_1(B_125),A_126)
      | ~ v5_relat_1(B_125,A_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_547,plain,(
    ! [B_125,A_126] :
      ( k2_relat_1(B_125) = A_126
      | ~ r1_tarski(A_126,k2_relat_1(B_125))
      | ~ v5_relat_1(B_125,A_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(resolution,[status(thm)],[c_532,c_2])).

tff(c_881,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_876,c_547])).

tff(c_889,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_507,c_881])).

tff(c_891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_611,c_889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:16:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.51  
% 3.23/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.51  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.23/1.51  
% 3.23/1.51  %Foreground sorts:
% 3.23/1.51  
% 3.23/1.51  
% 3.23/1.51  %Background operators:
% 3.23/1.51  
% 3.23/1.51  
% 3.23/1.51  %Foreground operators:
% 3.23/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.23/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.23/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.23/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.23/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.23/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.23/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.23/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.23/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.51  
% 3.39/1.54  tff(f_88, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relset_1)).
% 3.39/1.54  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.39/1.54  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.39/1.54  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.39/1.54  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.39/1.54  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.39/1.54  tff(f_65, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.39/1.54  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 3.39/1.54  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.39/1.54  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.39/1.54  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.39/1.54  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.39/1.54  tff(c_601, plain, (![A_140, B_141, C_142]: (k2_relset_1(A_140, B_141, C_142)=k2_relat_1(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.39/1.54  tff(c_610, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_601])).
% 3.39/1.54  tff(c_253, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.39/1.54  tff(c_262, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_253])).
% 3.39/1.54  tff(c_36, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.39/1.54  tff(c_72, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_36])).
% 3.39/1.54  tff(c_263, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_72])).
% 3.39/1.54  tff(c_18, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.39/1.54  tff(c_87, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.54  tff(c_93, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_87])).
% 3.39/1.54  tff(c_97, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_93])).
% 3.39/1.54  tff(c_38, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.39/1.54  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.39/1.54  tff(c_111, plain, (![A_41, B_42]: (v1_relat_1(A_41) | ~v1_relat_1(B_42) | ~r1_tarski(A_41, B_42))), inference(resolution, [status(thm)], [c_10, c_87])).
% 3.39/1.54  tff(c_117, plain, (v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_111])).
% 3.39/1.54  tff(c_126, plain, (v1_relat_1(k6_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_117])).
% 3.39/1.54  tff(c_24, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.39/1.54  tff(c_294, plain, (![A_81, B_82]: (r1_tarski(k1_relat_1(A_81), k1_relat_1(B_82)) | ~r1_tarski(A_81, B_82) | ~v1_relat_1(B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.39/1.54  tff(c_434, plain, (![A_106, B_107]: (r1_tarski(A_106, k1_relat_1(B_107)) | ~r1_tarski(k6_relat_1(A_106), B_107) | ~v1_relat_1(B_107) | ~v1_relat_1(k6_relat_1(A_106)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_294])).
% 3.39/1.54  tff(c_437, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_434])).
% 3.39/1.54  tff(c_444, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_97, c_437])).
% 3.39/1.54  tff(c_446, plain, $false, inference(negUnitSimplification, [status(thm)], [c_263, c_444])).
% 3.39/1.54  tff(c_447, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_36])).
% 3.39/1.54  tff(c_611, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_610, c_447])).
% 3.39/1.54  tff(c_466, plain, (![B_110, A_111]: (v1_relat_1(B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(A_111)) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.54  tff(c_472, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_466])).
% 3.39/1.54  tff(c_476, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_472])).
% 3.39/1.54  tff(c_498, plain, (![C_114, B_115, A_116]: (v5_relat_1(C_114, B_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_116, B_115))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.39/1.54  tff(c_507, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_498])).
% 3.39/1.54  tff(c_477, plain, (![A_112, B_113]: (v1_relat_1(A_112) | ~v1_relat_1(B_113) | ~r1_tarski(A_112, B_113))), inference(resolution, [status(thm)], [c_10, c_466])).
% 3.39/1.54  tff(c_486, plain, (v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_477])).
% 3.39/1.54  tff(c_496, plain, (v1_relat_1(k6_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_476, c_486])).
% 3.39/1.54  tff(c_26, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.39/1.54  tff(c_781, plain, (![A_174, B_175]: (r1_tarski(k2_relat_1(A_174), k2_relat_1(B_175)) | ~r1_tarski(A_174, B_175) | ~v1_relat_1(B_175) | ~v1_relat_1(A_174))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.39/1.54  tff(c_866, plain, (![A_184, B_185]: (r1_tarski(A_184, k2_relat_1(B_185)) | ~r1_tarski(k6_relat_1(A_184), B_185) | ~v1_relat_1(B_185) | ~v1_relat_1(k6_relat_1(A_184)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_781])).
% 3.39/1.54  tff(c_869, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_866])).
% 3.39/1.54  tff(c_876, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_496, c_476, c_869])).
% 3.39/1.54  tff(c_532, plain, (![B_125, A_126]: (r1_tarski(k2_relat_1(B_125), A_126) | ~v5_relat_1(B_125, A_126) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.39/1.54  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.54  tff(c_547, plain, (![B_125, A_126]: (k2_relat_1(B_125)=A_126 | ~r1_tarski(A_126, k2_relat_1(B_125)) | ~v5_relat_1(B_125, A_126) | ~v1_relat_1(B_125))), inference(resolution, [status(thm)], [c_532, c_2])).
% 3.39/1.54  tff(c_881, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_876, c_547])).
% 3.39/1.54  tff(c_889, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_476, c_507, c_881])).
% 3.39/1.54  tff(c_891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_611, c_889])).
% 3.39/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.54  
% 3.39/1.54  Inference rules
% 3.39/1.54  ----------------------
% 3.39/1.54  #Ref     : 0
% 3.39/1.54  #Sup     : 175
% 3.39/1.54  #Fact    : 0
% 3.39/1.54  #Define  : 0
% 3.39/1.54  #Split   : 10
% 3.39/1.54  #Chain   : 0
% 3.39/1.54  #Close   : 0
% 3.39/1.54  
% 3.39/1.54  Ordering : KBO
% 3.39/1.54  
% 3.39/1.54  Simplification rules
% 3.39/1.54  ----------------------
% 3.39/1.54  #Subsume      : 10
% 3.39/1.54  #Demod        : 68
% 3.39/1.54  #Tautology    : 57
% 3.39/1.54  #SimpNegUnit  : 3
% 3.39/1.54  #BackRed      : 5
% 3.39/1.54  
% 3.39/1.54  #Partial instantiations: 0
% 3.39/1.54  #Strategies tried      : 1
% 3.39/1.54  
% 3.39/1.54  Timing (in seconds)
% 3.39/1.54  ----------------------
% 3.39/1.54  Preprocessing        : 0.32
% 3.39/1.54  Parsing              : 0.17
% 3.39/1.54  CNF conversion       : 0.02
% 3.39/1.54  Main loop            : 0.42
% 3.39/1.54  Inferencing          : 0.16
% 3.39/1.54  Reduction            : 0.13
% 3.39/1.54  Demodulation         : 0.09
% 3.39/1.54  BG Simplification    : 0.02
% 3.39/1.54  Subsumption          : 0.08
% 3.39/1.54  Abstraction          : 0.02
% 3.39/1.54  MUC search           : 0.00
% 3.39/1.54  Cooper               : 0.00
% 3.39/1.54  Total                : 0.79
% 3.39/1.55  Index Insertion      : 0.00
% 3.39/1.55  Index Deletion       : 0.00
% 3.39/1.55  Index Matching       : 0.00
% 3.39/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
