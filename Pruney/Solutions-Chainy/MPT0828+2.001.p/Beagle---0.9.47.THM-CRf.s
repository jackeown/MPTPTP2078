%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:17 EST 2020

% Result     : Theorem 4.23s
% Output     : CNFRefutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 113 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  139 ( 219 expanded)
%              Number of equality atoms :   19 (  33 expanded)
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

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v4_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1375,plain,(
    ! [A_247,B_248,C_249] :
      ( k2_relset_1(A_247,B_248,C_249) = k2_relat_1(C_249)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1384,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1375])).

tff(c_349,plain,(
    ! [A_97,B_98,C_99] :
      ( k1_relset_1(A_97,B_98,C_99) = k1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_358,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_349])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_73,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_359,plain,(
    k1_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_73])).

tff(c_83,plain,(
    ! [C_41,A_42,B_43] :
      ( v1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_92,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_83])).

tff(c_154,plain,(
    ! [C_59,A_60,B_61] :
      ( v4_relat_1(C_59,A_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_163,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_154])).

tff(c_46,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    ! [B_56,A_57] :
      ( v4_relat_1(B_56,A_57)
      | ~ r1_tarski(k1_relat_1(B_56),A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_147,plain,(
    ! [B_56] :
      ( v4_relat_1(B_56,k1_relat_1(B_56))
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_137])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_439,plain,(
    ! [C_115,A_116,B_117] :
      ( v4_relat_1(C_115,A_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(B_117))
      | ~ v4_relat_1(B_117,A_116)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_541,plain,(
    ! [A_128,A_129,B_130] :
      ( v4_relat_1(A_128,A_129)
      | ~ v4_relat_1(B_130,A_129)
      | ~ v1_relat_1(B_130)
      | ~ r1_tarski(A_128,B_130) ) ),
    inference(resolution,[status(thm)],[c_10,c_439])).

tff(c_627,plain,(
    ! [A_137,B_138] :
      ( v4_relat_1(A_137,k1_relat_1(B_138))
      | ~ r1_tarski(A_137,B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(resolution,[status(thm)],[c_147,c_541])).

tff(c_28,plain,(
    ! [A_18] : v1_relat_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_228,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(k1_relat_1(B_76),A_77)
      | ~ v4_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_244,plain,(
    ! [A_17,A_77] :
      ( r1_tarski(A_17,A_77)
      | ~ v4_relat_1(k6_relat_1(A_17),A_77)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_228])).

tff(c_250,plain,(
    ! [A_17,A_77] :
      ( r1_tarski(A_17,A_77)
      | ~ v4_relat_1(k6_relat_1(A_17),A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_244])).

tff(c_976,plain,(
    ! [A_177,B_178] :
      ( r1_tarski(A_177,k1_relat_1(B_178))
      | ~ r1_tarski(k6_relat_1(A_177),B_178)
      | ~ v1_relat_1(B_178) ) ),
    inference(resolution,[status(thm)],[c_627,c_250])).

tff(c_979,plain,
    ( r1_tarski('#skF_2',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_976])).

tff(c_986,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_979])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_248,plain,(
    ! [B_76,A_77] :
      ( k1_relat_1(B_76) = A_77
      | ~ r1_tarski(A_77,k1_relat_1(B_76))
      | ~ v4_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_228,c_2])).

tff(c_992,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v4_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_986,c_248])).

tff(c_997,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_163,c_992])).

tff(c_999,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_359,c_997])).

tff(c_1000,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1385,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1384,c_1000])).

tff(c_1015,plain,(
    ! [C_181,A_182,B_183] :
      ( v1_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1024,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1015])).

tff(c_1083,plain,(
    ! [B_198,A_199] :
      ( v5_relat_1(B_198,A_199)
      | ~ r1_tarski(k2_relat_1(B_198),A_199)
      | ~ v1_relat_1(B_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1097,plain,(
    ! [B_198] :
      ( v5_relat_1(B_198,k2_relat_1(B_198))
      | ~ v1_relat_1(B_198) ) ),
    inference(resolution,[status(thm)],[c_6,c_1083])).

tff(c_1200,plain,(
    ! [C_220,A_221,B_222] :
      ( v5_relat_1(C_220,A_221)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(B_222))
      | ~ v5_relat_1(B_222,A_221)
      | ~ v1_relat_1(B_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1666,plain,(
    ! [A_273,A_274,B_275] :
      ( v5_relat_1(A_273,A_274)
      | ~ v5_relat_1(B_275,A_274)
      | ~ v1_relat_1(B_275)
      | ~ r1_tarski(A_273,B_275) ) ),
    inference(resolution,[status(thm)],[c_10,c_1200])).

tff(c_1740,plain,(
    ! [A_280,B_281] :
      ( v5_relat_1(A_280,k2_relat_1(B_281))
      | ~ r1_tarski(A_280,B_281)
      | ~ v1_relat_1(B_281) ) ),
    inference(resolution,[status(thm)],[c_1097,c_1666])).

tff(c_26,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1069,plain,(
    ! [B_196,A_197] :
      ( r1_tarski(k2_relat_1(B_196),A_197)
      | ~ v5_relat_1(B_196,A_197)
      | ~ v1_relat_1(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1078,plain,(
    ! [A_17,A_197] :
      ( r1_tarski(A_17,A_197)
      | ~ v5_relat_1(k6_relat_1(A_17),A_197)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1069])).

tff(c_1082,plain,(
    ! [A_17,A_197] :
      ( r1_tarski(A_17,A_197)
      | ~ v5_relat_1(k6_relat_1(A_17),A_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1078])).

tff(c_2005,plain,(
    ! [A_312,B_313] :
      ( r1_tarski(A_312,k2_relat_1(B_313))
      | ~ r1_tarski(k6_relat_1(A_312),B_313)
      | ~ v1_relat_1(B_313) ) ),
    inference(resolution,[status(thm)],[c_1740,c_1082])).

tff(c_2008,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_2005])).

tff(c_2015,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1024,c_2008])).

tff(c_2017,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1385,c_2015])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:34:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.23/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.82  
% 4.23/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.82  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.23/1.82  
% 4.23/1.82  %Foreground sorts:
% 4.23/1.82  
% 4.23/1.82  
% 4.23/1.82  %Background operators:
% 4.23/1.82  
% 4.23/1.82  
% 4.23/1.82  %Foreground operators:
% 4.23/1.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.23/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.23/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.23/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.23/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.23/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.23/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.23/1.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.23/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.23/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.23/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.23/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.23/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.23/1.82  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.23/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.23/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.23/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.23/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.23/1.82  
% 4.23/1.83  tff(f_102, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relset_1)).
% 4.23/1.83  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.23/1.83  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.23/1.83  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.23/1.83  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.23/1.83  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.23/1.83  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.23/1.83  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.23/1.83  tff(f_44, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v4_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_relat_1)).
% 4.23/1.83  tff(f_75, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 4.23/1.83  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.23/1.83  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.23/1.83  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_relat_1)).
% 4.23/1.83  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.23/1.83  tff(c_1375, plain, (![A_247, B_248, C_249]: (k2_relset_1(A_247, B_248, C_249)=k2_relat_1(C_249) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_248))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.23/1.83  tff(c_1384, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1375])).
% 4.23/1.83  tff(c_349, plain, (![A_97, B_98, C_99]: (k1_relset_1(A_97, B_98, C_99)=k1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.23/1.83  tff(c_358, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_349])).
% 4.23/1.83  tff(c_44, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.23/1.83  tff(c_73, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_44])).
% 4.23/1.83  tff(c_359, plain, (k1_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_358, c_73])).
% 4.23/1.83  tff(c_83, plain, (![C_41, A_42, B_43]: (v1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.23/1.83  tff(c_92, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_83])).
% 4.23/1.83  tff(c_154, plain, (![C_59, A_60, B_61]: (v4_relat_1(C_59, A_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.23/1.83  tff(c_163, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_154])).
% 4.23/1.83  tff(c_46, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.23/1.83  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.23/1.83  tff(c_137, plain, (![B_56, A_57]: (v4_relat_1(B_56, A_57) | ~r1_tarski(k1_relat_1(B_56), A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.23/1.83  tff(c_147, plain, (![B_56]: (v4_relat_1(B_56, k1_relat_1(B_56)) | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_6, c_137])).
% 4.23/1.83  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.23/1.83  tff(c_439, plain, (![C_115, A_116, B_117]: (v4_relat_1(C_115, A_116) | ~m1_subset_1(C_115, k1_zfmisc_1(B_117)) | ~v4_relat_1(B_117, A_116) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.23/1.83  tff(c_541, plain, (![A_128, A_129, B_130]: (v4_relat_1(A_128, A_129) | ~v4_relat_1(B_130, A_129) | ~v1_relat_1(B_130) | ~r1_tarski(A_128, B_130))), inference(resolution, [status(thm)], [c_10, c_439])).
% 4.23/1.83  tff(c_627, plain, (![A_137, B_138]: (v4_relat_1(A_137, k1_relat_1(B_138)) | ~r1_tarski(A_137, B_138) | ~v1_relat_1(B_138))), inference(resolution, [status(thm)], [c_147, c_541])).
% 4.23/1.83  tff(c_28, plain, (![A_18]: (v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.23/1.83  tff(c_24, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.23/1.83  tff(c_228, plain, (![B_76, A_77]: (r1_tarski(k1_relat_1(B_76), A_77) | ~v4_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.23/1.83  tff(c_244, plain, (![A_17, A_77]: (r1_tarski(A_17, A_77) | ~v4_relat_1(k6_relat_1(A_17), A_77) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_228])).
% 4.23/1.83  tff(c_250, plain, (![A_17, A_77]: (r1_tarski(A_17, A_77) | ~v4_relat_1(k6_relat_1(A_17), A_77))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_244])).
% 4.23/1.83  tff(c_976, plain, (![A_177, B_178]: (r1_tarski(A_177, k1_relat_1(B_178)) | ~r1_tarski(k6_relat_1(A_177), B_178) | ~v1_relat_1(B_178))), inference(resolution, [status(thm)], [c_627, c_250])).
% 4.23/1.83  tff(c_979, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_976])).
% 4.23/1.83  tff(c_986, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_979])).
% 4.23/1.83  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.23/1.83  tff(c_248, plain, (![B_76, A_77]: (k1_relat_1(B_76)=A_77 | ~r1_tarski(A_77, k1_relat_1(B_76)) | ~v4_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_228, c_2])).
% 4.23/1.83  tff(c_992, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v4_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_986, c_248])).
% 4.23/1.83  tff(c_997, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_163, c_992])).
% 4.23/1.83  tff(c_999, plain, $false, inference(negUnitSimplification, [status(thm)], [c_359, c_997])).
% 4.23/1.83  tff(c_1000, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_44])).
% 4.23/1.83  tff(c_1385, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1384, c_1000])).
% 4.23/1.83  tff(c_1015, plain, (![C_181, A_182, B_183]: (v1_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.23/1.83  tff(c_1024, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1015])).
% 4.23/1.83  tff(c_1083, plain, (![B_198, A_199]: (v5_relat_1(B_198, A_199) | ~r1_tarski(k2_relat_1(B_198), A_199) | ~v1_relat_1(B_198))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.23/1.83  tff(c_1097, plain, (![B_198]: (v5_relat_1(B_198, k2_relat_1(B_198)) | ~v1_relat_1(B_198))), inference(resolution, [status(thm)], [c_6, c_1083])).
% 4.23/1.83  tff(c_1200, plain, (![C_220, A_221, B_222]: (v5_relat_1(C_220, A_221) | ~m1_subset_1(C_220, k1_zfmisc_1(B_222)) | ~v5_relat_1(B_222, A_221) | ~v1_relat_1(B_222))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.23/1.83  tff(c_1666, plain, (![A_273, A_274, B_275]: (v5_relat_1(A_273, A_274) | ~v5_relat_1(B_275, A_274) | ~v1_relat_1(B_275) | ~r1_tarski(A_273, B_275))), inference(resolution, [status(thm)], [c_10, c_1200])).
% 4.23/1.83  tff(c_1740, plain, (![A_280, B_281]: (v5_relat_1(A_280, k2_relat_1(B_281)) | ~r1_tarski(A_280, B_281) | ~v1_relat_1(B_281))), inference(resolution, [status(thm)], [c_1097, c_1666])).
% 4.23/1.83  tff(c_26, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.23/1.83  tff(c_1069, plain, (![B_196, A_197]: (r1_tarski(k2_relat_1(B_196), A_197) | ~v5_relat_1(B_196, A_197) | ~v1_relat_1(B_196))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.23/1.83  tff(c_1078, plain, (![A_17, A_197]: (r1_tarski(A_17, A_197) | ~v5_relat_1(k6_relat_1(A_17), A_197) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1069])).
% 4.23/1.83  tff(c_1082, plain, (![A_17, A_197]: (r1_tarski(A_17, A_197) | ~v5_relat_1(k6_relat_1(A_17), A_197))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1078])).
% 4.23/1.83  tff(c_2005, plain, (![A_312, B_313]: (r1_tarski(A_312, k2_relat_1(B_313)) | ~r1_tarski(k6_relat_1(A_312), B_313) | ~v1_relat_1(B_313))), inference(resolution, [status(thm)], [c_1740, c_1082])).
% 4.23/1.83  tff(c_2008, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_2005])).
% 4.23/1.83  tff(c_2015, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1024, c_2008])).
% 4.23/1.83  tff(c_2017, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1385, c_2015])).
% 4.23/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.83  
% 4.23/1.83  Inference rules
% 4.23/1.83  ----------------------
% 4.23/1.83  #Ref     : 0
% 4.23/1.83  #Sup     : 376
% 4.23/1.83  #Fact    : 0
% 4.23/1.83  #Define  : 0
% 4.23/1.83  #Split   : 11
% 4.23/1.83  #Chain   : 0
% 4.23/1.83  #Close   : 0
% 4.23/1.83  
% 4.23/1.83  Ordering : KBO
% 4.23/1.83  
% 4.23/1.83  Simplification rules
% 4.23/1.83  ----------------------
% 4.23/1.83  #Subsume      : 51
% 4.23/1.83  #Demod        : 233
% 4.23/1.83  #Tautology    : 104
% 4.23/1.84  #SimpNegUnit  : 2
% 4.23/1.84  #BackRed      : 4
% 4.23/1.84  
% 4.23/1.84  #Partial instantiations: 0
% 4.23/1.84  #Strategies tried      : 1
% 4.23/1.84  
% 4.23/1.84  Timing (in seconds)
% 4.23/1.84  ----------------------
% 4.23/1.84  Preprocessing        : 0.40
% 4.23/1.84  Parsing              : 0.18
% 4.23/1.84  CNF conversion       : 0.04
% 4.23/1.84  Main loop            : 0.64
% 4.23/1.84  Inferencing          : 0.24
% 4.23/1.84  Reduction            : 0.20
% 4.23/1.84  Demodulation         : 0.14
% 4.23/1.84  BG Simplification    : 0.03
% 4.23/1.84  Subsumption          : 0.12
% 4.23/1.84  Abstraction          : 0.03
% 4.23/1.84  MUC search           : 0.00
% 4.23/1.84  Cooper               : 0.00
% 4.23/1.84  Total                : 1.08
% 4.23/1.84  Index Insertion      : 0.00
% 4.23/1.84  Index Deletion       : 0.00
% 4.23/1.84  Index Matching       : 0.00
% 4.23/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
