%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:21 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 118 expanded)
%              Number of leaves         :   31 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 218 expanded)
%              Number of equality atoms :   23 (  41 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_702,plain,(
    ! [A_147,B_148,C_149] :
      ( k2_relset_1(A_147,B_148,C_149) = k2_relat_1(C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_147,B_148))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_711,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_702])).

tff(c_299,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_308,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_299])).

tff(c_34,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_120,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_309,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_120])).

tff(c_133,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_142,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_133])).

tff(c_36,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_153,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_163,plain,(
    ! [A_46,B_47] :
      ( v1_relat_1(A_46)
      | ~ v1_relat_1(B_47)
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_8,c_153])).

tff(c_169,plain,
    ( v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_163])).

tff(c_174,plain,(
    v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_169])).

tff(c_20,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_385,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(k1_relat_1(A_88),k1_relat_1(B_89))
      | ~ r1_tarski(A_88,B_89)
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_446,plain,(
    ! [A_103,B_104] :
      ( r1_tarski(A_103,k1_relat_1(B_104))
      | ~ r1_tarski(k6_relat_1(A_103),B_104)
      | ~ v1_relat_1(B_104)
      | ~ v1_relat_1(k6_relat_1(A_103)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_385])).

tff(c_449,plain,
    ( r1_tarski('#skF_2',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_446])).

tff(c_452,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_142,c_449])).

tff(c_454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_452])).

tff(c_455,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_712,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_455])).

tff(c_483,plain,(
    ! [C_109,A_110,B_111] :
      ( v1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_492,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_483])).

tff(c_540,plain,(
    ! [C_125,B_126,A_127] :
      ( v5_relat_1(C_125,B_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_127,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_549,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_540])).

tff(c_473,plain,(
    ! [B_107,A_108] :
      ( v1_relat_1(B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_108))
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_503,plain,(
    ! [A_115,B_116] :
      ( v1_relat_1(A_115)
      | ~ v1_relat_1(B_116)
      | ~ r1_tarski(A_115,B_116) ) ),
    inference(resolution,[status(thm)],[c_8,c_473])).

tff(c_512,plain,
    ( v1_relat_1(k6_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_503])).

tff(c_518,plain,(
    v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_512])).

tff(c_22,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_672,plain,(
    ! [A_143,B_144] :
      ( r1_tarski(k2_relat_1(A_143),k2_relat_1(B_144))
      | ~ r1_tarski(A_143,B_144)
      | ~ v1_relat_1(B_144)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_952,plain,(
    ! [A_184,B_185] :
      ( r1_tarski(A_184,k2_relat_1(B_185))
      | ~ r1_tarski(k6_relat_1(A_184),B_185)
      | ~ v1_relat_1(B_185)
      | ~ v1_relat_1(k6_relat_1(A_184)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_672])).

tff(c_955,plain,
    ( r1_tarski('#skF_2',k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_952])).

tff(c_958,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_492,c_955])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_973,plain,(
    k2_xboole_0('#skF_2',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_958,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_556,plain,(
    ! [B_131,A_132] :
      ( r1_tarski(k2_relat_1(B_131),A_132)
      | ~ v5_relat_1(B_131,A_132)
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_588,plain,(
    ! [B_135,A_136] :
      ( k2_xboole_0(k2_relat_1(B_135),A_136) = A_136
      | ~ v5_relat_1(B_135,A_136)
      | ~ v1_relat_1(B_135) ) ),
    inference(resolution,[status(thm)],[c_556,c_4])).

tff(c_608,plain,(
    ! [A_1,B_135] :
      ( k2_xboole_0(A_1,k2_relat_1(B_135)) = A_1
      | ~ v5_relat_1(B_135,A_1)
      | ~ v1_relat_1(B_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_588])).

tff(c_977,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_973,c_608])).

tff(c_984,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_549,c_977])).

tff(c_986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_712,c_984])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 19:04:52 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.45  
% 2.88/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.46  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.88/1.46  
% 2.88/1.46  %Foreground sorts:
% 2.88/1.46  
% 2.88/1.46  
% 2.88/1.46  %Background operators:
% 2.88/1.46  
% 2.88/1.46  
% 2.88/1.46  %Foreground operators:
% 2.88/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.88/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.88/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.88/1.46  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.88/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.88/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.88/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.88/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.46  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.88/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.88/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.88/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.46  
% 3.19/1.47  tff(f_90, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relset_1)).
% 3.19/1.47  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.19/1.47  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.19/1.47  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.19/1.47  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.19/1.47  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.19/1.47  tff(f_63, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.19/1.47  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 3.19/1.47  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.19/1.47  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.19/1.47  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.19/1.47  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.19/1.47  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.19/1.47  tff(c_702, plain, (![A_147, B_148, C_149]: (k2_relset_1(A_147, B_148, C_149)=k2_relat_1(C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_147, B_148))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.19/1.47  tff(c_711, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_702])).
% 3.19/1.47  tff(c_299, plain, (![A_75, B_76, C_77]: (k1_relset_1(A_75, B_76, C_77)=k1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.19/1.47  tff(c_308, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_299])).
% 3.19/1.47  tff(c_34, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.19/1.47  tff(c_120, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_34])).
% 3.19/1.47  tff(c_309, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_120])).
% 3.19/1.47  tff(c_133, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.19/1.47  tff(c_142, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_133])).
% 3.19/1.47  tff(c_36, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.19/1.47  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.19/1.47  tff(c_153, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.19/1.47  tff(c_163, plain, (![A_46, B_47]: (v1_relat_1(A_46) | ~v1_relat_1(B_47) | ~r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_8, c_153])).
% 3.19/1.47  tff(c_169, plain, (v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_163])).
% 3.19/1.47  tff(c_174, plain, (v1_relat_1(k6_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_169])).
% 3.19/1.47  tff(c_20, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.19/1.47  tff(c_385, plain, (![A_88, B_89]: (r1_tarski(k1_relat_1(A_88), k1_relat_1(B_89)) | ~r1_tarski(A_88, B_89) | ~v1_relat_1(B_89) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.19/1.47  tff(c_446, plain, (![A_103, B_104]: (r1_tarski(A_103, k1_relat_1(B_104)) | ~r1_tarski(k6_relat_1(A_103), B_104) | ~v1_relat_1(B_104) | ~v1_relat_1(k6_relat_1(A_103)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_385])).
% 3.19/1.47  tff(c_449, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_446])).
% 3.19/1.47  tff(c_452, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_142, c_449])).
% 3.19/1.47  tff(c_454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_309, c_452])).
% 3.19/1.47  tff(c_455, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 3.19/1.47  tff(c_712, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_711, c_455])).
% 3.19/1.47  tff(c_483, plain, (![C_109, A_110, B_111]: (v1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.19/1.47  tff(c_492, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_483])).
% 3.19/1.47  tff(c_540, plain, (![C_125, B_126, A_127]: (v5_relat_1(C_125, B_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_127, B_126))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.19/1.47  tff(c_549, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_540])).
% 3.19/1.47  tff(c_473, plain, (![B_107, A_108]: (v1_relat_1(B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(A_108)) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.19/1.47  tff(c_503, plain, (![A_115, B_116]: (v1_relat_1(A_115) | ~v1_relat_1(B_116) | ~r1_tarski(A_115, B_116))), inference(resolution, [status(thm)], [c_8, c_473])).
% 3.19/1.47  tff(c_512, plain, (v1_relat_1(k6_relat_1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_503])).
% 3.19/1.47  tff(c_518, plain, (v1_relat_1(k6_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_492, c_512])).
% 3.19/1.47  tff(c_22, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.19/1.47  tff(c_672, plain, (![A_143, B_144]: (r1_tarski(k2_relat_1(A_143), k2_relat_1(B_144)) | ~r1_tarski(A_143, B_144) | ~v1_relat_1(B_144) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.19/1.47  tff(c_952, plain, (![A_184, B_185]: (r1_tarski(A_184, k2_relat_1(B_185)) | ~r1_tarski(k6_relat_1(A_184), B_185) | ~v1_relat_1(B_185) | ~v1_relat_1(k6_relat_1(A_184)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_672])).
% 3.19/1.47  tff(c_955, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_952])).
% 3.19/1.47  tff(c_958, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_518, c_492, c_955])).
% 3.19/1.47  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.19/1.47  tff(c_973, plain, (k2_xboole_0('#skF_2', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_958, c_4])).
% 3.19/1.47  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.19/1.47  tff(c_556, plain, (![B_131, A_132]: (r1_tarski(k2_relat_1(B_131), A_132) | ~v5_relat_1(B_131, A_132) | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.19/1.47  tff(c_588, plain, (![B_135, A_136]: (k2_xboole_0(k2_relat_1(B_135), A_136)=A_136 | ~v5_relat_1(B_135, A_136) | ~v1_relat_1(B_135))), inference(resolution, [status(thm)], [c_556, c_4])).
% 3.19/1.47  tff(c_608, plain, (![A_1, B_135]: (k2_xboole_0(A_1, k2_relat_1(B_135))=A_1 | ~v5_relat_1(B_135, A_1) | ~v1_relat_1(B_135))), inference(superposition, [status(thm), theory('equality')], [c_2, c_588])).
% 3.19/1.47  tff(c_977, plain, (k2_relat_1('#skF_3')='#skF_2' | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_973, c_608])).
% 3.19/1.47  tff(c_984, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_492, c_549, c_977])).
% 3.19/1.47  tff(c_986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_712, c_984])).
% 3.19/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.47  
% 3.19/1.47  Inference rules
% 3.19/1.47  ----------------------
% 3.19/1.47  #Ref     : 0
% 3.19/1.47  #Sup     : 217
% 3.19/1.47  #Fact    : 0
% 3.19/1.47  #Define  : 0
% 3.19/1.47  #Split   : 5
% 3.19/1.47  #Chain   : 0
% 3.19/1.47  #Close   : 0
% 3.19/1.47  
% 3.19/1.47  Ordering : KBO
% 3.19/1.47  
% 3.19/1.47  Simplification rules
% 3.19/1.47  ----------------------
% 3.19/1.47  #Subsume      : 28
% 3.19/1.47  #Demod        : 55
% 3.19/1.47  #Tautology    : 72
% 3.19/1.47  #SimpNegUnit  : 4
% 3.19/1.47  #BackRed      : 5
% 3.19/1.47  
% 3.19/1.47  #Partial instantiations: 0
% 3.19/1.47  #Strategies tried      : 1
% 3.19/1.47  
% 3.19/1.47  Timing (in seconds)
% 3.19/1.47  ----------------------
% 3.19/1.47  Preprocessing        : 0.30
% 3.19/1.47  Parsing              : 0.17
% 3.19/1.47  CNF conversion       : 0.02
% 3.19/1.47  Main loop            : 0.40
% 3.19/1.48  Inferencing          : 0.16
% 3.19/1.48  Reduction            : 0.12
% 3.19/1.48  Demodulation         : 0.09
% 3.19/1.48  BG Simplification    : 0.02
% 3.19/1.48  Subsumption          : 0.06
% 3.19/1.48  Abstraction          : 0.02
% 3.19/1.48  MUC search           : 0.00
% 3.19/1.48  Cooper               : 0.00
% 3.19/1.48  Total                : 0.74
% 3.19/1.48  Index Insertion      : 0.00
% 3.19/1.48  Index Deletion       : 0.00
% 3.19/1.48  Index Matching       : 0.00
% 3.19/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
