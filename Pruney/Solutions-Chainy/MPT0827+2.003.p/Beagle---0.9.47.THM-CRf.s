%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:15 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   75 (  97 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :  120 ( 174 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(C),D)
         => ( r1_tarski(C,k1_relset_1(A,B,D))
            & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v4_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).

tff(f_67,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_746,plain,(
    ! [A_155,B_156,C_157] :
      ( k2_relset_1(A_155,B_156,C_157) = k2_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_755,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_746])).

tff(c_279,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_relset_1(A_79,B_80,C_81) = k1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_288,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_279])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_72,plain,(
    ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_289,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_72])).

tff(c_87,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_relat_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_96,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_87])).

tff(c_38,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_179,plain,(
    ! [B_60,A_61] :
      ( v4_relat_1(B_60,A_61)
      | ~ r1_tarski(k1_relat_1(B_60),A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_193,plain,(
    ! [B_60] :
      ( v4_relat_1(B_60,k1_relat_1(B_60))
      | ~ v1_relat_1(B_60) ) ),
    inference(resolution,[status(thm)],[c_6,c_179])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_343,plain,(
    ! [C_90,A_91,B_92] :
      ( v4_relat_1(C_90,A_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(B_92))
      | ~ v4_relat_1(B_92,A_91)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_442,plain,(
    ! [A_104,A_105,B_106] :
      ( v4_relat_1(A_104,A_105)
      | ~ v4_relat_1(B_106,A_105)
      | ~ v1_relat_1(B_106)
      | ~ r1_tarski(A_104,B_106) ) ),
    inference(resolution,[status(thm)],[c_10,c_343])).

tff(c_495,plain,(
    ! [A_110,B_111] :
      ( v4_relat_1(A_110,k1_relat_1(B_111))
      | ~ r1_tarski(A_110,B_111)
      | ~ v1_relat_1(B_111) ) ),
    inference(resolution,[status(thm)],[c_193,c_442])).

tff(c_24,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_97,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(k1_relat_1(B_41),A_42)
      | ~ v4_relat_1(B_41,A_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_102,plain,(
    ! [A_18,A_42] :
      ( r1_tarski(A_18,A_42)
      | ~ v4_relat_1(k6_relat_1(A_18),A_42)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_97])).

tff(c_105,plain,(
    ! [A_18,A_42] :
      ( r1_tarski(A_18,A_42)
      | ~ v4_relat_1(k6_relat_1(A_18),A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_102])).

tff(c_543,plain,(
    ! [A_117,B_118] :
      ( r1_tarski(A_117,k1_relat_1(B_118))
      | ~ r1_tarski(k6_relat_1(A_117),B_118)
      | ~ v1_relat_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_495,c_105])).

tff(c_546,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_543])).

tff(c_553,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_546])).

tff(c_555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_553])).

tff(c_556,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_756,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_556])).

tff(c_558,plain,(
    ! [C_119,A_120,B_121] :
      ( v1_relat_1(C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_567,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_558])).

tff(c_611,plain,(
    ! [B_131,A_132] :
      ( v5_relat_1(B_131,A_132)
      | ~ r1_tarski(k2_relat_1(B_131),A_132)
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_625,plain,(
    ! [B_131] :
      ( v5_relat_1(B_131,k2_relat_1(B_131))
      | ~ v1_relat_1(B_131) ) ),
    inference(resolution,[status(thm)],[c_6,c_611])).

tff(c_837,plain,(
    ! [C_171,A_172,B_173] :
      ( v5_relat_1(C_171,A_172)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(B_173))
      | ~ v5_relat_1(B_173,A_172)
      | ~ v1_relat_1(B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_954,plain,(
    ! [A_190,A_191,B_192] :
      ( v5_relat_1(A_190,A_191)
      | ~ v5_relat_1(B_192,A_191)
      | ~ v1_relat_1(B_192)
      | ~ r1_tarski(A_190,B_192) ) ),
    inference(resolution,[status(thm)],[c_10,c_837])).

tff(c_990,plain,(
    ! [A_195,B_196] :
      ( v5_relat_1(A_195,k2_relat_1(B_196))
      | ~ r1_tarski(A_195,B_196)
      | ~ v1_relat_1(B_196) ) ),
    inference(resolution,[status(thm)],[c_625,c_954])).

tff(c_28,plain,(
    ! [A_18] : k2_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_597,plain,(
    ! [B_129,A_130] :
      ( r1_tarski(k2_relat_1(B_129),A_130)
      | ~ v5_relat_1(B_129,A_130)
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_606,plain,(
    ! [A_18,A_130] :
      ( r1_tarski(A_18,A_130)
      | ~ v5_relat_1(k6_relat_1(A_18),A_130)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_597])).

tff(c_610,plain,(
    ! [A_18,A_130] :
      ( r1_tarski(A_18,A_130)
      | ~ v5_relat_1(k6_relat_1(A_18),A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_606])).

tff(c_1049,plain,(
    ! [A_203,B_204] :
      ( r1_tarski(A_203,k2_relat_1(B_204))
      | ~ r1_tarski(k6_relat_1(A_203),B_204)
      | ~ v1_relat_1(B_204) ) ),
    inference(resolution,[status(thm)],[c_990,c_610])).

tff(c_1052,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_1049])).

tff(c_1059,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_1052])).

tff(c_1061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_756,c_1059])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.51  
% 3.03/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.51  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.03/1.51  
% 3.03/1.51  %Foreground sorts:
% 3.03/1.51  
% 3.03/1.51  
% 3.03/1.51  %Background operators:
% 3.03/1.51  
% 3.03/1.51  
% 3.03/1.51  %Foreground operators:
% 3.03/1.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.03/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.03/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.03/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.03/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.03/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.03/1.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.03/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.03/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.03/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.03/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.03/1.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.03/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.03/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.03/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.51  
% 3.03/1.53  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 3.03/1.53  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.03/1.53  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.03/1.53  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.03/1.53  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.03/1.53  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.03/1.53  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.03/1.53  tff(f_44, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v4_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_relat_1)).
% 3.03/1.53  tff(f_67, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.03/1.53  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.03/1.53  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.03/1.53  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_relat_1)).
% 3.03/1.53  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.03/1.53  tff(c_746, plain, (![A_155, B_156, C_157]: (k2_relset_1(A_155, B_156, C_157)=k2_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.03/1.53  tff(c_755, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_746])).
% 3.03/1.53  tff(c_279, plain, (![A_79, B_80, C_81]: (k1_relset_1(A_79, B_80, C_81)=k1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.03/1.53  tff(c_288, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_279])).
% 3.03/1.53  tff(c_36, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.03/1.53  tff(c_72, plain, (~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_36])).
% 3.03/1.53  tff(c_289, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_288, c_72])).
% 3.03/1.53  tff(c_87, plain, (![C_38, A_39, B_40]: (v1_relat_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.03/1.53  tff(c_96, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_87])).
% 3.03/1.53  tff(c_38, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.03/1.53  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.03/1.53  tff(c_179, plain, (![B_60, A_61]: (v4_relat_1(B_60, A_61) | ~r1_tarski(k1_relat_1(B_60), A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.03/1.53  tff(c_193, plain, (![B_60]: (v4_relat_1(B_60, k1_relat_1(B_60)) | ~v1_relat_1(B_60))), inference(resolution, [status(thm)], [c_6, c_179])).
% 3.03/1.53  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.03/1.53  tff(c_343, plain, (![C_90, A_91, B_92]: (v4_relat_1(C_90, A_91) | ~m1_subset_1(C_90, k1_zfmisc_1(B_92)) | ~v4_relat_1(B_92, A_91) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.03/1.53  tff(c_442, plain, (![A_104, A_105, B_106]: (v4_relat_1(A_104, A_105) | ~v4_relat_1(B_106, A_105) | ~v1_relat_1(B_106) | ~r1_tarski(A_104, B_106))), inference(resolution, [status(thm)], [c_10, c_343])).
% 3.03/1.53  tff(c_495, plain, (![A_110, B_111]: (v4_relat_1(A_110, k1_relat_1(B_111)) | ~r1_tarski(A_110, B_111) | ~v1_relat_1(B_111))), inference(resolution, [status(thm)], [c_193, c_442])).
% 3.03/1.53  tff(c_24, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.03/1.53  tff(c_26, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.03/1.53  tff(c_97, plain, (![B_41, A_42]: (r1_tarski(k1_relat_1(B_41), A_42) | ~v4_relat_1(B_41, A_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.03/1.53  tff(c_102, plain, (![A_18, A_42]: (r1_tarski(A_18, A_42) | ~v4_relat_1(k6_relat_1(A_18), A_42) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_97])).
% 3.03/1.53  tff(c_105, plain, (![A_18, A_42]: (r1_tarski(A_18, A_42) | ~v4_relat_1(k6_relat_1(A_18), A_42))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_102])).
% 3.03/1.53  tff(c_543, plain, (![A_117, B_118]: (r1_tarski(A_117, k1_relat_1(B_118)) | ~r1_tarski(k6_relat_1(A_117), B_118) | ~v1_relat_1(B_118))), inference(resolution, [status(thm)], [c_495, c_105])).
% 3.03/1.53  tff(c_546, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_543])).
% 3.03/1.53  tff(c_553, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_546])).
% 3.03/1.53  tff(c_555, plain, $false, inference(negUnitSimplification, [status(thm)], [c_289, c_553])).
% 3.03/1.53  tff(c_556, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_36])).
% 3.03/1.53  tff(c_756, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_755, c_556])).
% 3.03/1.53  tff(c_558, plain, (![C_119, A_120, B_121]: (v1_relat_1(C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.03/1.53  tff(c_567, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_558])).
% 3.03/1.53  tff(c_611, plain, (![B_131, A_132]: (v5_relat_1(B_131, A_132) | ~r1_tarski(k2_relat_1(B_131), A_132) | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.03/1.53  tff(c_625, plain, (![B_131]: (v5_relat_1(B_131, k2_relat_1(B_131)) | ~v1_relat_1(B_131))), inference(resolution, [status(thm)], [c_6, c_611])).
% 3.03/1.53  tff(c_837, plain, (![C_171, A_172, B_173]: (v5_relat_1(C_171, A_172) | ~m1_subset_1(C_171, k1_zfmisc_1(B_173)) | ~v5_relat_1(B_173, A_172) | ~v1_relat_1(B_173))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.03/1.53  tff(c_954, plain, (![A_190, A_191, B_192]: (v5_relat_1(A_190, A_191) | ~v5_relat_1(B_192, A_191) | ~v1_relat_1(B_192) | ~r1_tarski(A_190, B_192))), inference(resolution, [status(thm)], [c_10, c_837])).
% 3.03/1.53  tff(c_990, plain, (![A_195, B_196]: (v5_relat_1(A_195, k2_relat_1(B_196)) | ~r1_tarski(A_195, B_196) | ~v1_relat_1(B_196))), inference(resolution, [status(thm)], [c_625, c_954])).
% 3.03/1.53  tff(c_28, plain, (![A_18]: (k2_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.03/1.53  tff(c_597, plain, (![B_129, A_130]: (r1_tarski(k2_relat_1(B_129), A_130) | ~v5_relat_1(B_129, A_130) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.03/1.53  tff(c_606, plain, (![A_18, A_130]: (r1_tarski(A_18, A_130) | ~v5_relat_1(k6_relat_1(A_18), A_130) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_597])).
% 3.03/1.53  tff(c_610, plain, (![A_18, A_130]: (r1_tarski(A_18, A_130) | ~v5_relat_1(k6_relat_1(A_18), A_130))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_606])).
% 3.03/1.53  tff(c_1049, plain, (![A_203, B_204]: (r1_tarski(A_203, k2_relat_1(B_204)) | ~r1_tarski(k6_relat_1(A_203), B_204) | ~v1_relat_1(B_204))), inference(resolution, [status(thm)], [c_990, c_610])).
% 3.03/1.53  tff(c_1052, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38, c_1049])).
% 3.03/1.53  tff(c_1059, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_567, c_1052])).
% 3.03/1.53  tff(c_1061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_756, c_1059])).
% 3.03/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.53  
% 3.03/1.53  Inference rules
% 3.03/1.53  ----------------------
% 3.03/1.53  #Ref     : 0
% 3.03/1.53  #Sup     : 197
% 3.03/1.53  #Fact    : 0
% 3.03/1.53  #Define  : 0
% 3.03/1.53  #Split   : 7
% 3.03/1.53  #Chain   : 0
% 3.03/1.53  #Close   : 0
% 3.03/1.53  
% 3.03/1.53  Ordering : KBO
% 3.03/1.53  
% 3.03/1.53  Simplification rules
% 3.03/1.53  ----------------------
% 3.03/1.53  #Subsume      : 17
% 3.03/1.53  #Demod        : 105
% 3.03/1.53  #Tautology    : 52
% 3.03/1.53  #SimpNegUnit  : 2
% 3.03/1.53  #BackRed      : 3
% 3.03/1.53  
% 3.03/1.53  #Partial instantiations: 0
% 3.03/1.53  #Strategies tried      : 1
% 3.03/1.53  
% 3.03/1.53  Timing (in seconds)
% 3.03/1.53  ----------------------
% 3.03/1.53  Preprocessing        : 0.31
% 3.03/1.53  Parsing              : 0.17
% 3.03/1.53  CNF conversion       : 0.02
% 3.03/1.53  Main loop            : 0.39
% 3.03/1.53  Inferencing          : 0.15
% 3.03/1.53  Reduction            : 0.12
% 3.03/1.53  Demodulation         : 0.09
% 3.03/1.53  BG Simplification    : 0.02
% 3.03/1.53  Subsumption          : 0.07
% 3.03/1.53  Abstraction          : 0.02
% 3.03/1.53  MUC search           : 0.00
% 3.03/1.53  Cooper               : 0.00
% 3.03/1.53  Total                : 0.74
% 3.03/1.53  Index Insertion      : 0.00
% 3.03/1.53  Index Deletion       : 0.00
% 3.03/1.53  Index Matching       : 0.00
% 3.03/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
