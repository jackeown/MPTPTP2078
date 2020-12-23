%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:16 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 103 expanded)
%              Number of leaves         :   32 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :  129 ( 186 expanded)
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

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(C),D)
         => ( r1_tarski(C,k1_relset_1(A,B,D))
            & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_76,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v4_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).

tff(f_74,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(B))
         => v5_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_577,plain,(
    ! [A_120,B_121,C_122] :
      ( k2_relset_1(A_120,B_121,C_122) = k2_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_586,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_577])).

tff(c_366,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_375,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_366])).

tff(c_38,plain,
    ( ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_70,plain,(
    ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_376,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_70])).

tff(c_28,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_90,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_96,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_90])).

tff(c_100,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_96])).

tff(c_40,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [B_46,A_47] :
      ( v4_relat_1(B_46,A_47)
      | ~ r1_tarski(k1_relat_1(B_46),A_47)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_128,plain,(
    ! [B_46] :
      ( v4_relat_1(B_46,k1_relat_1(B_46))
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_6,c_118])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_263,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(B_75))
      | ~ v4_relat_1(B_75,A_74)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_290,plain,(
    ! [A_77,A_78,B_79] :
      ( v4_relat_1(A_77,A_78)
      | ~ v4_relat_1(B_79,A_78)
      | ~ v1_relat_1(B_79)
      | ~ r1_tarski(A_77,B_79) ) ),
    inference(resolution,[status(thm)],[c_10,c_263])).

tff(c_326,plain,(
    ! [A_82,B_83] :
      ( v4_relat_1(A_82,k1_relat_1(B_83))
      | ~ r1_tarski(A_82,B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_128,c_290])).

tff(c_26,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ! [A_23] : k1_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_186,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(k1_relat_1(B_60),A_61)
      | ~ v4_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_197,plain,(
    ! [A_23,A_61] :
      ( r1_tarski(A_23,A_61)
      | ~ v4_relat_1(k6_relat_1(A_23),A_61)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_186])).

tff(c_202,plain,(
    ! [A_23,A_61] :
      ( r1_tarski(A_23,A_61)
      | ~ v4_relat_1(k6_relat_1(A_23),A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_197])).

tff(c_411,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(A_93,k1_relat_1(B_94))
      | ~ r1_tarski(k6_relat_1(A_93),B_94)
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_326,c_202])).

tff(c_414,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_411])).

tff(c_421,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_414])).

tff(c_423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_421])).

tff(c_424,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_593,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_424])).

tff(c_448,plain,(
    ! [B_99,A_100] :
      ( v1_relat_1(B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_100))
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_454,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_448])).

tff(c_458,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_454])).

tff(c_549,plain,(
    ! [B_117,A_118] :
      ( v5_relat_1(B_117,A_118)
      | ~ r1_tarski(k2_relat_1(B_117),A_118)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_563,plain,(
    ! [B_117] :
      ( v5_relat_1(B_117,k2_relat_1(B_117))
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_6,c_549])).

tff(c_819,plain,(
    ! [C_155,A_156,B_157] :
      ( v5_relat_1(C_155,A_156)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(B_157))
      | ~ v5_relat_1(B_157,A_156)
      | ~ v1_relat_1(B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_910,plain,(
    ! [A_166,A_167,B_168] :
      ( v5_relat_1(A_166,A_167)
      | ~ v5_relat_1(B_168,A_167)
      | ~ v1_relat_1(B_168)
      | ~ r1_tarski(A_166,B_168) ) ),
    inference(resolution,[status(thm)],[c_10,c_819])).

tff(c_958,plain,(
    ! [A_173,B_174] :
      ( v5_relat_1(A_173,k2_relat_1(B_174))
      | ~ r1_tarski(A_173,B_174)
      | ~ v1_relat_1(B_174) ) ),
    inference(resolution,[status(thm)],[c_563,c_910])).

tff(c_32,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_535,plain,(
    ! [B_113,A_114] :
      ( r1_tarski(k2_relat_1(B_113),A_114)
      | ~ v5_relat_1(B_113,A_114)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_543,plain,(
    ! [A_23,A_114] :
      ( r1_tarski(A_23,A_114)
      | ~ v5_relat_1(k6_relat_1(A_23),A_114)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_535])).

tff(c_547,plain,(
    ! [A_23,A_114] :
      ( r1_tarski(A_23,A_114)
      | ~ v5_relat_1(k6_relat_1(A_23),A_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_543])).

tff(c_1028,plain,(
    ! [A_181,B_182] :
      ( r1_tarski(A_181,k2_relat_1(B_182))
      | ~ r1_tarski(k6_relat_1(A_181),B_182)
      | ~ v1_relat_1(B_182) ) ),
    inference(resolution,[status(thm)],[c_958,c_547])).

tff(c_1035,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_1028])).

tff(c_1043,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_1035])).

tff(c_1045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_593,c_1043])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.43  
% 2.79/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.43  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.79/1.43  
% 2.79/1.43  %Foreground sorts:
% 2.79/1.43  
% 2.79/1.43  
% 2.79/1.43  %Background operators:
% 2.79/1.43  
% 2.79/1.43  
% 2.79/1.43  %Foreground operators:
% 2.79/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.79/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.79/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.79/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.79/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.79/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.43  
% 2.79/1.45  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 2.79/1.45  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.79/1.45  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.79/1.45  tff(f_76, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.79/1.45  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.79/1.45  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.79/1.45  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.79/1.45  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.79/1.45  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v4_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_relat_1)).
% 2.79/1.45  tff(f_74, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.79/1.45  tff(f_80, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.79/1.45  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.79/1.45  tff(f_60, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(B)) => v5_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc6_relat_1)).
% 2.79/1.45  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.79/1.45  tff(c_577, plain, (![A_120, B_121, C_122]: (k2_relset_1(A_120, B_121, C_122)=k2_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.79/1.45  tff(c_586, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_577])).
% 2.79/1.45  tff(c_366, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.79/1.45  tff(c_375, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_366])).
% 2.79/1.45  tff(c_38, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.79/1.45  tff(c_70, plain, (~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_38])).
% 2.79/1.45  tff(c_376, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_375, c_70])).
% 2.79/1.45  tff(c_28, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.79/1.45  tff(c_90, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.79/1.45  tff(c_96, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_90])).
% 2.79/1.45  tff(c_100, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_96])).
% 2.79/1.45  tff(c_40, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.79/1.45  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.79/1.45  tff(c_118, plain, (![B_46, A_47]: (v4_relat_1(B_46, A_47) | ~r1_tarski(k1_relat_1(B_46), A_47) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.79/1.45  tff(c_128, plain, (![B_46]: (v4_relat_1(B_46, k1_relat_1(B_46)) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_6, c_118])).
% 2.79/1.45  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.79/1.45  tff(c_263, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(B_75)) | ~v4_relat_1(B_75, A_74) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.79/1.45  tff(c_290, plain, (![A_77, A_78, B_79]: (v4_relat_1(A_77, A_78) | ~v4_relat_1(B_79, A_78) | ~v1_relat_1(B_79) | ~r1_tarski(A_77, B_79))), inference(resolution, [status(thm)], [c_10, c_263])).
% 2.79/1.45  tff(c_326, plain, (![A_82, B_83]: (v4_relat_1(A_82, k1_relat_1(B_83)) | ~r1_tarski(A_82, B_83) | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_128, c_290])).
% 2.79/1.45  tff(c_26, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.79/1.45  tff(c_30, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.79/1.45  tff(c_186, plain, (![B_60, A_61]: (r1_tarski(k1_relat_1(B_60), A_61) | ~v4_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.79/1.45  tff(c_197, plain, (![A_23, A_61]: (r1_tarski(A_23, A_61) | ~v4_relat_1(k6_relat_1(A_23), A_61) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_186])).
% 2.79/1.45  tff(c_202, plain, (![A_23, A_61]: (r1_tarski(A_23, A_61) | ~v4_relat_1(k6_relat_1(A_23), A_61))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_197])).
% 2.79/1.45  tff(c_411, plain, (![A_93, B_94]: (r1_tarski(A_93, k1_relat_1(B_94)) | ~r1_tarski(k6_relat_1(A_93), B_94) | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_326, c_202])).
% 2.79/1.45  tff(c_414, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_411])).
% 2.79/1.45  tff(c_421, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_414])).
% 2.79/1.45  tff(c_423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_376, c_421])).
% 2.79/1.45  tff(c_424, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_38])).
% 2.79/1.45  tff(c_593, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_424])).
% 2.79/1.45  tff(c_448, plain, (![B_99, A_100]: (v1_relat_1(B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(A_100)) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.79/1.45  tff(c_454, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_448])).
% 2.79/1.45  tff(c_458, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_454])).
% 2.79/1.45  tff(c_549, plain, (![B_117, A_118]: (v5_relat_1(B_117, A_118) | ~r1_tarski(k2_relat_1(B_117), A_118) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.79/1.45  tff(c_563, plain, (![B_117]: (v5_relat_1(B_117, k2_relat_1(B_117)) | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_6, c_549])).
% 2.79/1.45  tff(c_819, plain, (![C_155, A_156, B_157]: (v5_relat_1(C_155, A_156) | ~m1_subset_1(C_155, k1_zfmisc_1(B_157)) | ~v5_relat_1(B_157, A_156) | ~v1_relat_1(B_157))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.79/1.45  tff(c_910, plain, (![A_166, A_167, B_168]: (v5_relat_1(A_166, A_167) | ~v5_relat_1(B_168, A_167) | ~v1_relat_1(B_168) | ~r1_tarski(A_166, B_168))), inference(resolution, [status(thm)], [c_10, c_819])).
% 2.79/1.45  tff(c_958, plain, (![A_173, B_174]: (v5_relat_1(A_173, k2_relat_1(B_174)) | ~r1_tarski(A_173, B_174) | ~v1_relat_1(B_174))), inference(resolution, [status(thm)], [c_563, c_910])).
% 2.79/1.45  tff(c_32, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.79/1.45  tff(c_535, plain, (![B_113, A_114]: (r1_tarski(k2_relat_1(B_113), A_114) | ~v5_relat_1(B_113, A_114) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.79/1.45  tff(c_543, plain, (![A_23, A_114]: (r1_tarski(A_23, A_114) | ~v5_relat_1(k6_relat_1(A_23), A_114) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_535])).
% 2.79/1.45  tff(c_547, plain, (![A_23, A_114]: (r1_tarski(A_23, A_114) | ~v5_relat_1(k6_relat_1(A_23), A_114))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_543])).
% 2.79/1.45  tff(c_1028, plain, (![A_181, B_182]: (r1_tarski(A_181, k2_relat_1(B_182)) | ~r1_tarski(k6_relat_1(A_181), B_182) | ~v1_relat_1(B_182))), inference(resolution, [status(thm)], [c_958, c_547])).
% 2.79/1.45  tff(c_1035, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_1028])).
% 2.79/1.45  tff(c_1043, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_458, c_1035])).
% 2.79/1.45  tff(c_1045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_593, c_1043])).
% 2.79/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.45  
% 2.79/1.45  Inference rules
% 2.79/1.45  ----------------------
% 2.79/1.45  #Ref     : 0
% 2.79/1.45  #Sup     : 199
% 2.79/1.45  #Fact    : 0
% 2.79/1.45  #Define  : 0
% 2.79/1.45  #Split   : 11
% 2.79/1.45  #Chain   : 0
% 2.79/1.45  #Close   : 0
% 2.79/1.45  
% 2.79/1.45  Ordering : KBO
% 2.79/1.45  
% 2.79/1.45  Simplification rules
% 2.79/1.45  ----------------------
% 2.79/1.45  #Subsume      : 23
% 2.79/1.45  #Demod        : 114
% 2.79/1.45  #Tautology    : 57
% 2.79/1.45  #SimpNegUnit  : 3
% 2.79/1.45  #BackRed      : 5
% 2.79/1.45  
% 2.79/1.45  #Partial instantiations: 0
% 2.79/1.45  #Strategies tried      : 1
% 2.79/1.45  
% 2.79/1.45  Timing (in seconds)
% 2.79/1.45  ----------------------
% 2.79/1.45  Preprocessing        : 0.31
% 2.79/1.45  Parsing              : 0.17
% 2.79/1.45  CNF conversion       : 0.02
% 2.79/1.45  Main loop            : 0.39
% 2.79/1.45  Inferencing          : 0.14
% 2.79/1.45  Reduction            : 0.13
% 2.79/1.45  Demodulation         : 0.09
% 2.79/1.45  BG Simplification    : 0.02
% 2.79/1.45  Subsumption          : 0.07
% 2.79/1.45  Abstraction          : 0.02
% 2.79/1.45  MUC search           : 0.00
% 2.79/1.45  Cooper               : 0.00
% 2.79/1.45  Total                : 0.73
% 2.79/1.45  Index Insertion      : 0.00
% 2.79/1.45  Index Deletion       : 0.00
% 2.79/1.45  Index Matching       : 0.00
% 2.79/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
