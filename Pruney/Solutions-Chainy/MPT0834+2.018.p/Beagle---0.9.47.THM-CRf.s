%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:52 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 107 expanded)
%              Number of leaves         :   36 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 157 expanded)
%              Number of equality atoms :   42 (  66 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
          & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_268,plain,(
    ! [A_88,B_89,C_90,D_91] :
      ( k8_relset_1(A_88,B_89,C_90,D_91) = k10_relat_1(C_90,D_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_271,plain,(
    ! [D_91] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_91) = k10_relat_1('#skF_3',D_91) ),
    inference(resolution,[status(thm)],[c_32,c_268])).

tff(c_258,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_262,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_258])).

tff(c_34,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_34])).

tff(c_82,plain,(
    ! [C_47,A_48,B_49] :
      ( v4_relat_1(C_47,A_48)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_86,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_82])).

tff(c_87,plain,(
    ! [B_50,A_51] :
      ( k7_relat_1(B_50,A_51) = B_50
      | ~ v4_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_90,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_87])).

tff(c_93,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_90])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_97,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_8])).

tff(c_101,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_97])).

tff(c_157,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( k7_relset_1(A_66,B_67,C_68,D_69) = k9_relat_1(C_68,D_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_160,plain,(
    ! [D_69] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_69) = k9_relat_1('#skF_3',D_69) ),
    inference(resolution,[status(thm)],[c_32,c_157])).

tff(c_143,plain,(
    ! [A_59,B_60,C_61] :
      ( k2_relset_1(A_59,B_60,C_61) = k2_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_147,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_143])).

tff(c_30,plain,
    ( k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3')
    | k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_69,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_148,plain,(
    k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_69])).

tff(c_170,plain,(
    k9_relat_1('#skF_3','#skF_1') != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_148])).

tff(c_173,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_170])).

tff(c_174,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_263,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_174])).

tff(c_276,plain,(
    k10_relat_1('#skF_3','#skF_2') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_263])).

tff(c_48,plain,(
    ! [C_38,B_39,A_40] :
      ( v5_relat_1(C_38,B_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_40,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_52,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_48])).

tff(c_176,plain,(
    ! [B_71,A_72] :
      ( r1_tarski(k2_relat_1(B_71),A_72)
      | ~ v5_relat_1(B_71,A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_229,plain,(
    ! [B_80,A_81] :
      ( k3_xboole_0(k2_relat_1(B_80),A_81) = k2_relat_1(B_80)
      | ~ v5_relat_1(B_80,A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_176,c_2])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k10_relat_1(B_8,k3_xboole_0(k2_relat_1(B_8),A_7)) = k10_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_303,plain,(
    ! [B_98,A_99] :
      ( k10_relat_1(B_98,k2_relat_1(B_98)) = k10_relat_1(B_98,A_99)
      | ~ v1_relat_1(B_98)
      | ~ v5_relat_1(B_98,A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_10])).

tff(c_305,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_303])).

tff(c_308,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_305])).

tff(c_12,plain,(
    ! [A_9] :
      ( k10_relat_1(A_9,k2_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_312,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_12])).

tff(c_319,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_312])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_276,c_319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:25:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.27  
% 2.13/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.28  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.13/1.28  
% 2.13/1.28  %Foreground sorts:
% 2.13/1.28  
% 2.13/1.28  
% 2.13/1.28  %Background operators:
% 2.13/1.28  
% 2.13/1.28  
% 2.13/1.28  %Foreground operators:
% 2.13/1.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.13/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.13/1.28  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.13/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.13/1.28  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.13/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.13/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.13/1.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.13/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.13/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.13/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.28  
% 2.33/1.29  tff(f_86, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.33/1.29  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.33/1.29  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.33/1.29  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.33/1.29  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.33/1.29  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.33/1.29  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.33/1.29  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.33/1.29  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.33/1.29  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.33/1.29  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.33/1.29  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.33/1.29  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.33/1.29  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.33/1.29  tff(c_268, plain, (![A_88, B_89, C_90, D_91]: (k8_relset_1(A_88, B_89, C_90, D_91)=k10_relat_1(C_90, D_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.33/1.29  tff(c_271, plain, (![D_91]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_91)=k10_relat_1('#skF_3', D_91))), inference(resolution, [status(thm)], [c_32, c_268])).
% 2.33/1.29  tff(c_258, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.33/1.29  tff(c_262, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_258])).
% 2.33/1.29  tff(c_34, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.33/1.29  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_34])).
% 2.33/1.29  tff(c_82, plain, (![C_47, A_48, B_49]: (v4_relat_1(C_47, A_48) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.33/1.29  tff(c_86, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_82])).
% 2.33/1.29  tff(c_87, plain, (![B_50, A_51]: (k7_relat_1(B_50, A_51)=B_50 | ~v4_relat_1(B_50, A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.33/1.29  tff(c_90, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_87])).
% 2.33/1.29  tff(c_93, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_90])).
% 2.33/1.29  tff(c_8, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.33/1.29  tff(c_97, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_93, c_8])).
% 2.33/1.29  tff(c_101, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_97])).
% 2.33/1.29  tff(c_157, plain, (![A_66, B_67, C_68, D_69]: (k7_relset_1(A_66, B_67, C_68, D_69)=k9_relat_1(C_68, D_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.33/1.29  tff(c_160, plain, (![D_69]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_69)=k9_relat_1('#skF_3', D_69))), inference(resolution, [status(thm)], [c_32, c_157])).
% 2.33/1.29  tff(c_143, plain, (![A_59, B_60, C_61]: (k2_relset_1(A_59, B_60, C_61)=k2_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.33/1.29  tff(c_147, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_143])).
% 2.33/1.29  tff(c_30, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3') | k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.33/1.29  tff(c_69, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.33/1.29  tff(c_148, plain, (k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_147, c_69])).
% 2.33/1.29  tff(c_170, plain, (k9_relat_1('#skF_3', '#skF_1')!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_148])).
% 2.33/1.29  tff(c_173, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_170])).
% 2.33/1.29  tff(c_174, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.33/1.29  tff(c_263, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_262, c_174])).
% 2.33/1.29  tff(c_276, plain, (k10_relat_1('#skF_3', '#skF_2')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_263])).
% 2.33/1.29  tff(c_48, plain, (![C_38, B_39, A_40]: (v5_relat_1(C_38, B_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_40, B_39))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.33/1.29  tff(c_52, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_48])).
% 2.33/1.29  tff(c_176, plain, (![B_71, A_72]: (r1_tarski(k2_relat_1(B_71), A_72) | ~v5_relat_1(B_71, A_72) | ~v1_relat_1(B_71))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.29  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.33/1.29  tff(c_229, plain, (![B_80, A_81]: (k3_xboole_0(k2_relat_1(B_80), A_81)=k2_relat_1(B_80) | ~v5_relat_1(B_80, A_81) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_176, c_2])).
% 2.33/1.29  tff(c_10, plain, (![B_8, A_7]: (k10_relat_1(B_8, k3_xboole_0(k2_relat_1(B_8), A_7))=k10_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.33/1.29  tff(c_303, plain, (![B_98, A_99]: (k10_relat_1(B_98, k2_relat_1(B_98))=k10_relat_1(B_98, A_99) | ~v1_relat_1(B_98) | ~v5_relat_1(B_98, A_99) | ~v1_relat_1(B_98))), inference(superposition, [status(thm), theory('equality')], [c_229, c_10])).
% 2.33/1.29  tff(c_305, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_303])).
% 2.33/1.29  tff(c_308, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_305])).
% 2.33/1.29  tff(c_12, plain, (![A_9]: (k10_relat_1(A_9, k2_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.33/1.29  tff(c_312, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_308, c_12])).
% 2.33/1.29  tff(c_319, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_312])).
% 2.33/1.29  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_276, c_319])).
% 2.33/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.29  
% 2.33/1.29  Inference rules
% 2.33/1.29  ----------------------
% 2.33/1.29  #Ref     : 0
% 2.33/1.29  #Sup     : 75
% 2.33/1.29  #Fact    : 0
% 2.33/1.29  #Define  : 0
% 2.33/1.29  #Split   : 1
% 2.33/1.29  #Chain   : 0
% 2.33/1.29  #Close   : 0
% 2.33/1.29  
% 2.33/1.29  Ordering : KBO
% 2.33/1.29  
% 2.33/1.29  Simplification rules
% 2.33/1.29  ----------------------
% 2.33/1.29  #Subsume      : 0
% 2.33/1.29  #Demod        : 14
% 2.33/1.29  #Tautology    : 43
% 2.33/1.29  #SimpNegUnit  : 1
% 2.33/1.29  #BackRed      : 5
% 2.33/1.29  
% 2.33/1.29  #Partial instantiations: 0
% 2.33/1.29  #Strategies tried      : 1
% 2.33/1.29  
% 2.33/1.29  Timing (in seconds)
% 2.33/1.29  ----------------------
% 2.33/1.29  Preprocessing        : 0.30
% 2.33/1.29  Parsing              : 0.17
% 2.33/1.29  CNF conversion       : 0.02
% 2.33/1.29  Main loop            : 0.20
% 2.33/1.29  Inferencing          : 0.08
% 2.33/1.29  Reduction            : 0.06
% 2.33/1.29  Demodulation         : 0.04
% 2.33/1.29  BG Simplification    : 0.01
% 2.33/1.29  Subsumption          : 0.02
% 2.33/1.29  Abstraction          : 0.01
% 2.33/1.29  MUC search           : 0.00
% 2.33/1.29  Cooper               : 0.00
% 2.33/1.29  Total                : 0.53
% 2.33/1.29  Index Insertion      : 0.00
% 2.33/1.29  Index Deletion       : 0.00
% 2.33/1.29  Index Matching       : 0.00
% 2.33/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
