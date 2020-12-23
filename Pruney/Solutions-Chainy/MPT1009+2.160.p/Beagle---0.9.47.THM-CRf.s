%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:04 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 190 expanded)
%              Number of leaves         :   37 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :   91 ( 391 expanded)
%              Number of equality atoms :   38 ( 106 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_relat_1)).

tff(c_10,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_66,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_66])).

tff(c_72,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_69])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_116,plain,(
    ! [B_56,A_57] :
      ( k1_tarski(k1_funct_1(B_56,A_57)) = k2_relat_1(B_56)
      | k1_tarski(A_57) != k1_relat_1(B_56)
      | ~ v1_funct_1(B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_102,plain,(
    ! [A_51,B_52,C_53,D_54] :
      ( k7_relset_1(A_51,B_52,C_53,D_54) = k9_relat_1(C_53,D_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_105,plain,(
    ! [D_54] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_54) = k9_relat_1('#skF_4',D_54) ),
    inference(resolution,[status(thm)],[c_42,c_102])).

tff(c_38,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_106,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_38])).

tff(c_122,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_106])).

tff(c_128,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_46,c_122])).

tff(c_130,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_44,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_83,plain,(
    ! [A_44,B_45,C_46] :
      ( k1_relset_1(A_44,B_45,C_46) = k1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_87,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_83])).

tff(c_157,plain,(
    ! [B_70,A_71,C_72] :
      ( k1_xboole_0 = B_70
      | k1_relset_1(A_71,B_70,C_72) = A_71
      | ~ v1_funct_2(C_72,A_71,B_70)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_160,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_157])).

tff(c_163,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_87,c_160])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_40,c_163])).

tff(c_167,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_168,plain,(
    ! [D_54] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_54) = k9_relat_1('#skF_4',D_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_105])).

tff(c_93,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_relset_1(A_48,B_49,C_50) = k2_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_97,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_93])).

tff(c_169,plain,(
    k2_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_97])).

tff(c_171,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_42])).

tff(c_226,plain,(
    ! [A_83,B_84,C_85] :
      ( k7_relset_1(A_83,B_84,C_85,A_83) = k2_relset_1(A_83,B_84,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_228,plain,(
    k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',k1_relat_1('#skF_4')) = k2_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_171,c_226])).

tff(c_230,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_169,c_228])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k9_relat_1(B_13,A_12),k9_relat_1(B_13,k1_relat_1(B_13)))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_237,plain,(
    ! [A_12] :
      ( r1_tarski(k9_relat_1('#skF_4',A_12),k2_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_12])).

tff(c_243,plain,(
    ! [A_12] : r1_tarski(k9_relat_1('#skF_4',A_12),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_237])).

tff(c_166,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.26  
% 2.27/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.27  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.27/1.27  
% 2.27/1.27  %Foreground sorts:
% 2.27/1.27  
% 2.27/1.27  
% 2.27/1.27  %Background operators:
% 2.27/1.27  
% 2.27/1.27  
% 2.27/1.27  %Foreground operators:
% 2.27/1.27  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.27/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.27  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.27/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.27/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.27/1.27  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.27/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.27/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.27/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.27  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.27/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.27  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.27/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.27  
% 2.27/1.28  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.27/1.28  tff(f_100, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 2.27/1.28  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.27/1.28  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.27/1.28  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.27/1.28  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.27/1.28  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.27/1.28  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.27/1.28  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.27/1.28  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_relat_1)).
% 2.27/1.28  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.27/1.28  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.27/1.28  tff(c_66, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.27/1.28  tff(c_69, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_66])).
% 2.27/1.28  tff(c_72, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_69])).
% 2.27/1.28  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.27/1.28  tff(c_116, plain, (![B_56, A_57]: (k1_tarski(k1_funct_1(B_56, A_57))=k2_relat_1(B_56) | k1_tarski(A_57)!=k1_relat_1(B_56) | ~v1_funct_1(B_56) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.27/1.28  tff(c_102, plain, (![A_51, B_52, C_53, D_54]: (k7_relset_1(A_51, B_52, C_53, D_54)=k9_relat_1(C_53, D_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.27/1.28  tff(c_105, plain, (![D_54]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_54)=k9_relat_1('#skF_4', D_54))), inference(resolution, [status(thm)], [c_42, c_102])).
% 2.27/1.28  tff(c_38, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.27/1.28  tff(c_106, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_38])).
% 2.27/1.28  tff(c_122, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_116, c_106])).
% 2.27/1.28  tff(c_128, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_46, c_122])).
% 2.27/1.28  tff(c_130, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_128])).
% 2.27/1.28  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.27/1.28  tff(c_44, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.27/1.28  tff(c_83, plain, (![A_44, B_45, C_46]: (k1_relset_1(A_44, B_45, C_46)=k1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.27/1.28  tff(c_87, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_83])).
% 2.27/1.28  tff(c_157, plain, (![B_70, A_71, C_72]: (k1_xboole_0=B_70 | k1_relset_1(A_71, B_70, C_72)=A_71 | ~v1_funct_2(C_72, A_71, B_70) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.27/1.28  tff(c_160, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_42, c_157])).
% 2.27/1.28  tff(c_163, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_87, c_160])).
% 2.27/1.28  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_40, c_163])).
% 2.27/1.28  tff(c_167, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_128])).
% 2.27/1.28  tff(c_168, plain, (![D_54]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_54)=k9_relat_1('#skF_4', D_54))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_105])).
% 2.27/1.28  tff(c_93, plain, (![A_48, B_49, C_50]: (k2_relset_1(A_48, B_49, C_50)=k2_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.27/1.28  tff(c_97, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_93])).
% 2.27/1.28  tff(c_169, plain, (k2_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_97])).
% 2.27/1.28  tff(c_171, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_42])).
% 2.27/1.28  tff(c_226, plain, (![A_83, B_84, C_85]: (k7_relset_1(A_83, B_84, C_85, A_83)=k2_relset_1(A_83, B_84, C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.27/1.28  tff(c_228, plain, (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', k1_relat_1('#skF_4'))=k2_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_171, c_226])).
% 2.27/1.28  tff(c_230, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_169, c_228])).
% 2.27/1.28  tff(c_12, plain, (![B_13, A_12]: (r1_tarski(k9_relat_1(B_13, A_12), k9_relat_1(B_13, k1_relat_1(B_13))) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.27/1.28  tff(c_237, plain, (![A_12]: (r1_tarski(k9_relat_1('#skF_4', A_12), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_230, c_12])).
% 2.27/1.28  tff(c_243, plain, (![A_12]: (r1_tarski(k9_relat_1('#skF_4', A_12), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_237])).
% 2.27/1.28  tff(c_166, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_128])).
% 2.27/1.28  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_243, c_166])).
% 2.27/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.28  
% 2.27/1.28  Inference rules
% 2.27/1.28  ----------------------
% 2.27/1.28  #Ref     : 0
% 2.27/1.28  #Sup     : 47
% 2.27/1.28  #Fact    : 0
% 2.27/1.28  #Define  : 0
% 2.27/1.28  #Split   : 1
% 2.27/1.28  #Chain   : 0
% 2.27/1.28  #Close   : 0
% 2.27/1.28  
% 2.27/1.28  Ordering : KBO
% 2.27/1.28  
% 2.27/1.28  Simplification rules
% 2.27/1.28  ----------------------
% 2.27/1.28  #Subsume      : 0
% 2.27/1.28  #Demod        : 27
% 2.27/1.28  #Tautology    : 34
% 2.27/1.28  #SimpNegUnit  : 1
% 2.27/1.28  #BackRed      : 7
% 2.27/1.28  
% 2.27/1.28  #Partial instantiations: 0
% 2.27/1.28  #Strategies tried      : 1
% 2.27/1.28  
% 2.27/1.28  Timing (in seconds)
% 2.27/1.28  ----------------------
% 2.27/1.28  Preprocessing        : 0.32
% 2.27/1.28  Parsing              : 0.17
% 2.27/1.28  CNF conversion       : 0.02
% 2.27/1.28  Main loop            : 0.19
% 2.27/1.28  Inferencing          : 0.07
% 2.27/1.28  Reduction            : 0.07
% 2.27/1.28  Demodulation         : 0.05
% 2.27/1.28  BG Simplification    : 0.01
% 2.27/1.28  Subsumption          : 0.02
% 2.27/1.29  Abstraction          : 0.01
% 2.27/1.29  MUC search           : 0.00
% 2.27/1.29  Cooper               : 0.00
% 2.27/1.29  Total                : 0.54
% 2.27/1.29  Index Insertion      : 0.00
% 2.27/1.29  Index Deletion       : 0.00
% 2.27/1.29  Index Matching       : 0.00
% 2.27/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
