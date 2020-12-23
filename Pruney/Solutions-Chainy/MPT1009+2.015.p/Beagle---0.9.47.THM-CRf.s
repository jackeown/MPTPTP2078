%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:44 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 265 expanded)
%              Number of leaves         :   40 ( 108 expanded)
%              Depth                    :   13
%              Number of atoms          :  119 ( 557 expanded)
%              Number of equality atoms :   35 ( 142 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_68,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_207,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_219,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_207])).

tff(c_36,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k9_relat_1(B_18,A_17),k2_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_24,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1776,plain,(
    ! [B_201,A_202] :
      ( k1_tarski(k1_funct_1(B_201,A_202)) = k2_relat_1(B_201)
      | k1_tarski(A_202) != k1_relat_1(B_201)
      | ~ v1_funct_1(B_201)
      | ~ v1_relat_1(B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1719,plain,(
    ! [A_193,B_194,C_195,D_196] :
      ( k7_relset_1(A_193,B_194,C_195,D_196) = k9_relat_1(C_195,D_196)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1732,plain,(
    ! [D_196] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_196) = k9_relat_1('#skF_4',D_196) ),
    inference(resolution,[status(thm)],[c_62,c_1719])).

tff(c_58,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1766,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1732,c_58])).

tff(c_1782,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1776,c_1766])).

tff(c_1791,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_66,c_1782])).

tff(c_1834,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1791])).

tff(c_263,plain,(
    ! [C_62,A_63,B_64] :
      ( v4_relat_1(C_62,A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_277,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_263])).

tff(c_361,plain,(
    ! [B_85,A_86] :
      ( r1_tarski(k1_relat_1(B_85),A_86)
      | ~ v4_relat_1(B_85,A_86)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( k1_tarski(B_8) = A_7
      | k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_tarski(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2554,plain,(
    ! [B_280,B_281] :
      ( k1_tarski(B_280) = k1_relat_1(B_281)
      | k1_relat_1(B_281) = k1_xboole_0
      | ~ v4_relat_1(B_281,k1_tarski(B_280))
      | ~ v1_relat_1(B_281) ) ),
    inference(resolution,[status(thm)],[c_361,c_14])).

tff(c_2584,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_277,c_2554])).

tff(c_2603,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_2584])).

tff(c_2604,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1834,c_2603])).

tff(c_1671,plain,(
    ! [A_192] :
      ( m1_subset_1(A_192,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_192),k2_relat_1(A_192))))
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1693,plain,(
    ! [A_192] :
      ( r1_tarski(A_192,k2_zfmisc_1(k1_relat_1(A_192),k2_relat_1(A_192)))
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(resolution,[status(thm)],[c_1671,c_26])).

tff(c_2679,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2604,c_1693])).

tff(c_2724,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_66,c_24,c_2679])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_136,plain,(
    ! [B_45,A_46] :
      ( B_45 = A_46
      | ~ r1_tarski(B_45,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_148,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_136])).

tff(c_2762,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2724,c_148])).

tff(c_2812,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2762,c_8])).

tff(c_102,plain,(
    ! [A_36,B_37] : v1_relat_1(k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_104,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_102])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_162,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(k9_relat_1(B_48,A_49),k2_relat_1(B_48))
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_167,plain,(
    ! [A_49] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_49),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_162])).

tff(c_171,plain,(
    ! [A_50] : r1_tarski(k9_relat_1(k1_xboole_0,A_50),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_167])).

tff(c_177,plain,(
    ! [A_50] : k9_relat_1(k1_xboole_0,A_50) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_171,c_148])).

tff(c_2807,plain,(
    ! [A_50] : k9_relat_1('#skF_4',A_50) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2762,c_2762,c_177])).

tff(c_2996,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2807,c_1766])).

tff(c_3000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2812,c_2996])).

tff(c_3001,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1791])).

tff(c_3019,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_3001])).

tff(c_3023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_3019])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.78  
% 4.41/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.78  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.41/1.78  
% 4.41/1.78  %Foreground sorts:
% 4.41/1.78  
% 4.41/1.78  
% 4.41/1.78  %Background operators:
% 4.41/1.78  
% 4.41/1.78  
% 4.41/1.78  %Foreground operators:
% 4.41/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.41/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.41/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.41/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.41/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.41/1.78  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.41/1.78  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.41/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.41/1.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.41/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.41/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.41/1.78  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.41/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.41/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.41/1.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.41/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.41/1.78  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.41/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.41/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.41/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.41/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.41/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.41/1.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.41/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.41/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.41/1.78  
% 4.41/1.79  tff(f_112, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 4.41/1.79  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.41/1.79  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 4.41/1.79  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.41/1.79  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 4.41/1.79  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.41/1.79  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.41/1.79  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.41/1.79  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 4.41/1.79  tff(f_100, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 4.41/1.79  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.41/1.79  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.41/1.79  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.41/1.79  tff(f_61, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.41/1.79  tff(f_68, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.41/1.79  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.41/1.79  tff(c_207, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.41/1.79  tff(c_219, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_207])).
% 4.41/1.79  tff(c_36, plain, (![B_18, A_17]: (r1_tarski(k9_relat_1(B_18, A_17), k2_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.41/1.79  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.41/1.79  tff(c_24, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.41/1.79  tff(c_1776, plain, (![B_201, A_202]: (k1_tarski(k1_funct_1(B_201, A_202))=k2_relat_1(B_201) | k1_tarski(A_202)!=k1_relat_1(B_201) | ~v1_funct_1(B_201) | ~v1_relat_1(B_201))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.41/1.79  tff(c_1719, plain, (![A_193, B_194, C_195, D_196]: (k7_relset_1(A_193, B_194, C_195, D_196)=k9_relat_1(C_195, D_196) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.41/1.79  tff(c_1732, plain, (![D_196]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_196)=k9_relat_1('#skF_4', D_196))), inference(resolution, [status(thm)], [c_62, c_1719])).
% 4.41/1.79  tff(c_58, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.41/1.79  tff(c_1766, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1732, c_58])).
% 4.41/1.79  tff(c_1782, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1776, c_1766])).
% 4.41/1.79  tff(c_1791, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_66, c_1782])).
% 4.41/1.79  tff(c_1834, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1791])).
% 4.41/1.79  tff(c_263, plain, (![C_62, A_63, B_64]: (v4_relat_1(C_62, A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.41/1.79  tff(c_277, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_62, c_263])).
% 4.41/1.79  tff(c_361, plain, (![B_85, A_86]: (r1_tarski(k1_relat_1(B_85), A_86) | ~v4_relat_1(B_85, A_86) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.41/1.79  tff(c_14, plain, (![B_8, A_7]: (k1_tarski(B_8)=A_7 | k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_tarski(B_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.41/1.79  tff(c_2554, plain, (![B_280, B_281]: (k1_tarski(B_280)=k1_relat_1(B_281) | k1_relat_1(B_281)=k1_xboole_0 | ~v4_relat_1(B_281, k1_tarski(B_280)) | ~v1_relat_1(B_281))), inference(resolution, [status(thm)], [c_361, c_14])).
% 4.41/1.79  tff(c_2584, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_277, c_2554])).
% 4.41/1.79  tff(c_2603, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_219, c_2584])).
% 4.41/1.79  tff(c_2604, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1834, c_2603])).
% 4.41/1.79  tff(c_1671, plain, (![A_192]: (m1_subset_1(A_192, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_192), k2_relat_1(A_192)))) | ~v1_funct_1(A_192) | ~v1_relat_1(A_192))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.41/1.79  tff(c_26, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.41/1.79  tff(c_1693, plain, (![A_192]: (r1_tarski(A_192, k2_zfmisc_1(k1_relat_1(A_192), k2_relat_1(A_192))) | ~v1_funct_1(A_192) | ~v1_relat_1(A_192))), inference(resolution, [status(thm)], [c_1671, c_26])).
% 4.41/1.79  tff(c_2679, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2604, c_1693])).
% 4.41/1.79  tff(c_2724, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_219, c_66, c_24, c_2679])).
% 4.41/1.79  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.41/1.79  tff(c_136, plain, (![B_45, A_46]: (B_45=A_46 | ~r1_tarski(B_45, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.41/1.79  tff(c_148, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_136])).
% 4.41/1.79  tff(c_2762, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2724, c_148])).
% 4.41/1.79  tff(c_2812, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2762, c_8])).
% 4.41/1.79  tff(c_102, plain, (![A_36, B_37]: (v1_relat_1(k2_zfmisc_1(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.41/1.79  tff(c_104, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_102])).
% 4.41/1.79  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.41/1.79  tff(c_162, plain, (![B_48, A_49]: (r1_tarski(k9_relat_1(B_48, A_49), k2_relat_1(B_48)) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.41/1.79  tff(c_167, plain, (![A_49]: (r1_tarski(k9_relat_1(k1_xboole_0, A_49), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_162])).
% 4.41/1.79  tff(c_171, plain, (![A_50]: (r1_tarski(k9_relat_1(k1_xboole_0, A_50), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_167])).
% 4.41/1.79  tff(c_177, plain, (![A_50]: (k9_relat_1(k1_xboole_0, A_50)=k1_xboole_0)), inference(resolution, [status(thm)], [c_171, c_148])).
% 4.41/1.79  tff(c_2807, plain, (![A_50]: (k9_relat_1('#skF_4', A_50)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2762, c_2762, c_177])).
% 4.41/1.79  tff(c_2996, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2807, c_1766])).
% 4.41/1.79  tff(c_3000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2812, c_2996])).
% 4.41/1.79  tff(c_3001, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1791])).
% 4.41/1.79  tff(c_3019, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_3001])).
% 4.41/1.79  tff(c_3023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_219, c_3019])).
% 4.41/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.41/1.79  
% 4.41/1.79  Inference rules
% 4.41/1.79  ----------------------
% 4.41/1.79  #Ref     : 0
% 4.41/1.79  #Sup     : 614
% 4.41/1.79  #Fact    : 0
% 4.41/1.79  #Define  : 0
% 4.41/1.79  #Split   : 4
% 4.41/1.79  #Chain   : 0
% 4.41/1.79  #Close   : 0
% 4.41/1.79  
% 4.41/1.79  Ordering : KBO
% 4.41/1.79  
% 4.41/1.79  Simplification rules
% 4.41/1.79  ----------------------
% 4.41/1.79  #Subsume      : 67
% 4.41/1.79  #Demod        : 939
% 4.41/1.79  #Tautology    : 355
% 4.41/1.79  #SimpNegUnit  : 2
% 4.41/1.79  #BackRed      : 108
% 4.41/1.79  
% 4.41/1.79  #Partial instantiations: 0
% 4.41/1.79  #Strategies tried      : 1
% 4.41/1.79  
% 4.41/1.79  Timing (in seconds)
% 4.41/1.79  ----------------------
% 4.41/1.80  Preprocessing        : 0.33
% 4.41/1.80  Parsing              : 0.18
% 4.41/1.80  CNF conversion       : 0.02
% 4.41/1.80  Main loop            : 0.69
% 4.41/1.80  Inferencing          : 0.24
% 4.41/1.80  Reduction            : 0.25
% 4.41/1.80  Demodulation         : 0.19
% 4.41/1.80  BG Simplification    : 0.03
% 4.41/1.80  Subsumption          : 0.12
% 4.41/1.80  Abstraction          : 0.03
% 4.41/1.80  MUC search           : 0.00
% 4.41/1.80  Cooper               : 0.00
% 4.41/1.80  Total                : 1.05
% 4.41/1.80  Index Insertion      : 0.00
% 4.41/1.80  Index Deletion       : 0.00
% 4.41/1.80  Index Matching       : 0.00
% 4.41/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
