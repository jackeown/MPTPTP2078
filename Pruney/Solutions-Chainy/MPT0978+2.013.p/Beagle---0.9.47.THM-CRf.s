%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:53 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 119 expanded)
%              Number of leaves         :   37 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  126 ( 285 expanded)
%              Number of equality atoms :   26 (  48 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
             => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_99,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_211,plain,(
    ! [A_68,B_69,C_70] :
      ( k2_relset_1(A_68,B_69,C_70) = k2_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_229,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_211])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_230,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_42])).

tff(c_297,plain,(
    ! [A_81,B_82,C_83] :
      ( m1_subset_1(k2_relset_1(A_81,B_82,C_83),k1_zfmisc_1(B_82))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_319,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_297])).

tff(c_329,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_319])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_372,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_329,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_377,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_372,c_2])).

tff(c_381,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_377])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_126,plain,(
    ! [B_54,A_55] :
      ( v1_relat_1(B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_55))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_135,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_126])).

tff(c_145,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_135])).

tff(c_138,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_126])).

tff(c_148,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_138])).

tff(c_40,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_20,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_57,plain,(
    ! [A_13] : k2_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_20])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_693,plain,(
    ! [A_133,D_134,E_131,F_132,B_130,C_129] :
      ( m1_subset_1(k1_partfun1(A_133,B_130,C_129,D_134,E_131,F_132),k1_zfmisc_1(k2_zfmisc_1(A_133,D_134)))
      | ~ m1_subset_1(F_132,k1_zfmisc_1(k2_zfmisc_1(C_129,D_134)))
      | ~ v1_funct_1(F_132)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_133,B_130)))
      | ~ v1_funct_1(E_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ! [A_30] : m1_subset_1(k6_partfun1(A_30),k1_zfmisc_1(k2_zfmisc_1(A_30,A_30))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_44,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_384,plain,(
    ! [D_85,C_86,A_87,B_88] :
      ( D_85 = C_86
      | ~ r2_relset_1(A_87,B_88,C_86,D_85)
      | ~ m1_subset_1(D_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88)))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_394,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_44,c_384])).

tff(c_413,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_394])).

tff(c_414,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_699,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_693,c_414])).

tff(c_724,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_56,c_52,c_699])).

tff(c_725,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_939,plain,(
    ! [C_169,E_166,A_167,F_168,B_165,D_164] :
      ( k1_partfun1(A_167,B_165,C_169,D_164,E_166,F_168) = k5_relat_1(E_166,F_168)
      | ~ m1_subset_1(F_168,k1_zfmisc_1(k2_zfmisc_1(C_169,D_164)))
      | ~ v1_funct_1(F_168)
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(A_167,B_165)))
      | ~ v1_funct_1(E_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_957,plain,(
    ! [A_167,B_165,E_166] :
      ( k1_partfun1(A_167,B_165,'#skF_1','#skF_2',E_166,'#skF_3') = k5_relat_1(E_166,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(A_167,B_165)))
      | ~ v1_funct_1(E_166) ) ),
    inference(resolution,[status(thm)],[c_52,c_939])).

tff(c_1135,plain,(
    ! [A_196,B_197,E_198] :
      ( k1_partfun1(A_196,B_197,'#skF_1','#skF_2',E_198,'#skF_3') = k5_relat_1(E_198,'#skF_3')
      | ~ m1_subset_1(E_198,k1_zfmisc_1(k2_zfmisc_1(A_196,B_197)))
      | ~ v1_funct_1(E_198) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_957])).

tff(c_1160,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1135])).

tff(c_1172,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_725,c_1160])).

tff(c_16,plain,(
    ! [A_10,B_12] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_10,B_12)),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1182,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_2')),k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1172,c_16])).

tff(c_1189,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_148,c_57,c_1182])).

tff(c_1191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_1189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.74  
% 3.37/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.74  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.37/1.74  
% 3.37/1.74  %Foreground sorts:
% 3.37/1.74  
% 3.37/1.74  
% 3.37/1.74  %Background operators:
% 3.37/1.74  
% 3.37/1.74  
% 3.37/1.74  %Foreground operators:
% 3.37/1.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.37/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.37/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.74  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.37/1.74  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.37/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.37/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.37/1.74  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.37/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.37/1.74  tff('#skF_2', type, '#skF_2': $i).
% 3.37/1.74  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.37/1.74  tff('#skF_3', type, '#skF_3': $i).
% 3.37/1.74  tff('#skF_1', type, '#skF_1': $i).
% 3.37/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.37/1.74  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.37/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.37/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.37/1.74  tff('#skF_4', type, '#skF_4': $i).
% 3.37/1.74  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.37/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.37/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.37/1.74  
% 3.39/1.75  tff(f_117, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 3.39/1.75  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.39/1.75  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.39/1.75  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.39/1.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.39/1.75  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.39/1.75  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.39/1.75  tff(f_99, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.39/1.75  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.39/1.75  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.39/1.75  tff(f_87, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 3.39/1.75  tff(f_71, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.39/1.75  tff(f_97, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.39/1.75  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 3.39/1.75  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.39/1.75  tff(c_211, plain, (![A_68, B_69, C_70]: (k2_relset_1(A_68, B_69, C_70)=k2_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.39/1.75  tff(c_229, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_211])).
% 3.39/1.75  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.39/1.75  tff(c_230, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_229, c_42])).
% 3.39/1.75  tff(c_297, plain, (![A_81, B_82, C_83]: (m1_subset_1(k2_relset_1(A_81, B_82, C_83), k1_zfmisc_1(B_82)) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.39/1.75  tff(c_319, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_229, c_297])).
% 3.39/1.75  tff(c_329, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_319])).
% 3.39/1.75  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.39/1.75  tff(c_372, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_329, c_8])).
% 3.39/1.75  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.75  tff(c_377, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_372, c_2])).
% 3.39/1.75  tff(c_381, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_230, c_377])).
% 3.39/1.75  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.39/1.75  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.39/1.75  tff(c_126, plain, (![B_54, A_55]: (v1_relat_1(B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_55)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.39/1.75  tff(c_135, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_126])).
% 3.39/1.75  tff(c_145, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_135])).
% 3.39/1.75  tff(c_138, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_126])).
% 3.39/1.75  tff(c_148, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_138])).
% 3.39/1.75  tff(c_40, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.39/1.75  tff(c_20, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.39/1.75  tff(c_57, plain, (![A_13]: (k2_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_20])).
% 3.39/1.75  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.39/1.75  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.39/1.75  tff(c_693, plain, (![A_133, D_134, E_131, F_132, B_130, C_129]: (m1_subset_1(k1_partfun1(A_133, B_130, C_129, D_134, E_131, F_132), k1_zfmisc_1(k2_zfmisc_1(A_133, D_134))) | ~m1_subset_1(F_132, k1_zfmisc_1(k2_zfmisc_1(C_129, D_134))) | ~v1_funct_1(F_132) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_133, B_130))) | ~v1_funct_1(E_131))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.39/1.75  tff(c_36, plain, (![A_30]: (m1_subset_1(k6_partfun1(A_30), k1_zfmisc_1(k2_zfmisc_1(A_30, A_30))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.39/1.76  tff(c_44, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.39/1.76  tff(c_384, plain, (![D_85, C_86, A_87, B_88]: (D_85=C_86 | ~r2_relset_1(A_87, B_88, C_86, D_85) | ~m1_subset_1(D_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.39/1.76  tff(c_394, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_44, c_384])).
% 3.39/1.76  tff(c_413, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_394])).
% 3.39/1.76  tff(c_414, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_413])).
% 3.39/1.76  tff(c_699, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_693, c_414])).
% 3.39/1.76  tff(c_724, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_56, c_52, c_699])).
% 3.39/1.76  tff(c_725, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_413])).
% 3.39/1.76  tff(c_939, plain, (![C_169, E_166, A_167, F_168, B_165, D_164]: (k1_partfun1(A_167, B_165, C_169, D_164, E_166, F_168)=k5_relat_1(E_166, F_168) | ~m1_subset_1(F_168, k1_zfmisc_1(k2_zfmisc_1(C_169, D_164))) | ~v1_funct_1(F_168) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(A_167, B_165))) | ~v1_funct_1(E_166))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.39/1.76  tff(c_957, plain, (![A_167, B_165, E_166]: (k1_partfun1(A_167, B_165, '#skF_1', '#skF_2', E_166, '#skF_3')=k5_relat_1(E_166, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(A_167, B_165))) | ~v1_funct_1(E_166))), inference(resolution, [status(thm)], [c_52, c_939])).
% 3.39/1.76  tff(c_1135, plain, (![A_196, B_197, E_198]: (k1_partfun1(A_196, B_197, '#skF_1', '#skF_2', E_198, '#skF_3')=k5_relat_1(E_198, '#skF_3') | ~m1_subset_1(E_198, k1_zfmisc_1(k2_zfmisc_1(A_196, B_197))) | ~v1_funct_1(E_198))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_957])).
% 3.39/1.76  tff(c_1160, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1135])).
% 3.39/1.76  tff(c_1172, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_725, c_1160])).
% 3.39/1.76  tff(c_16, plain, (![A_10, B_12]: (r1_tarski(k2_relat_1(k5_relat_1(A_10, B_12)), k2_relat_1(B_12)) | ~v1_relat_1(B_12) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.39/1.76  tff(c_1182, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_2')), k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1172, c_16])).
% 3.39/1.76  tff(c_1189, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_148, c_57, c_1182])).
% 3.39/1.76  tff(c_1191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_1189])).
% 3.39/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.76  
% 3.39/1.76  Inference rules
% 3.39/1.76  ----------------------
% 3.39/1.76  #Ref     : 0
% 3.39/1.76  #Sup     : 242
% 3.39/1.76  #Fact    : 0
% 3.39/1.76  #Define  : 0
% 3.39/1.76  #Split   : 7
% 3.39/1.76  #Chain   : 0
% 3.39/1.76  #Close   : 0
% 3.39/1.76  
% 3.39/1.76  Ordering : KBO
% 3.39/1.76  
% 3.39/1.76  Simplification rules
% 3.39/1.76  ----------------------
% 3.39/1.76  #Subsume      : 13
% 3.39/1.76  #Demod        : 117
% 3.39/1.76  #Tautology    : 62
% 3.39/1.76  #SimpNegUnit  : 3
% 3.39/1.76  #BackRed      : 2
% 3.39/1.76  
% 3.39/1.76  #Partial instantiations: 0
% 3.39/1.76  #Strategies tried      : 1
% 3.39/1.76  
% 3.39/1.76  Timing (in seconds)
% 3.39/1.76  ----------------------
% 3.39/1.76  Preprocessing        : 0.44
% 3.39/1.76  Parsing              : 0.28
% 3.39/1.76  CNF conversion       : 0.02
% 3.39/1.76  Main loop            : 0.45
% 3.39/1.76  Inferencing          : 0.17
% 3.39/1.76  Reduction            : 0.15
% 3.39/1.76  Demodulation         : 0.11
% 3.39/1.76  BG Simplification    : 0.02
% 3.39/1.76  Subsumption          : 0.08
% 3.39/1.76  Abstraction          : 0.03
% 3.39/1.76  MUC search           : 0.00
% 3.39/1.76  Cooper               : 0.00
% 3.39/1.76  Total                : 0.93
% 3.39/1.76  Index Insertion      : 0.00
% 3.39/1.76  Index Deletion       : 0.00
% 3.39/1.76  Index Matching       : 0.00
% 3.39/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
