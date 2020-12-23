%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:18 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 127 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 223 expanded)
%              Number of equality atoms :   24 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_171,plain,(
    ! [A_54,B_55,C_56] :
      ( k1_relset_1(A_54,B_55,C_56) = k1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_175,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_171])).

tff(c_28,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_64,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_176,plain,(
    k1_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_64])).

tff(c_10,plain,(
    ! [A_4] : k2_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ! [C_25,A_26,B_27] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_56,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_52])).

tff(c_65,plain,(
    ! [C_32,A_33,B_34] :
      ( v4_relat_1(C_32,A_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_69,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_65])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k1_relat_1(B_2),A_1)
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_199,plain,(
    ! [C_65,A_66,B_67,D_68] :
      ( r1_tarski(C_65,k1_relset_1(A_66,B_67,D_68))
      | ~ r1_tarski(k6_relat_1(C_65),D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_203,plain,(
    ! [A_69,B_70] :
      ( r1_tarski('#skF_2',k1_relset_1(A_69,B_70,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(resolution,[status(thm)],[c_30,c_199])).

tff(c_206,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_203])).

tff(c_208,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_206])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4] : k1_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_105,plain,(
    ! [A_46,B_47] :
      ( k5_relat_1(k6_relat_1(A_46),B_47) = B_47
      | ~ r1_tarski(k1_relat_1(B_47),A_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_111,plain,(
    ! [A_46,A_4] :
      ( k5_relat_1(k6_relat_1(A_46),k6_relat_1(A_4)) = k6_relat_1(A_4)
      | ~ r1_tarski(A_4,A_46)
      | ~ v1_relat_1(k6_relat_1(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_105])).

tff(c_135,plain,(
    ! [A_50,A_51] :
      ( k5_relat_1(k6_relat_1(A_50),k6_relat_1(A_51)) = k6_relat_1(A_51)
      | ~ r1_tarski(A_51,A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_111])).

tff(c_90,plain,(
    ! [B_42,A_43] :
      ( k5_relat_1(B_42,k6_relat_1(A_43)) = B_42
      | ~ r1_tarski(k2_relat_1(B_42),A_43)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_93,plain,(
    ! [A_4,A_43] :
      ( k5_relat_1(k6_relat_1(A_4),k6_relat_1(A_43)) = k6_relat_1(A_4)
      | ~ r1_tarski(A_4,A_43)
      | ~ v1_relat_1(k6_relat_1(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_95,plain,(
    ! [A_4,A_43] :
      ( k5_relat_1(k6_relat_1(A_4),k6_relat_1(A_43)) = k6_relat_1(A_4)
      | ~ r1_tarski(A_4,A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_93])).

tff(c_144,plain,(
    ! [A_51,A_50] :
      ( k6_relat_1(A_51) = k6_relat_1(A_50)
      | ~ r1_tarski(A_50,A_51)
      | ~ r1_tarski(A_51,A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_95])).

tff(c_211,plain,
    ( k6_relat_1(k1_relat_1('#skF_3')) = k6_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_208,c_144])).

tff(c_212,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_211])).

tff(c_215,plain,
    ( ~ v4_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_212])).

tff(c_219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_69,c_215])).

tff(c_220,plain,(
    k6_relat_1(k1_relat_1('#skF_3')) = k6_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_211])).

tff(c_270,plain,(
    k2_relat_1(k6_relat_1('#skF_2')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_10])).

tff(c_281,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_270])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_281])).

tff(c_284,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_502,plain,(
    ! [C_110,A_111,B_112,D_113] :
      ( r1_tarski(C_110,k2_relset_1(A_111,B_112,D_113))
      | ~ r1_tarski(k6_relat_1(C_110),D_113)
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_506,plain,(
    ! [A_114,B_115] :
      ( r1_tarski('#skF_2',k2_relset_1(A_114,B_115,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(resolution,[status(thm)],[c_30,c_502])).

tff(c_509,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_506])).

tff(c_513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_509])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:18:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.37  
% 2.57/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.38  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.57/1.38  
% 2.57/1.38  %Foreground sorts:
% 2.57/1.38  
% 2.57/1.38  
% 2.57/1.38  %Background operators:
% 2.57/1.38  
% 2.57/1.38  
% 2.57/1.38  %Foreground operators:
% 2.57/1.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.57/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.57/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.57/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.57/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.57/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.57/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.57/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.57/1.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.57/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.57/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.57/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.57/1.38  
% 2.57/1.39  tff(f_80, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relset_1)).
% 2.57/1.39  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.57/1.39  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.57/1.39  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.57/1.39  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.57/1.39  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.57/1.39  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 2.57/1.39  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.57/1.39  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.57/1.39  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.57/1.39  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.39  tff(c_171, plain, (![A_54, B_55, C_56]: (k1_relset_1(A_54, B_55, C_56)=k1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.57/1.39  tff(c_175, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_171])).
% 2.57/1.39  tff(c_28, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.39  tff(c_64, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_28])).
% 2.57/1.39  tff(c_176, plain, (k1_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_175, c_64])).
% 2.57/1.39  tff(c_10, plain, (![A_4]: (k2_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.57/1.39  tff(c_52, plain, (![C_25, A_26, B_27]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.57/1.39  tff(c_56, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_52])).
% 2.57/1.39  tff(c_65, plain, (![C_32, A_33, B_34]: (v4_relat_1(C_32, A_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.57/1.39  tff(c_69, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_65])).
% 2.57/1.39  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k1_relat_1(B_2), A_1) | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.57/1.39  tff(c_30, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.57/1.39  tff(c_199, plain, (![C_65, A_66, B_67, D_68]: (r1_tarski(C_65, k1_relset_1(A_66, B_67, D_68)) | ~r1_tarski(k6_relat_1(C_65), D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.57/1.39  tff(c_203, plain, (![A_69, B_70]: (r1_tarski('#skF_2', k1_relset_1(A_69, B_70, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(resolution, [status(thm)], [c_30, c_199])).
% 2.57/1.39  tff(c_206, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_203])).
% 2.57/1.39  tff(c_208, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_206])).
% 2.57/1.39  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.39  tff(c_8, plain, (![A_4]: (k1_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.57/1.39  tff(c_105, plain, (![A_46, B_47]: (k5_relat_1(k6_relat_1(A_46), B_47)=B_47 | ~r1_tarski(k1_relat_1(B_47), A_46) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.57/1.39  tff(c_111, plain, (![A_46, A_4]: (k5_relat_1(k6_relat_1(A_46), k6_relat_1(A_4))=k6_relat_1(A_4) | ~r1_tarski(A_4, A_46) | ~v1_relat_1(k6_relat_1(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_105])).
% 2.57/1.39  tff(c_135, plain, (![A_50, A_51]: (k5_relat_1(k6_relat_1(A_50), k6_relat_1(A_51))=k6_relat_1(A_51) | ~r1_tarski(A_51, A_50))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_111])).
% 2.57/1.39  tff(c_90, plain, (![B_42, A_43]: (k5_relat_1(B_42, k6_relat_1(A_43))=B_42 | ~r1_tarski(k2_relat_1(B_42), A_43) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.57/1.39  tff(c_93, plain, (![A_4, A_43]: (k5_relat_1(k6_relat_1(A_4), k6_relat_1(A_43))=k6_relat_1(A_4) | ~r1_tarski(A_4, A_43) | ~v1_relat_1(k6_relat_1(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_90])).
% 2.57/1.39  tff(c_95, plain, (![A_4, A_43]: (k5_relat_1(k6_relat_1(A_4), k6_relat_1(A_43))=k6_relat_1(A_4) | ~r1_tarski(A_4, A_43))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_93])).
% 2.57/1.39  tff(c_144, plain, (![A_51, A_50]: (k6_relat_1(A_51)=k6_relat_1(A_50) | ~r1_tarski(A_50, A_51) | ~r1_tarski(A_51, A_50))), inference(superposition, [status(thm), theory('equality')], [c_135, c_95])).
% 2.57/1.39  tff(c_211, plain, (k6_relat_1(k1_relat_1('#skF_3'))=k6_relat_1('#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_208, c_144])).
% 2.57/1.39  tff(c_212, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_211])).
% 2.57/1.39  tff(c_215, plain, (~v4_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_212])).
% 2.57/1.39  tff(c_219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_69, c_215])).
% 2.57/1.39  tff(c_220, plain, (k6_relat_1(k1_relat_1('#skF_3'))=k6_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_211])).
% 2.57/1.39  tff(c_270, plain, (k2_relat_1(k6_relat_1('#skF_2'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_220, c_10])).
% 2.57/1.39  tff(c_281, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_270])).
% 2.57/1.39  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_281])).
% 2.57/1.39  tff(c_284, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_28])).
% 2.57/1.39  tff(c_502, plain, (![C_110, A_111, B_112, D_113]: (r1_tarski(C_110, k2_relset_1(A_111, B_112, D_113)) | ~r1_tarski(k6_relat_1(C_110), D_113) | ~m1_subset_1(D_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.57/1.39  tff(c_506, plain, (![A_114, B_115]: (r1_tarski('#skF_2', k2_relset_1(A_114, B_115, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(resolution, [status(thm)], [c_30, c_502])).
% 2.57/1.39  tff(c_509, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_506])).
% 2.57/1.39  tff(c_513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_509])).
% 2.57/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.39  
% 2.57/1.39  Inference rules
% 2.57/1.39  ----------------------
% 2.57/1.39  #Ref     : 0
% 2.57/1.39  #Sup     : 104
% 2.57/1.39  #Fact    : 0
% 2.57/1.39  #Define  : 0
% 2.57/1.39  #Split   : 5
% 2.57/1.39  #Chain   : 0
% 2.57/1.39  #Close   : 0
% 2.57/1.39  
% 2.57/1.39  Ordering : KBO
% 2.57/1.39  
% 2.57/1.39  Simplification rules
% 2.57/1.39  ----------------------
% 2.57/1.39  #Subsume      : 8
% 2.57/1.39  #Demod        : 41
% 2.57/1.39  #Tautology    : 40
% 2.57/1.39  #SimpNegUnit  : 2
% 2.57/1.39  #BackRed      : 1
% 2.57/1.39  
% 2.57/1.39  #Partial instantiations: 0
% 2.57/1.39  #Strategies tried      : 1
% 2.57/1.39  
% 2.57/1.39  Timing (in seconds)
% 2.57/1.39  ----------------------
% 2.57/1.40  Preprocessing        : 0.31
% 2.57/1.40  Parsing              : 0.17
% 2.57/1.40  CNF conversion       : 0.02
% 2.57/1.40  Main loop            : 0.28
% 2.57/1.40  Inferencing          : 0.11
% 2.57/1.40  Reduction            : 0.08
% 2.57/1.40  Demodulation         : 0.06
% 2.57/1.40  BG Simplification    : 0.02
% 2.57/1.40  Subsumption          : 0.05
% 2.57/1.40  Abstraction          : 0.02
% 2.57/1.40  MUC search           : 0.00
% 2.57/1.40  Cooper               : 0.00
% 2.57/1.40  Total                : 0.62
% 2.57/1.40  Index Insertion      : 0.00
% 2.57/1.40  Index Deletion       : 0.00
% 2.57/1.40  Index Matching       : 0.00
% 2.57/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
