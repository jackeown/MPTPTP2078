%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:29 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 158 expanded)
%              Number of leaves         :   29 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :   99 ( 282 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_18,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_37,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_34,c_37])).

tff(c_43,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_40])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k7_relat_1(B_14,A_13),B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_160,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( m1_subset_1(A_99,k1_zfmisc_1(k2_zfmisc_1(B_100,C_101)))
      | ~ r1_tarski(A_99,D_102)
      | ~ m1_subset_1(D_102,k1_zfmisc_1(k2_zfmisc_1(B_100,C_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_244,plain,(
    ! [B_116,A_117,B_118,C_119] :
      ( m1_subset_1(k7_relat_1(B_116,A_117),k1_zfmisc_1(k2_zfmisc_1(B_118,C_119)))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k2_zfmisc_1(B_118,C_119)))
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_20,c_160])).

tff(c_22,plain,(
    ! [C_17,B_16,A_15] :
      ( v5_relat_1(C_17,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_390,plain,(
    ! [B_133,A_134,C_135,B_136] :
      ( v5_relat_1(k7_relat_1(B_133,A_134),C_135)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(k2_zfmisc_1(B_136,C_135)))
      | ~ v1_relat_1(B_133) ) ),
    inference(resolution,[status(thm)],[c_244,c_22])).

tff(c_396,plain,(
    ! [A_134] :
      ( v5_relat_1(k7_relat_1('#skF_4',A_134),'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_390])).

tff(c_401,plain,(
    ! [A_134] : v5_relat_1(k7_relat_1('#skF_4',A_134),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_396])).

tff(c_56,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_60,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_56])).

tff(c_16,plain,(
    ! [C_10,A_8,B_9] :
      ( v1_relat_1(k7_relat_1(C_10,A_8))
      | ~ v4_relat_1(C_10,B_9)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_62,plain,(
    ! [A_8] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_8))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_16])).

tff(c_65,plain,(
    ! [A_8] : v1_relat_1(k7_relat_1('#skF_4',A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_62])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_73,plain,(
    ! [C_53,A_54,B_55] :
      ( v4_relat_1(k7_relat_1(C_53,A_54),A_54)
      | ~ v4_relat_1(C_53,B_55)
      | ~ v1_relat_1(C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_75,plain,(
    ! [A_54] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_54),A_54)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_73])).

tff(c_78,plain,(
    ! [A_54] : v4_relat_1(k7_relat_1('#skF_4',A_54),A_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_75])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_220,plain,(
    ! [C_113,A_114,B_115] :
      ( m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ r1_tarski(k2_relat_1(C_113),B_115)
      | ~ r1_tarski(k1_relat_1(C_113),A_114)
      | ~ v1_relat_1(C_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_133,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( k5_relset_1(A_78,B_79,C_80,D_81) = k7_relat_1(C_80,D_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_136,plain,(
    ! [D_81] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_81) = k7_relat_1('#skF_4',D_81) ),
    inference(resolution,[status(thm)],[c_34,c_133])).

tff(c_32,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_137,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_32])).

tff(c_223,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_220,c_137])).

tff(c_237,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_223])).

tff(c_281,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_284,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_281])).

tff(c_288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_78,c_284])).

tff(c_289,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_302,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_289])).

tff(c_305,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_302])).

tff(c_404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.34  
% 2.55/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.35  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.55/1.35  
% 2.55/1.35  %Foreground sorts:
% 2.55/1.35  
% 2.55/1.35  
% 2.55/1.35  %Background operators:
% 2.55/1.35  
% 2.55/1.35  
% 2.55/1.35  %Foreground operators:
% 2.55/1.35  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.55/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.55/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.55/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.55/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.55/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.55/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.55/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.35  
% 2.55/1.36  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.55/1.36  tff(f_89, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 2.55/1.36  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.55/1.36  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 2.55/1.36  tff(f_84, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_relset_1)).
% 2.55/1.36  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.55/1.36  tff(f_54, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc23_relat_1)).
% 2.55/1.36  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.55/1.36  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.55/1.36  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.55/1.36  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.55/1.36  tff(c_18, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.55/1.36  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.55/1.36  tff(c_37, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.36  tff(c_40, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_34, c_37])).
% 2.55/1.36  tff(c_43, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_40])).
% 2.55/1.36  tff(c_20, plain, (![B_14, A_13]: (r1_tarski(k7_relat_1(B_14, A_13), B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.55/1.36  tff(c_160, plain, (![A_99, B_100, C_101, D_102]: (m1_subset_1(A_99, k1_zfmisc_1(k2_zfmisc_1(B_100, C_101))) | ~r1_tarski(A_99, D_102) | ~m1_subset_1(D_102, k1_zfmisc_1(k2_zfmisc_1(B_100, C_101))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.55/1.36  tff(c_244, plain, (![B_116, A_117, B_118, C_119]: (m1_subset_1(k7_relat_1(B_116, A_117), k1_zfmisc_1(k2_zfmisc_1(B_118, C_119))) | ~m1_subset_1(B_116, k1_zfmisc_1(k2_zfmisc_1(B_118, C_119))) | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_20, c_160])).
% 2.55/1.36  tff(c_22, plain, (![C_17, B_16, A_15]: (v5_relat_1(C_17, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.55/1.36  tff(c_390, plain, (![B_133, A_134, C_135, B_136]: (v5_relat_1(k7_relat_1(B_133, A_134), C_135) | ~m1_subset_1(B_133, k1_zfmisc_1(k2_zfmisc_1(B_136, C_135))) | ~v1_relat_1(B_133))), inference(resolution, [status(thm)], [c_244, c_22])).
% 2.55/1.36  tff(c_396, plain, (![A_134]: (v5_relat_1(k7_relat_1('#skF_4', A_134), '#skF_3') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_390])).
% 2.55/1.36  tff(c_401, plain, (![A_134]: (v5_relat_1(k7_relat_1('#skF_4', A_134), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_396])).
% 2.55/1.36  tff(c_56, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.55/1.36  tff(c_60, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_56])).
% 2.55/1.36  tff(c_16, plain, (![C_10, A_8, B_9]: (v1_relat_1(k7_relat_1(C_10, A_8)) | ~v4_relat_1(C_10, B_9) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.55/1.36  tff(c_62, plain, (![A_8]: (v1_relat_1(k7_relat_1('#skF_4', A_8)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_16])).
% 2.55/1.36  tff(c_65, plain, (![A_8]: (v1_relat_1(k7_relat_1('#skF_4', A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_62])).
% 2.55/1.36  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.55/1.36  tff(c_73, plain, (![C_53, A_54, B_55]: (v4_relat_1(k7_relat_1(C_53, A_54), A_54) | ~v4_relat_1(C_53, B_55) | ~v1_relat_1(C_53))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.55/1.36  tff(c_75, plain, (![A_54]: (v4_relat_1(k7_relat_1('#skF_4', A_54), A_54) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_73])).
% 2.55/1.36  tff(c_78, plain, (![A_54]: (v4_relat_1(k7_relat_1('#skF_4', A_54), A_54))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_75])).
% 2.55/1.36  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.55/1.36  tff(c_220, plain, (![C_113, A_114, B_115]: (m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~r1_tarski(k2_relat_1(C_113), B_115) | ~r1_tarski(k1_relat_1(C_113), A_114) | ~v1_relat_1(C_113))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.55/1.36  tff(c_133, plain, (![A_78, B_79, C_80, D_81]: (k5_relset_1(A_78, B_79, C_80, D_81)=k7_relat_1(C_80, D_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.55/1.36  tff(c_136, plain, (![D_81]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_81)=k7_relat_1('#skF_4', D_81))), inference(resolution, [status(thm)], [c_34, c_133])).
% 2.55/1.36  tff(c_32, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.55/1.36  tff(c_137, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_32])).
% 2.55/1.36  tff(c_223, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_220, c_137])).
% 2.55/1.36  tff(c_237, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_223])).
% 2.55/1.36  tff(c_281, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_237])).
% 2.55/1.36  tff(c_284, plain, (~v4_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_281])).
% 2.55/1.36  tff(c_288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_78, c_284])).
% 2.55/1.36  tff(c_289, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_237])).
% 2.55/1.36  tff(c_302, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_289])).
% 2.55/1.36  tff(c_305, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_302])).
% 2.55/1.36  tff(c_404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_401, c_305])).
% 2.55/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.36  
% 2.55/1.36  Inference rules
% 2.55/1.36  ----------------------
% 2.55/1.36  #Ref     : 0
% 2.55/1.36  #Sup     : 72
% 2.55/1.36  #Fact    : 0
% 2.55/1.36  #Define  : 0
% 2.55/1.36  #Split   : 2
% 2.55/1.36  #Chain   : 0
% 2.55/1.36  #Close   : 0
% 2.55/1.36  
% 2.55/1.36  Ordering : KBO
% 2.55/1.36  
% 2.55/1.36  Simplification rules
% 2.55/1.36  ----------------------
% 2.55/1.36  #Subsume      : 2
% 2.55/1.36  #Demod        : 78
% 2.55/1.36  #Tautology    : 21
% 2.55/1.36  #SimpNegUnit  : 0
% 2.55/1.36  #BackRed      : 2
% 2.55/1.36  
% 2.55/1.36  #Partial instantiations: 0
% 2.55/1.36  #Strategies tried      : 1
% 2.55/1.36  
% 2.55/1.36  Timing (in seconds)
% 2.55/1.36  ----------------------
% 2.55/1.37  Preprocessing        : 0.31
% 2.55/1.37  Parsing              : 0.18
% 2.55/1.37  CNF conversion       : 0.02
% 2.55/1.37  Main loop            : 0.25
% 2.55/1.37  Inferencing          : 0.09
% 2.55/1.37  Reduction            : 0.08
% 2.55/1.37  Demodulation         : 0.06
% 2.55/1.37  BG Simplification    : 0.01
% 2.55/1.37  Subsumption          : 0.04
% 2.55/1.37  Abstraction          : 0.01
% 2.55/1.37  MUC search           : 0.00
% 2.55/1.37  Cooper               : 0.00
% 2.55/1.37  Total                : 0.59
% 2.55/1.37  Index Insertion      : 0.00
% 2.55/1.37  Index Deletion       : 0.00
% 2.55/1.37  Index Matching       : 0.00
% 2.55/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
