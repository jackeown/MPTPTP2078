%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:26 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 117 expanded)
%              Number of leaves         :   28 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   93 ( 195 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_47,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_38])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,A_6)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k7_relat_1(B_9,A_8),B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_174,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( m1_subset_1(A_66,k1_zfmisc_1(k2_zfmisc_1(B_67,C_68)))
      | ~ r1_tarski(A_66,D_69)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(B_67,C_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_427,plain,(
    ! [B_120,A_121,B_122,C_123] :
      ( m1_subset_1(k7_relat_1(B_120,A_121),k1_zfmisc_1(k2_zfmisc_1(B_122,C_123)))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_zfmisc_1(B_122,C_123)))
      | ~ v1_relat_1(B_120) ) ),
    inference(resolution,[status(thm)],[c_10,c_174])).

tff(c_16,plain,(
    ! [A_16,B_17,C_18] :
      ( k2_relset_1(A_16,B_17,C_18) = k2_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_876,plain,(
    ! [B_214,C_215,B_216,A_217] :
      ( k2_relset_1(B_214,C_215,k7_relat_1(B_216,A_217)) = k2_relat_1(k7_relat_1(B_216,A_217))
      | ~ m1_subset_1(B_216,k1_zfmisc_1(k2_zfmisc_1(B_214,C_215)))
      | ~ v1_relat_1(B_216) ) ),
    inference(resolution,[status(thm)],[c_427,c_16])).

tff(c_890,plain,(
    ! [A_217] :
      ( k2_relset_1('#skF_1','#skF_3',k7_relat_1('#skF_4',A_217)) = k2_relat_1(k7_relat_1('#skF_4',A_217))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_876])).

tff(c_899,plain,(
    ! [A_218] : k2_relset_1('#skF_1','#skF_3',k7_relat_1('#skF_4',A_218)) = k2_relat_1(k7_relat_1('#skF_4',A_218)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_890])).

tff(c_110,plain,(
    ! [A_58,B_59,C_60] :
      ( m1_subset_1(k2_relset_1(A_58,B_59,C_60),k1_zfmisc_1(B_59))
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [A_58,B_59,C_60] :
      ( r1_tarski(k2_relset_1(A_58,B_59,C_60),B_59)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_456,plain,(
    ! [B_122,C_123,B_120,A_121] :
      ( r1_tarski(k2_relset_1(B_122,C_123,k7_relat_1(B_120,A_121)),C_123)
      | ~ m1_subset_1(B_120,k1_zfmisc_1(k2_zfmisc_1(B_122,C_123)))
      | ~ v1_relat_1(B_120) ) ),
    inference(resolution,[status(thm)],[c_427,c_131])).

tff(c_911,plain,(
    ! [A_218] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_218)),'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_899,c_456])).

tff(c_925,plain,(
    ! [A_218] : r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_218)),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_26,c_911])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_79,plain,(
    ! [A_46,B_47] :
      ( v1_relat_1(A_46)
      | ~ v1_relat_1(B_47)
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_4,c_69])).

tff(c_92,plain,(
    ! [B_9,A_8] :
      ( v1_relat_1(k7_relat_1(B_9,A_8))
      | ~ v1_relat_1(B_9) ) ),
    inference(resolution,[status(thm)],[c_10,c_79])).

tff(c_276,plain,(
    ! [C_85,A_86,B_87] :
      ( m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ r1_tarski(k2_relat_1(C_85),B_87)
      | ~ r1_tarski(k1_relat_1(C_85),A_86)
      | ~ v1_relat_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_147,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( k5_relset_1(A_61,B_62,C_63,D_64) = k7_relat_1(C_63,D_64)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_158,plain,(
    ! [D_64] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_64) = k7_relat_1('#skF_4',D_64) ),
    inference(resolution,[status(thm)],[c_26,c_147])).

tff(c_24,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_160,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_24])).

tff(c_301,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_276,c_160])).

tff(c_397,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_400,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_397])).

tff(c_404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_400])).

tff(c_405,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_407,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_405])).

tff(c_929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_925,c_407])).

tff(c_930,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_405])).

tff(c_935,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_930])).

tff(c_939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_935])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.55  
% 3.28/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.56  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.28/1.56  
% 3.28/1.56  %Foreground sorts:
% 3.28/1.56  
% 3.28/1.56  
% 3.28/1.56  %Background operators:
% 3.28/1.56  
% 3.28/1.56  
% 3.28/1.56  %Foreground operators:
% 3.28/1.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.28/1.56  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 3.28/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.28/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.28/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.28/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.28/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.56  
% 3.34/1.57  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 3.34/1.57  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.34/1.57  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 3.34/1.57  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 3.34/1.57  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_relset_1)).
% 3.34/1.57  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.34/1.57  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.34/1.57  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.34/1.57  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.34/1.57  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 3.34/1.57  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 3.34/1.57  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.34/1.57  tff(c_38, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.34/1.57  tff(c_47, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_38])).
% 3.34/1.57  tff(c_8, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, A_6)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.34/1.57  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k7_relat_1(B_9, A_8), B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.34/1.57  tff(c_174, plain, (![A_66, B_67, C_68, D_69]: (m1_subset_1(A_66, k1_zfmisc_1(k2_zfmisc_1(B_67, C_68))) | ~r1_tarski(A_66, D_69) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(B_67, C_68))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.34/1.57  tff(c_427, plain, (![B_120, A_121, B_122, C_123]: (m1_subset_1(k7_relat_1(B_120, A_121), k1_zfmisc_1(k2_zfmisc_1(B_122, C_123))) | ~m1_subset_1(B_120, k1_zfmisc_1(k2_zfmisc_1(B_122, C_123))) | ~v1_relat_1(B_120))), inference(resolution, [status(thm)], [c_10, c_174])).
% 3.34/1.57  tff(c_16, plain, (![A_16, B_17, C_18]: (k2_relset_1(A_16, B_17, C_18)=k2_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.34/1.57  tff(c_876, plain, (![B_214, C_215, B_216, A_217]: (k2_relset_1(B_214, C_215, k7_relat_1(B_216, A_217))=k2_relat_1(k7_relat_1(B_216, A_217)) | ~m1_subset_1(B_216, k1_zfmisc_1(k2_zfmisc_1(B_214, C_215))) | ~v1_relat_1(B_216))), inference(resolution, [status(thm)], [c_427, c_16])).
% 3.34/1.57  tff(c_890, plain, (![A_217]: (k2_relset_1('#skF_1', '#skF_3', k7_relat_1('#skF_4', A_217))=k2_relat_1(k7_relat_1('#skF_4', A_217)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_876])).
% 3.34/1.57  tff(c_899, plain, (![A_218]: (k2_relset_1('#skF_1', '#skF_3', k7_relat_1('#skF_4', A_218))=k2_relat_1(k7_relat_1('#skF_4', A_218)))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_890])).
% 3.34/1.57  tff(c_110, plain, (![A_58, B_59, C_60]: (m1_subset_1(k2_relset_1(A_58, B_59, C_60), k1_zfmisc_1(B_59)) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.34/1.57  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.34/1.57  tff(c_131, plain, (![A_58, B_59, C_60]: (r1_tarski(k2_relset_1(A_58, B_59, C_60), B_59) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(resolution, [status(thm)], [c_110, c_2])).
% 3.34/1.57  tff(c_456, plain, (![B_122, C_123, B_120, A_121]: (r1_tarski(k2_relset_1(B_122, C_123, k7_relat_1(B_120, A_121)), C_123) | ~m1_subset_1(B_120, k1_zfmisc_1(k2_zfmisc_1(B_122, C_123))) | ~v1_relat_1(B_120))), inference(resolution, [status(thm)], [c_427, c_131])).
% 3.34/1.57  tff(c_911, plain, (![A_218]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_218)), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_899, c_456])).
% 3.34/1.57  tff(c_925, plain, (![A_218]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_218)), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_26, c_911])).
% 3.34/1.57  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.34/1.57  tff(c_69, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.34/1.57  tff(c_79, plain, (![A_46, B_47]: (v1_relat_1(A_46) | ~v1_relat_1(B_47) | ~r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_4, c_69])).
% 3.34/1.57  tff(c_92, plain, (![B_9, A_8]: (v1_relat_1(k7_relat_1(B_9, A_8)) | ~v1_relat_1(B_9))), inference(resolution, [status(thm)], [c_10, c_79])).
% 3.34/1.57  tff(c_276, plain, (![C_85, A_86, B_87]: (m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~r1_tarski(k2_relat_1(C_85), B_87) | ~r1_tarski(k1_relat_1(C_85), A_86) | ~v1_relat_1(C_85))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.34/1.57  tff(c_147, plain, (![A_61, B_62, C_63, D_64]: (k5_relset_1(A_61, B_62, C_63, D_64)=k7_relat_1(C_63, D_64) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.34/1.57  tff(c_158, plain, (![D_64]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_64)=k7_relat_1('#skF_4', D_64))), inference(resolution, [status(thm)], [c_26, c_147])).
% 3.34/1.57  tff(c_24, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.34/1.57  tff(c_160, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_24])).
% 3.34/1.57  tff(c_301, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_276, c_160])).
% 3.34/1.57  tff(c_397, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_301])).
% 3.34/1.57  tff(c_400, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_92, c_397])).
% 3.34/1.57  tff(c_404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_400])).
% 3.34/1.57  tff(c_405, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_301])).
% 3.34/1.57  tff(c_407, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_405])).
% 3.34/1.57  tff(c_929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_925, c_407])).
% 3.34/1.57  tff(c_930, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_405])).
% 3.34/1.57  tff(c_935, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_930])).
% 3.34/1.57  tff(c_939, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47, c_935])).
% 3.34/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.57  
% 3.34/1.57  Inference rules
% 3.34/1.57  ----------------------
% 3.34/1.57  #Ref     : 0
% 3.34/1.57  #Sup     : 203
% 3.34/1.57  #Fact    : 0
% 3.34/1.57  #Define  : 0
% 3.34/1.57  #Split   : 6
% 3.34/1.57  #Chain   : 0
% 3.34/1.57  #Close   : 0
% 3.34/1.57  
% 3.34/1.57  Ordering : KBO
% 3.34/1.57  
% 3.34/1.57  Simplification rules
% 3.34/1.57  ----------------------
% 3.34/1.57  #Subsume      : 33
% 3.34/1.57  #Demod        : 36
% 3.34/1.57  #Tautology    : 18
% 3.34/1.57  #SimpNegUnit  : 0
% 3.34/1.57  #BackRed      : 3
% 3.34/1.57  
% 3.34/1.57  #Partial instantiations: 0
% 3.34/1.57  #Strategies tried      : 1
% 3.34/1.57  
% 3.34/1.57  Timing (in seconds)
% 3.34/1.57  ----------------------
% 3.34/1.57  Preprocessing        : 0.31
% 3.34/1.57  Parsing              : 0.18
% 3.34/1.57  CNF conversion       : 0.02
% 3.34/1.57  Main loop            : 0.44
% 3.34/1.57  Inferencing          : 0.18
% 3.34/1.57  Reduction            : 0.11
% 3.34/1.57  Demodulation         : 0.07
% 3.34/1.57  BG Simplification    : 0.02
% 3.34/1.57  Subsumption          : 0.09
% 3.34/1.57  Abstraction          : 0.03
% 3.34/1.57  MUC search           : 0.00
% 3.34/1.57  Cooper               : 0.00
% 3.34/1.58  Total                : 0.78
% 3.34/1.58  Index Insertion      : 0.00
% 3.34/1.58  Index Deletion       : 0.00
% 3.34/1.58  Index Matching       : 0.00
% 3.34/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
