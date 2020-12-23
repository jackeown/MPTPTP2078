%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:59 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 114 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 206 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_49,plain,(
    ! [B_27,A_28] :
      ( v1_relat_1(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28))
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_49])).

tff(c_55,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_52])).

tff(c_86,plain,(
    ! [C_43,B_44,A_45] :
      ( v5_relat_1(C_43,B_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_45,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_90,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_86])).

tff(c_26,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_76,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(k2_relat_1(B_39),A_40)
      | ~ v5_relat_1(B_39,A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_265,plain,(
    ! [B_58,A_59] :
      ( k2_xboole_0(k2_relat_1(B_58),A_59) = A_59
      | ~ v5_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_76,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_421,plain,(
    ! [B_73,C_74,A_75] :
      ( r1_tarski(k2_relat_1(B_73),C_74)
      | ~ r1_tarski(A_75,C_74)
      | ~ v5_relat_1(B_73,A_75)
      | ~ v1_relat_1(B_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_2])).

tff(c_460,plain,(
    ! [B_78] :
      ( r1_tarski(k2_relat_1(B_78),'#skF_4')
      | ~ v5_relat_1(B_78,'#skF_3')
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_26,c_421])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_91,plain,(
    ! [C_46,A_47,B_48] :
      ( v4_relat_1(C_46,A_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_95,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_91])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_98,plain,
    ( k7_relat_1('#skF_5','#skF_1') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_95,c_14])).

tff(c_101,plain,(
    k7_relat_1('#skF_5','#skF_1') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_98])).

tff(c_16,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_16,A_15)),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_105,plain,
    ( r1_tarski(k1_relat_1('#skF_5'),'#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_16])).

tff(c_109,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_105])).

tff(c_114,plain,(
    k2_xboole_0(k1_relat_1('#skF_5'),'#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_109,c_4])).

tff(c_118,plain,(
    ! [C_3] :
      ( r1_tarski(k1_relat_1('#skF_5'),C_3)
      | ~ r1_tarski('#skF_1',C_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_2])).

tff(c_122,plain,(
    ! [C_49,A_50,B_51] :
      ( m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ r1_tarski(k2_relat_1(C_49),B_51)
      | ~ r1_tarski(k1_relat_1(C_49),A_50)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_134,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_122,c_24])).

tff(c_142,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_134])).

tff(c_148,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_151,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_118,c_148])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_151])).

tff(c_156,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_471,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_460,c_156])).

tff(c_485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_90,c_471])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.34  
% 2.40/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.34  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.40/1.34  
% 2.40/1.34  %Foreground sorts:
% 2.40/1.34  
% 2.40/1.34  
% 2.40/1.34  %Background operators:
% 2.40/1.34  
% 2.40/1.34  
% 2.40/1.34  %Foreground operators:
% 2.40/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.34  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.40/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.40/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.40/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.40/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.40/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.40/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.40/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.40/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.40/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.40/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.34  
% 2.67/1.36  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.67/1.36  tff(f_81, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_relset_1)).
% 2.67/1.36  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.67/1.36  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.67/1.36  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.67/1.36  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.67/1.36  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.67/1.36  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.67/1.36  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.67/1.36  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.67/1.36  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.67/1.36  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.67/1.36  tff(c_49, plain, (![B_27, A_28]: (v1_relat_1(B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_28)) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.67/1.36  tff(c_52, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_49])).
% 2.67/1.36  tff(c_55, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_52])).
% 2.67/1.36  tff(c_86, plain, (![C_43, B_44, A_45]: (v5_relat_1(C_43, B_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_45, B_44))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.67/1.36  tff(c_90, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_86])).
% 2.67/1.36  tff(c_26, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.67/1.36  tff(c_76, plain, (![B_39, A_40]: (r1_tarski(k2_relat_1(B_39), A_40) | ~v5_relat_1(B_39, A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.67/1.36  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.36  tff(c_265, plain, (![B_58, A_59]: (k2_xboole_0(k2_relat_1(B_58), A_59)=A_59 | ~v5_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_76, c_4])).
% 2.67/1.36  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.67/1.36  tff(c_421, plain, (![B_73, C_74, A_75]: (r1_tarski(k2_relat_1(B_73), C_74) | ~r1_tarski(A_75, C_74) | ~v5_relat_1(B_73, A_75) | ~v1_relat_1(B_73))), inference(superposition, [status(thm), theory('equality')], [c_265, c_2])).
% 2.67/1.36  tff(c_460, plain, (![B_78]: (r1_tarski(k2_relat_1(B_78), '#skF_4') | ~v5_relat_1(B_78, '#skF_3') | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_26, c_421])).
% 2.67/1.36  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.67/1.36  tff(c_91, plain, (![C_46, A_47, B_48]: (v4_relat_1(C_46, A_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.67/1.36  tff(c_95, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_91])).
% 2.67/1.36  tff(c_14, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.67/1.36  tff(c_98, plain, (k7_relat_1('#skF_5', '#skF_1')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_95, c_14])).
% 2.67/1.36  tff(c_101, plain, (k7_relat_1('#skF_5', '#skF_1')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_55, c_98])).
% 2.67/1.36  tff(c_16, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(k7_relat_1(B_16, A_15)), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.67/1.36  tff(c_105, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_101, c_16])).
% 2.67/1.36  tff(c_109, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_105])).
% 2.67/1.36  tff(c_114, plain, (k2_xboole_0(k1_relat_1('#skF_5'), '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_109, c_4])).
% 2.67/1.36  tff(c_118, plain, (![C_3]: (r1_tarski(k1_relat_1('#skF_5'), C_3) | ~r1_tarski('#skF_1', C_3))), inference(superposition, [status(thm), theory('equality')], [c_114, c_2])).
% 2.67/1.36  tff(c_122, plain, (![C_49, A_50, B_51]: (m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~r1_tarski(k2_relat_1(C_49), B_51) | ~r1_tarski(k1_relat_1(C_49), A_50) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.67/1.36  tff(c_24, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.67/1.36  tff(c_134, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_122, c_24])).
% 2.67/1.36  tff(c_142, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_134])).
% 2.67/1.36  tff(c_148, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_142])).
% 2.67/1.36  tff(c_151, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_118, c_148])).
% 2.67/1.36  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_151])).
% 2.67/1.36  tff(c_156, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_142])).
% 2.67/1.36  tff(c_471, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_460, c_156])).
% 2.67/1.36  tff(c_485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_90, c_471])).
% 2.67/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.36  
% 2.67/1.36  Inference rules
% 2.67/1.36  ----------------------
% 2.67/1.36  #Ref     : 0
% 2.67/1.36  #Sup     : 111
% 2.67/1.36  #Fact    : 0
% 2.67/1.36  #Define  : 0
% 2.67/1.36  #Split   : 5
% 2.67/1.36  #Chain   : 0
% 2.67/1.36  #Close   : 0
% 2.67/1.36  
% 2.67/1.36  Ordering : KBO
% 2.67/1.36  
% 2.67/1.36  Simplification rules
% 2.67/1.36  ----------------------
% 2.67/1.36  #Subsume      : 12
% 2.67/1.36  #Demod        : 32
% 2.67/1.36  #Tautology    : 42
% 2.67/1.36  #SimpNegUnit  : 2
% 2.67/1.36  #BackRed      : 2
% 2.67/1.36  
% 2.67/1.36  #Partial instantiations: 0
% 2.67/1.36  #Strategies tried      : 1
% 2.67/1.36  
% 2.67/1.36  Timing (in seconds)
% 2.67/1.36  ----------------------
% 2.67/1.36  Preprocessing        : 0.28
% 2.67/1.36  Parsing              : 0.16
% 2.67/1.36  CNF conversion       : 0.02
% 2.67/1.36  Main loop            : 0.28
% 2.67/1.36  Inferencing          : 0.11
% 2.67/1.36  Reduction            : 0.08
% 2.67/1.36  Demodulation         : 0.05
% 2.67/1.36  BG Simplification    : 0.01
% 2.67/1.36  Subsumption          : 0.05
% 2.67/1.36  Abstraction          : 0.01
% 2.67/1.36  MUC search           : 0.00
% 2.67/1.36  Cooper               : 0.00
% 2.67/1.36  Total                : 0.59
% 2.67/1.36  Index Insertion      : 0.00
% 2.67/1.36  Index Deletion       : 0.00
% 2.67/1.36  Index Matching       : 0.00
% 2.67/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
