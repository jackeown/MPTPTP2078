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
% DateTime   : Thu Dec  3 10:00:17 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 4.24s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 199 expanded)
%              Number of leaves         :   21 (  76 expanded)
%              Depth                    :   15
%              Number of atoms          :  119 ( 470 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k8_relat_1(A,B)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

tff(c_18,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(k8_relat_1(A_11,B_12),B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_61,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(A_34,C_35)
      | ~ r1_tarski(B_36,C_35)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_39] :
      ( r1_tarski(A_39,'#skF_4')
      | ~ r1_tarski(A_39,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_61])).

tff(c_87,plain,(
    ! [A_11] :
      ( r1_tarski(k8_relat_1(A_11,'#skF_3'),'#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_79])).

tff(c_92,plain,(
    ! [A_40] : r1_tarski(k8_relat_1(A_40,'#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_87])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_35,plain,(
    ! [B_28,A_29] :
      ( v1_relat_1(B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_29))
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_39,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(A_4)
      | ~ v1_relat_1(B_5)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_35])).

tff(c_97,plain,(
    ! [A_40] :
      ( v1_relat_1(k8_relat_1(A_40,'#skF_3'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_92,c_39])).

tff(c_101,plain,(
    ! [A_40] : v1_relat_1(k8_relat_1(A_40,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_97])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_9,B_10)),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_74,plain,(
    ! [A_37,B_38] :
      ( k8_relat_1(A_37,B_38) = B_38
      | ~ r1_tarski(k2_relat_1(B_38),A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_335,plain,(
    ! [A_86,B_87] :
      ( k8_relat_1(A_86,k8_relat_1(A_86,B_87)) = k8_relat_1(A_86,B_87)
      | ~ v1_relat_1(k8_relat_1(A_86,B_87))
      | ~ v1_relat_1(B_87) ) ),
    inference(resolution,[status(thm)],[c_10,c_74])).

tff(c_341,plain,(
    ! [A_40] :
      ( k8_relat_1(A_40,k8_relat_1(A_40,'#skF_3')) = k8_relat_1(A_40,'#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_101,c_335])).

tff(c_354,plain,(
    ! [A_88] : k8_relat_1(A_88,k8_relat_1(A_88,'#skF_3')) = k8_relat_1(A_88,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_341])).

tff(c_422,plain,(
    ! [A_88] :
      ( r1_tarski(k8_relat_1(A_88,'#skF_3'),k8_relat_1(A_88,'#skF_3'))
      | ~ v1_relat_1(k8_relat_1(A_88,'#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_12])).

tff(c_572,plain,(
    ! [A_91] : r1_tarski(k8_relat_1(A_91,'#skF_3'),k8_relat_1(A_91,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_422])).

tff(c_71,plain,(
    ! [A_34,B_12,A_11] :
      ( r1_tarski(A_34,B_12)
      | ~ r1_tarski(A_34,k8_relat_1(A_11,B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_12,c_61])).

tff(c_575,plain,(
    ! [A_91] :
      ( r1_tarski(k8_relat_1(A_91,'#skF_3'),'#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_572,c_71])).

tff(c_588,plain,(
    ! [A_91] : r1_tarski(k8_relat_1(A_91,'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_575])).

tff(c_419,plain,(
    ! [A_88] :
      ( r1_tarski(k2_relat_1(k8_relat_1(A_88,'#skF_3')),A_88)
      | ~ v1_relat_1(k8_relat_1(A_88,'#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_10])).

tff(c_517,plain,(
    ! [A_90] : r1_tarski(k2_relat_1(k8_relat_1(A_90,'#skF_3')),A_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_419])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_103,plain,(
    ! [A_42] :
      ( r1_tarski(A_42,'#skF_2')
      | ~ r1_tarski(A_42,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_61])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k8_relat_1(A_13,B_14) = B_14
      | ~ r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_113,plain,(
    ! [B_14] :
      ( k8_relat_1('#skF_2',B_14) = B_14
      | ~ v1_relat_1(B_14)
      | ~ r1_tarski(k2_relat_1(B_14),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_103,c_14])).

tff(c_537,plain,
    ( k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) = k8_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_517,c_113])).

tff(c_562,plain,(
    k8_relat_1('#skF_2',k8_relat_1('#skF_1','#skF_3')) = k8_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_537])).

tff(c_16,plain,(
    ! [A_15,B_16,C_18] :
      ( r1_tarski(k8_relat_1(A_15,B_16),k8_relat_1(A_15,C_18))
      | ~ r1_tarski(B_16,C_18)
      | ~ v1_relat_1(C_18)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_155,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_tarski(k8_relat_1(A_51,B_52),k8_relat_1(A_51,C_53))
      | ~ r1_tarski(B_52,C_53)
      | ~ v1_relat_1(C_53)
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_616,plain,(
    ! [A_95,A_96,C_97,B_98] :
      ( r1_tarski(A_95,k8_relat_1(A_96,C_97))
      | ~ r1_tarski(A_95,k8_relat_1(A_96,B_98))
      | ~ r1_tarski(B_98,C_97)
      | ~ v1_relat_1(C_97)
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_2184,plain,(
    ! [A_144,B_145,C_146,C_147] :
      ( r1_tarski(k8_relat_1(A_144,B_145),k8_relat_1(A_144,C_146))
      | ~ r1_tarski(C_147,C_146)
      | ~ v1_relat_1(C_146)
      | ~ r1_tarski(B_145,C_147)
      | ~ v1_relat_1(C_147)
      | ~ v1_relat_1(B_145) ) ),
    inference(resolution,[status(thm)],[c_16,c_616])).

tff(c_2266,plain,(
    ! [A_144,B_145] :
      ( r1_tarski(k8_relat_1(A_144,B_145),k8_relat_1(A_144,'#skF_4'))
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(B_145,'#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_145) ) ),
    inference(resolution,[status(thm)],[c_22,c_2184])).

tff(c_2423,plain,(
    ! [A_152,B_153] :
      ( r1_tarski(k8_relat_1(A_152,B_153),k8_relat_1(A_152,'#skF_4'))
      | ~ r1_tarski(B_153,'#skF_3')
      | ~ v1_relat_1(B_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_2266])).

tff(c_2447,plain,
    ( r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_2423])).

tff(c_2468,plain,(
    r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_588,c_2447])).

tff(c_2470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_2468])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:50:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.89/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.69  
% 3.89/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.70  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.89/1.70  
% 3.89/1.70  %Foreground sorts:
% 3.89/1.70  
% 3.89/1.70  
% 3.89/1.70  %Background operators:
% 3.89/1.70  
% 3.89/1.70  
% 3.89/1.70  %Foreground operators:
% 3.89/1.70  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.89/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.89/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.89/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.89/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.89/1.70  tff('#skF_1', type, '#skF_1': $i).
% 3.89/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.89/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.89/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.89/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.89/1.70  
% 4.24/1.71  tff(f_77, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_relat_1)).
% 4.24/1.71  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 4.24/1.71  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.24/1.71  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.24/1.71  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.24/1.71  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k8_relat_1(A, B)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_relat_1)).
% 4.24/1.71  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 4.24/1.71  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_relat_1)).
% 4.24/1.71  tff(c_18, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.24/1.71  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.24/1.71  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.24/1.71  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(k8_relat_1(A_11, B_12), B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.24/1.71  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.24/1.71  tff(c_61, plain, (![A_34, C_35, B_36]: (r1_tarski(A_34, C_35) | ~r1_tarski(B_36, C_35) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.24/1.71  tff(c_79, plain, (![A_39]: (r1_tarski(A_39, '#skF_4') | ~r1_tarski(A_39, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_61])).
% 4.24/1.71  tff(c_87, plain, (![A_11]: (r1_tarski(k8_relat_1(A_11, '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_12, c_79])).
% 4.24/1.71  tff(c_92, plain, (![A_40]: (r1_tarski(k8_relat_1(A_40, '#skF_3'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_87])).
% 4.24/1.71  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.24/1.71  tff(c_35, plain, (![B_28, A_29]: (v1_relat_1(B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_29)) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.24/1.71  tff(c_39, plain, (![A_4, B_5]: (v1_relat_1(A_4) | ~v1_relat_1(B_5) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_35])).
% 4.24/1.71  tff(c_97, plain, (![A_40]: (v1_relat_1(k8_relat_1(A_40, '#skF_3')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_92, c_39])).
% 4.24/1.71  tff(c_101, plain, (![A_40]: (v1_relat_1(k8_relat_1(A_40, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_97])).
% 4.24/1.71  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k2_relat_1(k8_relat_1(A_9, B_10)), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.24/1.71  tff(c_74, plain, (![A_37, B_38]: (k8_relat_1(A_37, B_38)=B_38 | ~r1_tarski(k2_relat_1(B_38), A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.24/1.71  tff(c_335, plain, (![A_86, B_87]: (k8_relat_1(A_86, k8_relat_1(A_86, B_87))=k8_relat_1(A_86, B_87) | ~v1_relat_1(k8_relat_1(A_86, B_87)) | ~v1_relat_1(B_87))), inference(resolution, [status(thm)], [c_10, c_74])).
% 4.24/1.71  tff(c_341, plain, (![A_40]: (k8_relat_1(A_40, k8_relat_1(A_40, '#skF_3'))=k8_relat_1(A_40, '#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_101, c_335])).
% 4.24/1.71  tff(c_354, plain, (![A_88]: (k8_relat_1(A_88, k8_relat_1(A_88, '#skF_3'))=k8_relat_1(A_88, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_341])).
% 4.24/1.71  tff(c_422, plain, (![A_88]: (r1_tarski(k8_relat_1(A_88, '#skF_3'), k8_relat_1(A_88, '#skF_3')) | ~v1_relat_1(k8_relat_1(A_88, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_354, c_12])).
% 4.24/1.71  tff(c_572, plain, (![A_91]: (r1_tarski(k8_relat_1(A_91, '#skF_3'), k8_relat_1(A_91, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_422])).
% 4.24/1.71  tff(c_71, plain, (![A_34, B_12, A_11]: (r1_tarski(A_34, B_12) | ~r1_tarski(A_34, k8_relat_1(A_11, B_12)) | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_12, c_61])).
% 4.24/1.71  tff(c_575, plain, (![A_91]: (r1_tarski(k8_relat_1(A_91, '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_572, c_71])).
% 4.24/1.71  tff(c_588, plain, (![A_91]: (r1_tarski(k8_relat_1(A_91, '#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_575])).
% 4.24/1.71  tff(c_419, plain, (![A_88]: (r1_tarski(k2_relat_1(k8_relat_1(A_88, '#skF_3')), A_88) | ~v1_relat_1(k8_relat_1(A_88, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_354, c_10])).
% 4.24/1.71  tff(c_517, plain, (![A_90]: (r1_tarski(k2_relat_1(k8_relat_1(A_90, '#skF_3')), A_90))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_419])).
% 4.24/1.71  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.24/1.71  tff(c_103, plain, (![A_42]: (r1_tarski(A_42, '#skF_2') | ~r1_tarski(A_42, '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_61])).
% 4.24/1.71  tff(c_14, plain, (![A_13, B_14]: (k8_relat_1(A_13, B_14)=B_14 | ~r1_tarski(k2_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.24/1.71  tff(c_113, plain, (![B_14]: (k8_relat_1('#skF_2', B_14)=B_14 | ~v1_relat_1(B_14) | ~r1_tarski(k2_relat_1(B_14), '#skF_1'))), inference(resolution, [status(thm)], [c_103, c_14])).
% 4.24/1.71  tff(c_537, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))=k8_relat_1('#skF_1', '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_517, c_113])).
% 4.24/1.71  tff(c_562, plain, (k8_relat_1('#skF_2', k8_relat_1('#skF_1', '#skF_3'))=k8_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_537])).
% 4.24/1.71  tff(c_16, plain, (![A_15, B_16, C_18]: (r1_tarski(k8_relat_1(A_15, B_16), k8_relat_1(A_15, C_18)) | ~r1_tarski(B_16, C_18) | ~v1_relat_1(C_18) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.24/1.71  tff(c_155, plain, (![A_51, B_52, C_53]: (r1_tarski(k8_relat_1(A_51, B_52), k8_relat_1(A_51, C_53)) | ~r1_tarski(B_52, C_53) | ~v1_relat_1(C_53) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.24/1.71  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.24/1.71  tff(c_616, plain, (![A_95, A_96, C_97, B_98]: (r1_tarski(A_95, k8_relat_1(A_96, C_97)) | ~r1_tarski(A_95, k8_relat_1(A_96, B_98)) | ~r1_tarski(B_98, C_97) | ~v1_relat_1(C_97) | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_155, c_2])).
% 4.24/1.71  tff(c_2184, plain, (![A_144, B_145, C_146, C_147]: (r1_tarski(k8_relat_1(A_144, B_145), k8_relat_1(A_144, C_146)) | ~r1_tarski(C_147, C_146) | ~v1_relat_1(C_146) | ~r1_tarski(B_145, C_147) | ~v1_relat_1(C_147) | ~v1_relat_1(B_145))), inference(resolution, [status(thm)], [c_16, c_616])).
% 4.24/1.71  tff(c_2266, plain, (![A_144, B_145]: (r1_tarski(k8_relat_1(A_144, B_145), k8_relat_1(A_144, '#skF_4')) | ~v1_relat_1('#skF_4') | ~r1_tarski(B_145, '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_145))), inference(resolution, [status(thm)], [c_22, c_2184])).
% 4.24/1.71  tff(c_2423, plain, (![A_152, B_153]: (r1_tarski(k8_relat_1(A_152, B_153), k8_relat_1(A_152, '#skF_4')) | ~r1_tarski(B_153, '#skF_3') | ~v1_relat_1(B_153))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_2266])).
% 4.24/1.71  tff(c_2447, plain, (r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_4')) | ~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_3') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_562, c_2423])).
% 4.24/1.71  tff(c_2468, plain, (r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_588, c_2447])).
% 4.24/1.71  tff(c_2470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_2468])).
% 4.24/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/1.71  
% 4.24/1.71  Inference rules
% 4.24/1.71  ----------------------
% 4.24/1.71  #Ref     : 0
% 4.24/1.71  #Sup     : 513
% 4.24/1.71  #Fact    : 0
% 4.24/1.71  #Define  : 0
% 4.24/1.71  #Split   : 4
% 4.24/1.71  #Chain   : 0
% 4.24/1.71  #Close   : 0
% 4.24/1.71  
% 4.24/1.71  Ordering : KBO
% 4.24/1.71  
% 4.24/1.71  Simplification rules
% 4.24/1.71  ----------------------
% 4.24/1.71  #Subsume      : 75
% 4.24/1.71  #Demod        : 370
% 4.24/1.71  #Tautology    : 118
% 4.24/1.71  #SimpNegUnit  : 1
% 4.24/1.71  #BackRed      : 0
% 4.24/1.71  
% 4.24/1.71  #Partial instantiations: 0
% 4.24/1.71  #Strategies tried      : 1
% 4.24/1.71  
% 4.24/1.71  Timing (in seconds)
% 4.24/1.71  ----------------------
% 4.24/1.71  Preprocessing        : 0.27
% 4.24/1.71  Parsing              : 0.16
% 4.24/1.71  CNF conversion       : 0.02
% 4.24/1.71  Main loop            : 0.68
% 4.24/1.71  Inferencing          : 0.22
% 4.24/1.71  Reduction            : 0.24
% 4.24/1.71  Demodulation         : 0.18
% 4.24/1.71  BG Simplification    : 0.02
% 4.24/1.71  Subsumption          : 0.14
% 4.24/1.71  Abstraction          : 0.03
% 4.24/1.71  MUC search           : 0.00
% 4.24/1.71  Cooper               : 0.00
% 4.24/1.71  Total                : 0.98
% 4.24/1.71  Index Insertion      : 0.00
% 4.24/1.71  Index Deletion       : 0.00
% 4.24/1.72  Index Matching       : 0.00
% 4.24/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
