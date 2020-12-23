%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:54 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.46s
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
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_18,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

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
    ! [A_15] :
      ( r1_tarski(k7_relat_1('#skF_3',A_15),'#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_79])).

tff(c_92,plain,(
    ! [A_40] : r1_tarski(k7_relat_1('#skF_3',A_40),'#skF_4') ),
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
      ( v1_relat_1(k7_relat_1('#skF_3',A_40))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_92,c_39])).

tff(c_101,plain,(
    ! [A_40] : v1_relat_1(k7_relat_1('#skF_3',A_40)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_97])).

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_74,plain,(
    ! [B_37,A_38] :
      ( k7_relat_1(B_37,A_38) = B_37
      | ~ r1_tarski(k1_relat_1(B_37),A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_335,plain,(
    ! [B_86,A_87] :
      ( k7_relat_1(k7_relat_1(B_86,A_87),A_87) = k7_relat_1(B_86,A_87)
      | ~ v1_relat_1(k7_relat_1(B_86,A_87))
      | ~ v1_relat_1(B_86) ) ),
    inference(resolution,[status(thm)],[c_12,c_74])).

tff(c_341,plain,(
    ! [A_40] :
      ( k7_relat_1(k7_relat_1('#skF_3',A_40),A_40) = k7_relat_1('#skF_3',A_40)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_101,c_335])).

tff(c_354,plain,(
    ! [A_88] : k7_relat_1(k7_relat_1('#skF_3',A_88),A_88) = k7_relat_1('#skF_3',A_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_341])).

tff(c_422,plain,(
    ! [A_88] :
      ( r1_tarski(k7_relat_1('#skF_3',A_88),k7_relat_1('#skF_3',A_88))
      | ~ v1_relat_1(k7_relat_1('#skF_3',A_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_14])).

tff(c_572,plain,(
    ! [A_91] : r1_tarski(k7_relat_1('#skF_3',A_91),k7_relat_1('#skF_3',A_91)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_422])).

tff(c_71,plain,(
    ! [A_34,B_16,A_15] :
      ( r1_tarski(A_34,B_16)
      | ~ r1_tarski(A_34,k7_relat_1(B_16,A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_14,c_61])).

tff(c_575,plain,(
    ! [A_91] :
      ( r1_tarski(k7_relat_1('#skF_3',A_91),'#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_572,c_71])).

tff(c_588,plain,(
    ! [A_91] : r1_tarski(k7_relat_1('#skF_3',A_91),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_575])).

tff(c_419,plain,(
    ! [A_88] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_88)),A_88)
      | ~ v1_relat_1(k7_relat_1('#skF_3',A_88)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_12])).

tff(c_517,plain,(
    ! [A_90] : r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_90)),A_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_419])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_103,plain,(
    ! [A_42] :
      ( r1_tarski(A_42,'#skF_2')
      | ~ r1_tarski(A_42,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_61])).

tff(c_16,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_113,plain,(
    ! [B_18] :
      ( k7_relat_1(B_18,'#skF_2') = B_18
      | ~ v1_relat_1(B_18)
      | ~ r1_tarski(k1_relat_1(B_18),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_103,c_16])).

tff(c_537,plain,
    ( k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') = k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_517,c_113])).

tff(c_562,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') = k7_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_537])).

tff(c_10,plain,(
    ! [B_10,A_9,C_12] :
      ( r1_tarski(k7_relat_1(B_10,A_9),k7_relat_1(C_12,A_9))
      | ~ r1_tarski(B_10,C_12)
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_155,plain,(
    ! [B_51,A_52,C_53] :
      ( r1_tarski(k7_relat_1(B_51,A_52),k7_relat_1(C_53,A_52))
      | ~ r1_tarski(B_51,C_53)
      | ~ v1_relat_1(C_53)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_616,plain,(
    ! [A_95,C_96,A_97,B_98] :
      ( r1_tarski(A_95,k7_relat_1(C_96,A_97))
      | ~ r1_tarski(A_95,k7_relat_1(B_98,A_97))
      | ~ r1_tarski(B_98,C_96)
      | ~ v1_relat_1(C_96)
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_2184,plain,(
    ! [B_144,A_145,C_146,C_147] :
      ( r1_tarski(k7_relat_1(B_144,A_145),k7_relat_1(C_146,A_145))
      | ~ r1_tarski(C_147,C_146)
      | ~ v1_relat_1(C_146)
      | ~ r1_tarski(B_144,C_147)
      | ~ v1_relat_1(C_147)
      | ~ v1_relat_1(B_144) ) ),
    inference(resolution,[status(thm)],[c_10,c_616])).

tff(c_2266,plain,(
    ! [B_144,A_145] :
      ( r1_tarski(k7_relat_1(B_144,A_145),k7_relat_1('#skF_4',A_145))
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(B_144,'#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_144) ) ),
    inference(resolution,[status(thm)],[c_22,c_2184])).

tff(c_2423,plain,(
    ! [B_152,A_153] :
      ( r1_tarski(k7_relat_1(B_152,A_153),k7_relat_1('#skF_4',A_153))
      | ~ r1_tarski(B_152,'#skF_3')
      | ~ v1_relat_1(B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_2266])).

tff(c_2447,plain,
    ( r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_562,c_2423])).

tff(c_2468,plain,(
    r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_588,c_2447])).

tff(c_2470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_2468])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:06:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.78  
% 4.09/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.09/1.78  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.09/1.78  
% 4.09/1.78  %Foreground sorts:
% 4.09/1.78  
% 4.09/1.78  
% 4.09/1.78  %Background operators:
% 4.09/1.78  
% 4.09/1.78  
% 4.09/1.78  %Foreground operators:
% 4.09/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.78  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.09/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/1.78  tff('#skF_2', type, '#skF_2': $i).
% 4.09/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.09/1.78  tff('#skF_1', type, '#skF_1': $i).
% 4.09/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.09/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.09/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.09/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.09/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.09/1.78  
% 4.46/1.79  tff(f_77, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_relat_1)).
% 4.46/1.79  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 4.46/1.79  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.46/1.79  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.46/1.79  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.46/1.79  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 4.46/1.79  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 4.46/1.79  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_relat_1)).
% 4.46/1.79  tff(c_18, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.46/1.79  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.46/1.79  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.46/1.79  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.46/1.79  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.46/1.79  tff(c_61, plain, (![A_34, C_35, B_36]: (r1_tarski(A_34, C_35) | ~r1_tarski(B_36, C_35) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.46/1.79  tff(c_79, plain, (![A_39]: (r1_tarski(A_39, '#skF_4') | ~r1_tarski(A_39, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_61])).
% 4.46/1.79  tff(c_87, plain, (![A_15]: (r1_tarski(k7_relat_1('#skF_3', A_15), '#skF_4') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_79])).
% 4.46/1.79  tff(c_92, plain, (![A_40]: (r1_tarski(k7_relat_1('#skF_3', A_40), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_87])).
% 4.46/1.79  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.46/1.79  tff(c_35, plain, (![B_28, A_29]: (v1_relat_1(B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_29)) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.46/1.79  tff(c_39, plain, (![A_4, B_5]: (v1_relat_1(A_4) | ~v1_relat_1(B_5) | ~r1_tarski(A_4, B_5))), inference(resolution, [status(thm)], [c_6, c_35])).
% 4.46/1.79  tff(c_97, plain, (![A_40]: (v1_relat_1(k7_relat_1('#skF_3', A_40)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_92, c_39])).
% 4.46/1.79  tff(c_101, plain, (![A_40]: (v1_relat_1(k7_relat_1('#skF_3', A_40)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_97])).
% 4.46/1.79  tff(c_12, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.46/1.79  tff(c_74, plain, (![B_37, A_38]: (k7_relat_1(B_37, A_38)=B_37 | ~r1_tarski(k1_relat_1(B_37), A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.46/1.79  tff(c_335, plain, (![B_86, A_87]: (k7_relat_1(k7_relat_1(B_86, A_87), A_87)=k7_relat_1(B_86, A_87) | ~v1_relat_1(k7_relat_1(B_86, A_87)) | ~v1_relat_1(B_86))), inference(resolution, [status(thm)], [c_12, c_74])).
% 4.46/1.79  tff(c_341, plain, (![A_40]: (k7_relat_1(k7_relat_1('#skF_3', A_40), A_40)=k7_relat_1('#skF_3', A_40) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_101, c_335])).
% 4.46/1.79  tff(c_354, plain, (![A_88]: (k7_relat_1(k7_relat_1('#skF_3', A_88), A_88)=k7_relat_1('#skF_3', A_88))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_341])).
% 4.46/1.79  tff(c_422, plain, (![A_88]: (r1_tarski(k7_relat_1('#skF_3', A_88), k7_relat_1('#skF_3', A_88)) | ~v1_relat_1(k7_relat_1('#skF_3', A_88)))), inference(superposition, [status(thm), theory('equality')], [c_354, c_14])).
% 4.46/1.79  tff(c_572, plain, (![A_91]: (r1_tarski(k7_relat_1('#skF_3', A_91), k7_relat_1('#skF_3', A_91)))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_422])).
% 4.46/1.79  tff(c_71, plain, (![A_34, B_16, A_15]: (r1_tarski(A_34, B_16) | ~r1_tarski(A_34, k7_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_14, c_61])).
% 4.46/1.79  tff(c_575, plain, (![A_91]: (r1_tarski(k7_relat_1('#skF_3', A_91), '#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_572, c_71])).
% 4.46/1.79  tff(c_588, plain, (![A_91]: (r1_tarski(k7_relat_1('#skF_3', A_91), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_575])).
% 4.46/1.79  tff(c_419, plain, (![A_88]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_88)), A_88) | ~v1_relat_1(k7_relat_1('#skF_3', A_88)))), inference(superposition, [status(thm), theory('equality')], [c_354, c_12])).
% 4.46/1.79  tff(c_517, plain, (![A_90]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_90)), A_90))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_419])).
% 4.46/1.79  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.46/1.79  tff(c_103, plain, (![A_42]: (r1_tarski(A_42, '#skF_2') | ~r1_tarski(A_42, '#skF_1'))), inference(resolution, [status(thm)], [c_20, c_61])).
% 4.46/1.79  tff(c_16, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~r1_tarski(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.46/1.79  tff(c_113, plain, (![B_18]: (k7_relat_1(B_18, '#skF_2')=B_18 | ~v1_relat_1(B_18) | ~r1_tarski(k1_relat_1(B_18), '#skF_1'))), inference(resolution, [status(thm)], [c_103, c_16])).
% 4.46/1.79  tff(c_537, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_517, c_113])).
% 4.46/1.79  tff(c_562, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')=k7_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_537])).
% 4.46/1.79  tff(c_10, plain, (![B_10, A_9, C_12]: (r1_tarski(k7_relat_1(B_10, A_9), k7_relat_1(C_12, A_9)) | ~r1_tarski(B_10, C_12) | ~v1_relat_1(C_12) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.46/1.79  tff(c_155, plain, (![B_51, A_52, C_53]: (r1_tarski(k7_relat_1(B_51, A_52), k7_relat_1(C_53, A_52)) | ~r1_tarski(B_51, C_53) | ~v1_relat_1(C_53) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.46/1.79  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.46/1.79  tff(c_616, plain, (![A_95, C_96, A_97, B_98]: (r1_tarski(A_95, k7_relat_1(C_96, A_97)) | ~r1_tarski(A_95, k7_relat_1(B_98, A_97)) | ~r1_tarski(B_98, C_96) | ~v1_relat_1(C_96) | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_155, c_2])).
% 4.46/1.79  tff(c_2184, plain, (![B_144, A_145, C_146, C_147]: (r1_tarski(k7_relat_1(B_144, A_145), k7_relat_1(C_146, A_145)) | ~r1_tarski(C_147, C_146) | ~v1_relat_1(C_146) | ~r1_tarski(B_144, C_147) | ~v1_relat_1(C_147) | ~v1_relat_1(B_144))), inference(resolution, [status(thm)], [c_10, c_616])).
% 4.46/1.79  tff(c_2266, plain, (![B_144, A_145]: (r1_tarski(k7_relat_1(B_144, A_145), k7_relat_1('#skF_4', A_145)) | ~v1_relat_1('#skF_4') | ~r1_tarski(B_144, '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_144))), inference(resolution, [status(thm)], [c_22, c_2184])).
% 4.46/1.79  tff(c_2423, plain, (![B_152, A_153]: (r1_tarski(k7_relat_1(B_152, A_153), k7_relat_1('#skF_4', A_153)) | ~r1_tarski(B_152, '#skF_3') | ~v1_relat_1(B_152))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_2266])).
% 4.46/1.79  tff(c_2447, plain, (r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_562, c_2423])).
% 4.46/1.79  tff(c_2468, plain, (r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_588, c_2447])).
% 4.46/1.79  tff(c_2470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_2468])).
% 4.46/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.46/1.79  
% 4.46/1.79  Inference rules
% 4.46/1.79  ----------------------
% 4.46/1.79  #Ref     : 0
% 4.46/1.79  #Sup     : 513
% 4.46/1.79  #Fact    : 0
% 4.46/1.79  #Define  : 0
% 4.46/1.79  #Split   : 4
% 4.46/1.79  #Chain   : 0
% 4.46/1.79  #Close   : 0
% 4.46/1.79  
% 4.46/1.79  Ordering : KBO
% 4.46/1.79  
% 4.46/1.79  Simplification rules
% 4.46/1.79  ----------------------
% 4.46/1.79  #Subsume      : 75
% 4.46/1.79  #Demod        : 370
% 4.46/1.79  #Tautology    : 118
% 4.46/1.79  #SimpNegUnit  : 1
% 4.46/1.79  #BackRed      : 0
% 4.46/1.79  
% 4.46/1.79  #Partial instantiations: 0
% 4.46/1.79  #Strategies tried      : 1
% 4.46/1.79  
% 4.46/1.79  Timing (in seconds)
% 4.46/1.79  ----------------------
% 4.46/1.80  Preprocessing        : 0.29
% 4.46/1.80  Parsing              : 0.16
% 4.46/1.80  CNF conversion       : 0.02
% 4.46/1.80  Main loop            : 0.74
% 4.46/1.80  Inferencing          : 0.24
% 4.46/1.80  Reduction            : 0.26
% 4.46/1.80  Demodulation         : 0.20
% 4.46/1.80  BG Simplification    : 0.03
% 4.46/1.80  Subsumption          : 0.16
% 4.46/1.80  Abstraction          : 0.03
% 4.46/1.80  MUC search           : 0.00
% 4.46/1.80  Cooper               : 0.00
% 4.46/1.80  Total                : 1.06
% 4.46/1.80  Index Insertion      : 0.00
% 4.46/1.80  Index Deletion       : 0.00
% 4.46/1.80  Index Matching       : 0.00
% 4.46/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
