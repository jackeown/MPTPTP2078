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
% DateTime   : Thu Dec  3 10:17:05 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 165 expanded)
%              Number of leaves         :   20 (  63 expanded)
%              Depth                    :    9
%              Number of atoms          :   91 ( 427 expanded)
%              Number of equality atoms :   32 ( 217 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k5_partfun1(A,B,k3_partfun1(C,A,B)) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k3_partfun1(C,A,B) = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
      <=> k5_partfun1(A,B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => v1_partfun1(k3_partfun1(C,A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_funct_2)).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [C_10,A_11,B_12] :
      ( k3_partfun1(C_10,A_11,B_12) = C_10
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12)))
      | ~ v1_funct_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_25,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_22])).

tff(c_28,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_25])).

tff(c_12,plain,(
    k5_partfun1('#skF_1','#skF_2',k3_partfun1('#skF_3','#skF_1','#skF_2')) != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_29,plain,(
    k5_partfun1('#skF_1','#skF_2','#skF_3') != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12])).

tff(c_34,plain,(
    ! [A_13,B_14,C_15] :
      ( k5_partfun1(A_13,B_14,C_15) = k1_tarski(C_15)
      | ~ v1_partfun1(C_15,A_13)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14)))
      | ~ v1_funct_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_37,plain,
    ( k5_partfun1('#skF_1','#skF_2','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_34])).

tff(c_40,plain,
    ( k5_partfun1('#skF_1','#skF_2','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_37])).

tff(c_41,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_40])).

tff(c_14,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_21,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_18,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_51,plain,(
    ! [B_21,C_22,A_23] :
      ( k1_xboole_0 = B_21
      | v1_partfun1(k3_partfun1(C_22,A_23,B_21),A_23)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_23,B_21)))
      | ~ v1_funct_2(C_22,A_23,B_21)
      | ~ v1_funct_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1(k3_partfun1('#skF_3','#skF_1','#skF_2'),'#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_51])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_28,c_53])).

tff(c_58,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_21,c_56])).

tff(c_59,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_60,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_65,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60])).

tff(c_71,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_16])).

tff(c_73,plain,(
    ! [C_24,A_25,B_26] :
      ( k3_partfun1(C_24,A_25,B_26) = C_24
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_76,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_73])).

tff(c_79,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_76])).

tff(c_72,plain,(
    k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_3','#skF_1','#skF_1')) != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_65,c_12])).

tff(c_80,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_3') != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_72])).

tff(c_92,plain,(
    ! [A_30,B_31,C_32] :
      ( k5_partfun1(A_30,B_31,C_32) = k1_tarski(C_32)
      | ~ v1_partfun1(C_32,A_30)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_95,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_92])).

tff(c_98,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_3') = k1_tarski('#skF_3')
    | ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_95])).

tff(c_99,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_98])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_18])).

tff(c_2,plain,(
    ! [C_3,B_2] :
      ( v1_partfun1(k3_partfun1(C_3,k1_xboole_0,B_2),k1_xboole_0)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_2(C_3,k1_xboole_0,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [C_33,B_34] :
      ( v1_partfun1(k3_partfun1(C_33,'#skF_1',B_34),'#skF_1')
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_34)))
      | ~ v1_funct_2(C_33,'#skF_1',B_34)
      | ~ v1_funct_1(C_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_59,c_59,c_59,c_2])).

tff(c_104,plain,
    ( v1_partfun1(k3_partfun1('#skF_3','#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_101])).

tff(c_107,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_66,c_79,c_104])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.19  
% 1.86/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.20  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.86/1.20  
% 1.86/1.20  %Foreground sorts:
% 1.86/1.20  
% 1.86/1.20  
% 1.86/1.20  %Background operators:
% 1.86/1.20  
% 1.86/1.20  
% 1.86/1.20  %Foreground operators:
% 1.86/1.20  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 1.86/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.86/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.86/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.20  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.86/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.86/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.20  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 1.86/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.86/1.20  
% 1.94/1.21  tff(f_64, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k5_partfun1(A, B, k3_partfun1(C, A, B)) = k1_tarski(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t161_funct_2)).
% 1.94/1.21  tff(f_51, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k3_partfun1(C, A, B) = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_partfun1)).
% 1.94/1.21  tff(f_45, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) <=> (k5_partfun1(A, B, C) = k1_tarski(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_partfun1)).
% 1.94/1.21  tff(f_37, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => v1_partfun1(k3_partfun1(C, A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_funct_2)).
% 1.94/1.21  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.21  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.21  tff(c_22, plain, (![C_10, A_11, B_12]: (k3_partfun1(C_10, A_11, B_12)=C_10 | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))) | ~v1_funct_1(C_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.94/1.21  tff(c_25, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_2')='#skF_3' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_22])).
% 1.94/1.21  tff(c_28, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_25])).
% 1.94/1.21  tff(c_12, plain, (k5_partfun1('#skF_1', '#skF_2', k3_partfun1('#skF_3', '#skF_1', '#skF_2'))!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.21  tff(c_29, plain, (k5_partfun1('#skF_1', '#skF_2', '#skF_3')!=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_12])).
% 1.94/1.21  tff(c_34, plain, (![A_13, B_14, C_15]: (k5_partfun1(A_13, B_14, C_15)=k1_tarski(C_15) | ~v1_partfun1(C_15, A_13) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))) | ~v1_funct_1(C_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.21  tff(c_37, plain, (k5_partfun1('#skF_1', '#skF_2', '#skF_3')=k1_tarski('#skF_3') | ~v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_34])).
% 1.94/1.21  tff(c_40, plain, (k5_partfun1('#skF_1', '#skF_2', '#skF_3')=k1_tarski('#skF_3') | ~v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_37])).
% 1.94/1.21  tff(c_41, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_29, c_40])).
% 1.94/1.21  tff(c_14, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.21  tff(c_21, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_14])).
% 1.94/1.21  tff(c_18, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.94/1.21  tff(c_51, plain, (![B_21, C_22, A_23]: (k1_xboole_0=B_21 | v1_partfun1(k3_partfun1(C_22, A_23, B_21), A_23) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_23, B_21))) | ~v1_funct_2(C_22, A_23, B_21) | ~v1_funct_1(C_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.94/1.21  tff(c_53, plain, (k1_xboole_0='#skF_2' | v1_partfun1(k3_partfun1('#skF_3', '#skF_1', '#skF_2'), '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_51])).
% 1.94/1.21  tff(c_56, plain, (k1_xboole_0='#skF_2' | v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_28, c_53])).
% 1.94/1.21  tff(c_58, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_21, c_56])).
% 1.94/1.21  tff(c_59, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_14])).
% 1.94/1.21  tff(c_60, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_14])).
% 1.94/1.21  tff(c_65, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59, c_60])).
% 1.94/1.21  tff(c_71, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_16])).
% 1.94/1.21  tff(c_73, plain, (![C_24, A_25, B_26]: (k3_partfun1(C_24, A_25, B_26)=C_24 | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.94/1.21  tff(c_76, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_73])).
% 1.94/1.21  tff(c_79, plain, (k3_partfun1('#skF_3', '#skF_1', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_76])).
% 1.94/1.21  tff(c_72, plain, (k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_3', '#skF_1', '#skF_1'))!=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_65, c_12])).
% 1.94/1.21  tff(c_80, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_3')!=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_72])).
% 1.94/1.21  tff(c_92, plain, (![A_30, B_31, C_32]: (k5_partfun1(A_30, B_31, C_32)=k1_tarski(C_32) | ~v1_partfun1(C_32, A_30) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_1(C_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.94/1.21  tff(c_95, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_3')=k1_tarski('#skF_3') | ~v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_92])).
% 1.94/1.21  tff(c_98, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_3')=k1_tarski('#skF_3') | ~v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_95])).
% 1.94/1.21  tff(c_99, plain, (~v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_80, c_98])).
% 1.94/1.21  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_18])).
% 1.94/1.21  tff(c_2, plain, (![C_3, B_2]: (v1_partfun1(k3_partfun1(C_3, k1_xboole_0, B_2), k1_xboole_0) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_2(C_3, k1_xboole_0, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.94/1.21  tff(c_101, plain, (![C_33, B_34]: (v1_partfun1(k3_partfun1(C_33, '#skF_1', B_34), '#skF_1') | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_34))) | ~v1_funct_2(C_33, '#skF_1', B_34) | ~v1_funct_1(C_33))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_59, c_59, c_59, c_2])).
% 1.94/1.21  tff(c_104, plain, (v1_partfun1(k3_partfun1('#skF_3', '#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_71, c_101])).
% 1.94/1.21  tff(c_107, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_66, c_79, c_104])).
% 1.94/1.21  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_107])).
% 1.94/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.21  
% 1.94/1.21  Inference rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Ref     : 0
% 1.94/1.21  #Sup     : 16
% 1.94/1.21  #Fact    : 0
% 1.94/1.21  #Define  : 0
% 1.94/1.21  #Split   : 1
% 1.94/1.21  #Chain   : 0
% 1.94/1.21  #Close   : 0
% 1.94/1.21  
% 1.94/1.21  Ordering : KBO
% 1.94/1.21  
% 1.94/1.21  Simplification rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Subsume      : 2
% 1.94/1.21  #Demod        : 23
% 1.94/1.21  #Tautology    : 8
% 1.94/1.21  #SimpNegUnit  : 5
% 1.94/1.21  #BackRed      : 3
% 1.94/1.21  
% 1.94/1.21  #Partial instantiations: 0
% 1.94/1.21  #Strategies tried      : 1
% 1.94/1.21  
% 1.94/1.21  Timing (in seconds)
% 1.94/1.21  ----------------------
% 1.94/1.21  Preprocessing        : 0.30
% 1.94/1.21  Parsing              : 0.17
% 1.94/1.21  CNF conversion       : 0.02
% 1.94/1.21  Main loop            : 0.12
% 1.94/1.21  Inferencing          : 0.04
% 1.94/1.21  Reduction            : 0.04
% 1.94/1.21  Demodulation         : 0.03
% 1.94/1.21  BG Simplification    : 0.01
% 1.94/1.21  Subsumption          : 0.02
% 1.94/1.21  Abstraction          : 0.01
% 1.94/1.21  MUC search           : 0.00
% 1.94/1.21  Cooper               : 0.00
% 1.94/1.21  Total                : 0.45
% 1.94/1.21  Index Insertion      : 0.00
% 1.94/1.21  Index Deletion       : 0.00
% 1.94/1.21  Index Matching       : 0.00
% 1.94/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
