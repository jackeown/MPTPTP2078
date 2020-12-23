%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:06 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 213 expanded)
%              Number of leaves         :   21 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 ( 506 expanded)
%              Number of equality atoms :   17 ( 146 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => k5_partfun1(A,A,k3_partfun1(B,A,A)) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k3_partfun1(C,A,B) = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_partfun1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_partfun1(C,A)
      <=> k5_partfun1(A,B,C) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => v1_partfun1(k3_partfun1(C,A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_funct_2)).

tff(c_22,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_41,plain,(
    ! [C_16,A_17,B_18] :
      ( k3_partfun1(C_16,A_17,B_18) = C_16
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_funct_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_44,plain,
    ( k3_partfun1('#skF_2','#skF_1','#skF_1') = '#skF_2'
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_41])).

tff(c_47,plain,(
    k3_partfun1('#skF_2','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_44])).

tff(c_16,plain,(
    k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_2','#skF_1','#skF_1')) != k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_48,plain,(
    k5_partfun1('#skF_1','#skF_1','#skF_2') != k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_16])).

tff(c_60,plain,(
    ! [A_22,B_23,C_24] :
      ( k5_partfun1(A_22,B_23,C_24) = k1_tarski(C_24)
      | ~ v1_partfun1(C_24,A_22)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ v1_funct_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_2') = k1_tarski('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_60])).

tff(c_66,plain,
    ( k5_partfun1('#skF_1','#skF_1','#skF_2') = k1_tarski('#skF_2')
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_63])).

tff(c_67,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_66])).

tff(c_20,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_69,plain,(
    ! [B_27,C_28,A_29] :
      ( k1_xboole_0 = B_27
      | v1_partfun1(k3_partfun1(C_28,A_29,B_27),A_29)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_27)))
      | ~ v1_funct_2(C_28,A_29,B_27)
      | ~ v1_funct_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1(k3_partfun1('#skF_2','#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_69])).

tff(c_74,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_47,c_71])).

tff(c_75,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_74])).

tff(c_6,plain,(
    ! [C_6,B_5] :
      ( v1_partfun1(k3_partfun1(C_6,k1_xboole_0,B_5),k1_xboole_0)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5)))
      | ~ v1_funct_2(C_6,k1_xboole_0,B_5)
      | ~ v1_funct_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,(
    ! [C_30,B_31] :
      ( v1_partfun1(k3_partfun1(C_30,'#skF_1',B_31),'#skF_1')
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_31)))
      | ~ v1_funct_2(C_30,'#skF_1',B_31)
      | ~ v1_funct_1(C_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_75,c_75,c_75,c_6])).

tff(c_85,plain,
    ( v1_partfun1(k3_partfun1('#skF_2','#skF_1','#skF_1'),'#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_82])).

tff(c_88,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_47,c_85])).

tff(c_90,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.52  
% 2.18/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.53  %$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.18/1.53  
% 2.18/1.53  %Foreground sorts:
% 2.18/1.53  
% 2.18/1.53  
% 2.18/1.53  %Background operators:
% 2.18/1.53  
% 2.18/1.53  
% 2.18/1.53  %Foreground operators:
% 2.18/1.53  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 2.18/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.18/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.53  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.53  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.18/1.53  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.53  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 2.18/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.53  
% 2.25/1.55  tff(f_64, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k5_partfun1(A, A, k3_partfun1(B, A, A)) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_2)).
% 2.25/1.55  tff(f_55, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k3_partfun1(C, A, B) = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_partfun1)).
% 2.25/1.55  tff(f_49, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_partfun1(C, A) <=> (k5_partfun1(A, B, C) = k1_tarski(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_partfun1)).
% 2.25/1.55  tff(f_41, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => v1_partfun1(k3_partfun1(C, A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_funct_2)).
% 2.25/1.55  tff(c_22, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.25/1.55  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.25/1.55  tff(c_41, plain, (![C_16, A_17, B_18]: (k3_partfun1(C_16, A_17, B_18)=C_16 | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_funct_1(C_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.25/1.55  tff(c_44, plain, (k3_partfun1('#skF_2', '#skF_1', '#skF_1')='#skF_2' | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_41])).
% 2.25/1.55  tff(c_47, plain, (k3_partfun1('#skF_2', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_44])).
% 2.25/1.55  tff(c_16, plain, (k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_2', '#skF_1', '#skF_1'))!=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.25/1.55  tff(c_48, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')!=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_16])).
% 2.25/1.55  tff(c_60, plain, (![A_22, B_23, C_24]: (k5_partfun1(A_22, B_23, C_24)=k1_tarski(C_24) | ~v1_partfun1(C_24, A_22) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~v1_funct_1(C_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.25/1.55  tff(c_63, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')=k1_tarski('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_60])).
% 2.25/1.55  tff(c_66, plain, (k5_partfun1('#skF_1', '#skF_1', '#skF_2')=k1_tarski('#skF_2') | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_63])).
% 2.25/1.55  tff(c_67, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_48, c_66])).
% 2.25/1.55  tff(c_20, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.25/1.55  tff(c_69, plain, (![B_27, C_28, A_29]: (k1_xboole_0=B_27 | v1_partfun1(k3_partfun1(C_28, A_29, B_27), A_29) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_27))) | ~v1_funct_2(C_28, A_29, B_27) | ~v1_funct_1(C_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.25/1.55  tff(c_71, plain, (k1_xboole_0='#skF_1' | v1_partfun1(k3_partfun1('#skF_2', '#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_69])).
% 2.25/1.55  tff(c_74, plain, (k1_xboole_0='#skF_1' | v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_47, c_71])).
% 2.25/1.55  tff(c_75, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_67, c_74])).
% 2.25/1.55  tff(c_6, plain, (![C_6, B_5]: (v1_partfun1(k3_partfun1(C_6, k1_xboole_0, B_5), k1_xboole_0) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_5))) | ~v1_funct_2(C_6, k1_xboole_0, B_5) | ~v1_funct_1(C_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.25/1.55  tff(c_82, plain, (![C_30, B_31]: (v1_partfun1(k3_partfun1(C_30, '#skF_1', B_31), '#skF_1') | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_31))) | ~v1_funct_2(C_30, '#skF_1', B_31) | ~v1_funct_1(C_30))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_75, c_75, c_75, c_6])).
% 2.25/1.55  tff(c_85, plain, (v1_partfun1(k3_partfun1('#skF_2', '#skF_1', '#skF_1'), '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_82])).
% 2.25/1.55  tff(c_88, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_47, c_85])).
% 2.25/1.55  tff(c_90, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_88])).
% 2.25/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.55  
% 2.25/1.55  Inference rules
% 2.25/1.55  ----------------------
% 2.25/1.55  #Ref     : 0
% 2.25/1.55  #Sup     : 13
% 2.25/1.55  #Fact    : 0
% 2.25/1.55  #Define  : 0
% 2.25/1.55  #Split   : 0
% 2.25/1.55  #Chain   : 0
% 2.25/1.55  #Close   : 0
% 2.25/1.55  
% 2.25/1.55  Ordering : KBO
% 2.25/1.55  
% 2.25/1.55  Simplification rules
% 2.25/1.55  ----------------------
% 2.25/1.55  #Subsume      : 1
% 2.25/1.55  #Demod        : 15
% 2.25/1.55  #Tautology    : 8
% 2.25/1.55  #SimpNegUnit  : 3
% 2.25/1.55  #BackRed      : 3
% 2.25/1.55  
% 2.25/1.55  #Partial instantiations: 0
% 2.25/1.55  #Strategies tried      : 1
% 2.25/1.55  
% 2.25/1.55  Timing (in seconds)
% 2.25/1.55  ----------------------
% 2.25/1.55  Preprocessing        : 0.47
% 2.25/1.55  Parsing              : 0.25
% 2.25/1.55  CNF conversion       : 0.03
% 2.25/1.55  Main loop            : 0.17
% 2.25/1.55  Inferencing          : 0.06
% 2.25/1.55  Reduction            : 0.06
% 2.25/1.55  Demodulation         : 0.04
% 2.25/1.55  BG Simplification    : 0.02
% 2.25/1.55  Subsumption          : 0.03
% 2.25/1.55  Abstraction          : 0.01
% 2.25/1.55  MUC search           : 0.00
% 2.25/1.55  Cooper               : 0.00
% 2.25/1.55  Total                : 0.69
% 2.25/1.55  Index Insertion      : 0.00
% 2.25/1.55  Index Deletion       : 0.00
% 2.25/1.55  Index Matching       : 0.00
% 2.25/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
