%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:43 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :   53 (  82 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 ( 130 expanded)
%              Number of equality atoms :   32 (  56 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ( r1_xboole_0(B,C)
                & r1_xboole_0(k3_subset_1(A,B),k3_subset_1(A,C)) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(c_24,plain,(
    k3_subset_1('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_389,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k3_subset_1(A_45,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_401,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_389])).

tff(c_8,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k4_xboole_0(A_4,B_5)) = k3_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_427,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_8])).

tff(c_440,plain,(
    ! [A_47,B_48] :
      ( k3_subset_1(A_47,k3_subset_1(A_47,B_48)) = B_48
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_449,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_440])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k3_subset_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1909,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,k3_subset_1(A_81,B_82)) = k3_subset_1(A_81,k3_subset_1(A_81,B_82))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(resolution,[status(thm)],[c_20,c_389])).

tff(c_1915,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_1909])).

tff(c_1920,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_449,c_1915])).

tff(c_1949,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1920,c_427])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_44,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_44])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_400,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_389])).

tff(c_503,plain,(
    ! [A_49,B_50,C_51] : k2_xboole_0(k4_xboole_0(A_49,B_50),k4_xboole_0(A_49,C_51)) = k4_xboole_0(A_49,k3_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2141,plain,(
    ! [B_85] : k2_xboole_0(k4_xboole_0('#skF_1',B_85),k3_subset_1('#skF_1','#skF_3')) = k4_xboole_0('#skF_1',k3_xboole_0(B_85,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_503])).

tff(c_2167,plain,(
    k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_3')) = k4_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_2141])).

tff(c_2189,plain,(
    k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_56,c_2167])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(k2_xboole_0(A_11,B_12),B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_3701,plain,
    ( k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1','#skF_2')
    | ~ r1_xboole_0(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2189,c_16])).

tff(c_3709,plain,(
    k3_subset_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1949,c_3701])).

tff(c_448,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_440])).

tff(c_3718,plain,(
    k3_subset_1('#skF_1','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3709,c_448])).

tff(c_3726,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_3718])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:50:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.86  
% 4.47/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.87  %$ r1_xboole_0 > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.47/1.87  
% 4.47/1.87  %Foreground sorts:
% 4.47/1.87  
% 4.47/1.87  
% 4.47/1.87  %Background operators:
% 4.47/1.87  
% 4.47/1.87  
% 4.47/1.87  %Foreground operators:
% 4.47/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.47/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.47/1.87  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.47/1.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.47/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.47/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.47/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.47/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.47/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.47/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.47/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.47/1.87  
% 4.47/1.88  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_xboole_0(B, C) & r1_xboole_0(k3_subset_1(A, B), k3_subset_1(A, C))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_subset_1)).
% 4.47/1.88  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.47/1.88  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.47/1.88  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.47/1.88  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.47/1.88  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.47/1.88  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.47/1.88  tff(f_35, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_xboole_1)).
% 4.47/1.88  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 4.47/1.88  tff(c_24, plain, (k3_subset_1('#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.47/1.88  tff(c_26, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.47/1.88  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.47/1.88  tff(c_389, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k3_subset_1(A_45, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.47/1.88  tff(c_401, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_389])).
% 4.47/1.88  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k4_xboole_0(A_4, B_5))=k3_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.47/1.88  tff(c_427, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_401, c_8])).
% 4.47/1.88  tff(c_440, plain, (![A_47, B_48]: (k3_subset_1(A_47, k3_subset_1(A_47, B_48))=B_48 | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.47/1.88  tff(c_449, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_30, c_440])).
% 4.47/1.88  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(k3_subset_1(A_15, B_16), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.47/1.88  tff(c_1909, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k3_subset_1(A_81, B_82))=k3_subset_1(A_81, k3_subset_1(A_81, B_82)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(resolution, [status(thm)], [c_20, c_389])).
% 4.47/1.88  tff(c_1915, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_1909])).
% 4.47/1.88  tff(c_1920, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_427, c_449, c_1915])).
% 4.47/1.88  tff(c_1949, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1920, c_427])).
% 4.47/1.88  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.47/1.88  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.47/1.88  tff(c_44, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.47/1.88  tff(c_56, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_44])).
% 4.47/1.88  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.47/1.88  tff(c_400, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_389])).
% 4.47/1.88  tff(c_503, plain, (![A_49, B_50, C_51]: (k2_xboole_0(k4_xboole_0(A_49, B_50), k4_xboole_0(A_49, C_51))=k4_xboole_0(A_49, k3_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.47/1.88  tff(c_2141, plain, (![B_85]: (k2_xboole_0(k4_xboole_0('#skF_1', B_85), k3_subset_1('#skF_1', '#skF_3'))=k4_xboole_0('#skF_1', k3_xboole_0(B_85, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_401, c_503])).
% 4.47/1.88  tff(c_2167, plain, (k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_3'))=k4_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_400, c_2141])).
% 4.47/1.88  tff(c_2189, plain, (k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_56, c_2167])).
% 4.47/1.88  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(k2_xboole_0(A_11, B_12), B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.47/1.88  tff(c_3701, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', '#skF_2') | ~r1_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2189, c_16])).
% 4.47/1.88  tff(c_3709, plain, (k3_subset_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1949, c_3701])).
% 4.47/1.88  tff(c_448, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_32, c_440])).
% 4.47/1.88  tff(c_3718, plain, (k3_subset_1('#skF_1', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3709, c_448])).
% 4.47/1.88  tff(c_3726, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_3718])).
% 4.47/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.88  
% 4.47/1.88  Inference rules
% 4.47/1.88  ----------------------
% 4.47/1.88  #Ref     : 0
% 4.47/1.88  #Sup     : 952
% 4.47/1.88  #Fact    : 0
% 4.47/1.88  #Define  : 0
% 4.47/1.88  #Split   : 2
% 4.47/1.88  #Chain   : 0
% 4.47/1.88  #Close   : 0
% 4.47/1.88  
% 4.47/1.88  Ordering : KBO
% 4.47/1.88  
% 4.47/1.88  Simplification rules
% 4.47/1.88  ----------------------
% 4.47/1.88  #Subsume      : 38
% 4.47/1.88  #Demod        : 830
% 4.47/1.88  #Tautology    : 546
% 4.47/1.88  #SimpNegUnit  : 18
% 4.47/1.88  #BackRed      : 19
% 4.47/1.88  
% 4.47/1.88  #Partial instantiations: 0
% 4.47/1.88  #Strategies tried      : 1
% 4.47/1.88  
% 4.47/1.88  Timing (in seconds)
% 4.47/1.88  ----------------------
% 4.47/1.88  Preprocessing        : 0.30
% 4.47/1.88  Parsing              : 0.16
% 4.47/1.88  CNF conversion       : 0.02
% 4.47/1.88  Main loop            : 0.81
% 4.47/1.88  Inferencing          : 0.27
% 4.47/1.88  Reduction            : 0.33
% 4.47/1.88  Demodulation         : 0.26
% 4.47/1.88  BG Simplification    : 0.03
% 4.47/1.88  Subsumption          : 0.12
% 4.47/1.88  Abstraction          : 0.05
% 4.47/1.88  MUC search           : 0.00
% 4.47/1.88  Cooper               : 0.00
% 4.47/1.88  Total                : 1.14
% 4.47/1.88  Index Insertion      : 0.00
% 4.47/1.88  Index Deletion       : 0.00
% 4.47/1.88  Index Matching       : 0.00
% 4.47/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
