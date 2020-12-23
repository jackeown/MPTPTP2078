%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:41 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   52 (  64 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 (  93 expanded)
%              Number of equality atoms :   40 (  55 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ~ ( B != k1_xboole_0
          & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k5_setfam_1(A,k7_setfam_1(A,B)) = k7_subset_1(A,k2_subset_1(A),k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_setfam_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_20,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_61,plain,(
    ! [A_26,B_27] :
      ( k7_setfam_1(A_26,B_27) != k1_xboole_0
      | k1_xboole_0 = B_27
      | ~ m1_subset_1(B_27,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_68,plain,
    ( k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_61])).

tff(c_76,plain,(
    k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_68])).

tff(c_79,plain,(
    ! [A_29,B_30] :
      ( k7_setfam_1(A_29,k7_setfam_1(A_29,B_30)) = B_30
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_89,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_79])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k7_setfam_1(A_8,B_9),k1_zfmisc_1(k1_zfmisc_1(A_8)))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k1_zfmisc_1(A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_182,plain,(
    ! [A_39,B_40] :
      ( k6_setfam_1(A_39,k7_setfam_1(A_39,B_40)) = k3_subset_1(A_39,k5_setfam_1(A_39,B_40))
      | k1_xboole_0 = B_40
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(A_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_919,plain,(
    ! [A_77,B_78] :
      ( k6_setfam_1(A_77,k7_setfam_1(A_77,k7_setfam_1(A_77,B_78))) = k3_subset_1(A_77,k5_setfam_1(A_77,k7_setfam_1(A_77,B_78)))
      | k7_setfam_1(A_77,B_78) = k1_xboole_0
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k1_zfmisc_1(A_77))) ) ),
    inference(resolution,[status(thm)],[c_10,c_182])).

tff(c_933,plain,
    ( k6_setfam_1('#skF_1',k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_919])).

tff(c_943,plain,
    ( k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2')
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_933])).

tff(c_944,plain,(
    k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_943])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_25,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k7_subset_1(A_14,k2_subset_1(A_14),k6_setfam_1(A_14,B_15)) = k5_setfam_1(A_14,k7_setfam_1(A_14,B_15))
      | k1_xboole_0 = B_15
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_266,plain,(
    ! [A_45,B_46] :
      ( k7_subset_1(A_45,A_45,k6_setfam_1(A_45,B_46)) = k5_setfam_1(A_45,k7_setfam_1(A_45,B_46))
      | k1_xboole_0 = B_46
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_275,plain,
    ( k7_subset_1('#skF_1','#skF_1',k6_setfam_1('#skF_1','#skF_2')) = k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_266])).

tff(c_285,plain,(
    k7_subset_1('#skF_1','#skF_1',k6_setfam_1('#skF_1','#skF_2')) = k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_275])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] :
      ( m1_subset_1(k7_subset_1(A_3,B_4,C_5),k1_zfmisc_1(A_3))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_290,plain,
    ( m1_subset_1(k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_6])).

tff(c_294,plain,(
    m1_subset_1(k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_290])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_subset_1(A_6,k3_subset_1(A_6,B_7)) = B_7
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_298,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))) = k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_294,c_8])).

tff(c_947,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_298])).

tff(c_949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_947])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:38:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.41  
% 2.85/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.41  %$ m1_subset_1 > k7_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.85/1.41  
% 2.85/1.41  %Foreground sorts:
% 2.85/1.41  
% 2.85/1.41  
% 2.85/1.41  %Background operators:
% 2.85/1.41  
% 2.85/1.41  
% 2.85/1.41  %Foreground operators:
% 2.85/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.41  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.85/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.85/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.41  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.85/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.85/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.41  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.85/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.41  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.85/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.41  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.85/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.42  
% 2.85/1.43  tff(f_75, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tops_2)).
% 2.85/1.43  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.85/1.43  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.85/1.43  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 2.85/1.43  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tops_2)).
% 2.85/1.43  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.85/1.43  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.85/1.43  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k7_subset_1(A, k2_subset_1(A), k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_setfam_1)).
% 2.85/1.43  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 2.85/1.43  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.85/1.43  tff(c_20, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.85/1.43  tff(c_22, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.85/1.43  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.85/1.43  tff(c_61, plain, (![A_26, B_27]: (k7_setfam_1(A_26, B_27)!=k1_xboole_0 | k1_xboole_0=B_27 | ~m1_subset_1(B_27, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.85/1.43  tff(c_68, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_24, c_61])).
% 2.85/1.43  tff(c_76, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_22, c_68])).
% 2.85/1.43  tff(c_79, plain, (![A_29, B_30]: (k7_setfam_1(A_29, k7_setfam_1(A_29, B_30))=B_30 | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(A_29))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.85/1.43  tff(c_89, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_24, c_79])).
% 2.85/1.43  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(k7_setfam_1(A_8, B_9), k1_zfmisc_1(k1_zfmisc_1(A_8))) | ~m1_subset_1(B_9, k1_zfmisc_1(k1_zfmisc_1(A_8))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.85/1.43  tff(c_182, plain, (![A_39, B_40]: (k6_setfam_1(A_39, k7_setfam_1(A_39, B_40))=k3_subset_1(A_39, k5_setfam_1(A_39, B_40)) | k1_xboole_0=B_40 | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(A_39))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.85/1.43  tff(c_919, plain, (![A_77, B_78]: (k6_setfam_1(A_77, k7_setfam_1(A_77, k7_setfam_1(A_77, B_78)))=k3_subset_1(A_77, k5_setfam_1(A_77, k7_setfam_1(A_77, B_78))) | k7_setfam_1(A_77, B_78)=k1_xboole_0 | ~m1_subset_1(B_78, k1_zfmisc_1(k1_zfmisc_1(A_77))))), inference(resolution, [status(thm)], [c_10, c_182])).
% 2.85/1.43  tff(c_933, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))) | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_919])).
% 2.85/1.43  tff(c_943, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2') | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_89, c_933])).
% 2.85/1.43  tff(c_944, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_76, c_943])).
% 2.85/1.43  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.85/1.43  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.85/1.43  tff(c_25, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 2.85/1.43  tff(c_16, plain, (![A_14, B_15]: (k7_subset_1(A_14, k2_subset_1(A_14), k6_setfam_1(A_14, B_15))=k5_setfam_1(A_14, k7_setfam_1(A_14, B_15)) | k1_xboole_0=B_15 | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.85/1.43  tff(c_266, plain, (![A_45, B_46]: (k7_subset_1(A_45, A_45, k6_setfam_1(A_45, B_46))=k5_setfam_1(A_45, k7_setfam_1(A_45, B_46)) | k1_xboole_0=B_46 | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(A_45))))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 2.85/1.43  tff(c_275, plain, (k7_subset_1('#skF_1', '#skF_1', k6_setfam_1('#skF_1', '#skF_2'))=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_24, c_266])).
% 2.85/1.43  tff(c_285, plain, (k7_subset_1('#skF_1', '#skF_1', k6_setfam_1('#skF_1', '#skF_2'))=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_22, c_275])).
% 2.85/1.43  tff(c_6, plain, (![A_3, B_4, C_5]: (m1_subset_1(k7_subset_1(A_3, B_4, C_5), k1_zfmisc_1(A_3)) | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.85/1.43  tff(c_290, plain, (m1_subset_1(k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_285, c_6])).
% 2.85/1.43  tff(c_294, plain, (m1_subset_1(k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_25, c_290])).
% 2.85/1.43  tff(c_8, plain, (![A_6, B_7]: (k3_subset_1(A_6, k3_subset_1(A_6, B_7))=B_7 | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.85/1.43  tff(c_298, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))))=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_294, c_8])).
% 2.85/1.43  tff(c_947, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_944, c_298])).
% 2.85/1.43  tff(c_949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_947])).
% 2.85/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.43  
% 2.85/1.43  Inference rules
% 2.85/1.43  ----------------------
% 2.85/1.43  #Ref     : 0
% 2.85/1.43  #Sup     : 249
% 2.85/1.43  #Fact    : 0
% 2.85/1.43  #Define  : 0
% 2.85/1.43  #Split   : 0
% 2.85/1.43  #Chain   : 0
% 2.85/1.43  #Close   : 0
% 2.85/1.43  
% 2.85/1.43  Ordering : KBO
% 2.85/1.43  
% 2.85/1.43  Simplification rules
% 2.85/1.43  ----------------------
% 2.85/1.43  #Subsume      : 76
% 2.85/1.43  #Demod        : 54
% 2.85/1.43  #Tautology    : 106
% 2.85/1.43  #SimpNegUnit  : 7
% 2.85/1.43  #BackRed      : 1
% 2.85/1.43  
% 2.85/1.43  #Partial instantiations: 0
% 2.85/1.43  #Strategies tried      : 1
% 2.85/1.43  
% 2.85/1.43  Timing (in seconds)
% 2.85/1.43  ----------------------
% 2.85/1.43  Preprocessing        : 0.28
% 2.85/1.43  Parsing              : 0.16
% 2.85/1.43  CNF conversion       : 0.02
% 2.85/1.43  Main loop            : 0.38
% 2.85/1.43  Inferencing          : 0.15
% 2.85/1.43  Reduction            : 0.11
% 2.85/1.43  Demodulation         : 0.08
% 2.85/1.43  BG Simplification    : 0.02
% 2.85/1.43  Subsumption          : 0.08
% 2.85/1.43  Abstraction          : 0.02
% 2.85/1.43  MUC search           : 0.00
% 2.85/1.43  Cooper               : 0.00
% 2.85/1.43  Total                : 0.69
% 2.85/1.43  Index Insertion      : 0.00
% 2.85/1.43  Index Deletion       : 0.00
% 2.85/1.43  Index Matching       : 0.00
% 2.85/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
