%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:42 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  78 expanded)
%              Number of equality atoms :   33 (  43 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 )
        & ~ ( k7_setfam_1(A,B) != k1_xboole_0
            & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_16,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    ! [A_18,B_19] :
      ( k7_setfam_1(A_18,B_19) != k1_xboole_0
      | k1_xboole_0 = B_19
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_41,plain,
    ( k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_38])).

tff(c_44,plain,(
    k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_41])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k7_setfam_1(A_16,k7_setfam_1(A_16,B_17)) = B_17
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_33,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_30])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k7_setfam_1(A_5,B_6),k1_zfmisc_1(k1_zfmisc_1(A_5)))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_98,plain,(
    ! [A_28,B_29] :
      ( k6_setfam_1(A_28,k7_setfam_1(A_28,B_29)) = k3_subset_1(A_28,k5_setfam_1(A_28,B_29))
      | k1_xboole_0 = B_29
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k1_zfmisc_1(A_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_261,plain,(
    ! [A_46,B_47] :
      ( k6_setfam_1(A_46,k7_setfam_1(A_46,k7_setfam_1(A_46,B_47))) = k3_subset_1(A_46,k5_setfam_1(A_46,k7_setfam_1(A_46,B_47)))
      | k7_setfam_1(A_46,B_47) = k1_xboole_0
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_268,plain,
    ( k6_setfam_1('#skF_1',k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_261])).

tff(c_272,plain,
    ( k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2')
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_268])).

tff(c_273,plain,(
    k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_272])).

tff(c_45,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k5_setfam_1(A_20,B_21),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_subset_1(A_1,k3_subset_1(A_1,B_2)) = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    ! [A_24,B_25] :
      ( k3_subset_1(A_24,k3_subset_1(A_24,k5_setfam_1(A_24,B_25))) = k5_setfam_1(A_24,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_81,plain,(
    ! [A_5,B_6] :
      ( k3_subset_1(A_5,k3_subset_1(A_5,k5_setfam_1(A_5,k7_setfam_1(A_5,B_6)))) = k5_setfam_1(A_5,k7_setfam_1(A_5,B_6))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(resolution,[status(thm)],[c_6,c_73])).

tff(c_277,plain,
    ( k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_81])).

tff(c_281,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_277])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:31:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.28  
% 2.12/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.28  %$ m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.12/1.28  
% 2.12/1.28  %Foreground sorts:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Background operators:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Foreground operators:
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.28  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.12/1.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.12/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.12/1.28  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.28  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.12/1.28  
% 2.12/1.29  tff(f_70, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tops_2)).
% 2.12/1.29  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)) & ~(~(k7_setfam_1(A, B) = k1_xboole_0) & (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tops_2)).
% 2.12/1.29  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.12/1.29  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 2.12/1.29  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tops_2)).
% 2.12/1.29  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.12/1.29  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.12/1.29  tff(c_16, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.12/1.29  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.12/1.29  tff(c_18, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.12/1.29  tff(c_38, plain, (![A_18, B_19]: (k7_setfam_1(A_18, B_19)!=k1_xboole_0 | k1_xboole_0=B_19 | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.12/1.29  tff(c_41, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_20, c_38])).
% 2.12/1.29  tff(c_44, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_41])).
% 2.12/1.29  tff(c_30, plain, (![A_16, B_17]: (k7_setfam_1(A_16, k7_setfam_1(A_16, B_17))=B_17 | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.12/1.29  tff(c_33, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_20, c_30])).
% 2.12/1.29  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k7_setfam_1(A_5, B_6), k1_zfmisc_1(k1_zfmisc_1(A_5))) | ~m1_subset_1(B_6, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.12/1.29  tff(c_98, plain, (![A_28, B_29]: (k6_setfam_1(A_28, k7_setfam_1(A_28, B_29))=k3_subset_1(A_28, k5_setfam_1(A_28, B_29)) | k1_xboole_0=B_29 | ~m1_subset_1(B_29, k1_zfmisc_1(k1_zfmisc_1(A_28))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.12/1.29  tff(c_261, plain, (![A_46, B_47]: (k6_setfam_1(A_46, k7_setfam_1(A_46, k7_setfam_1(A_46, B_47)))=k3_subset_1(A_46, k5_setfam_1(A_46, k7_setfam_1(A_46, B_47))) | k7_setfam_1(A_46, B_47)=k1_xboole_0 | ~m1_subset_1(B_47, k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(resolution, [status(thm)], [c_6, c_98])).
% 2.12/1.29  tff(c_268, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))) | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_261])).
% 2.12/1.29  tff(c_272, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2') | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_33, c_268])).
% 2.12/1.29  tff(c_273, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_272])).
% 2.12/1.29  tff(c_45, plain, (![A_20, B_21]: (m1_subset_1(k5_setfam_1(A_20, B_21), k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.29  tff(c_2, plain, (![A_1, B_2]: (k3_subset_1(A_1, k3_subset_1(A_1, B_2))=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.29  tff(c_73, plain, (![A_24, B_25]: (k3_subset_1(A_24, k3_subset_1(A_24, k5_setfam_1(A_24, B_25)))=k5_setfam_1(A_24, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(k1_zfmisc_1(A_24))))), inference(resolution, [status(thm)], [c_45, c_2])).
% 2.12/1.29  tff(c_81, plain, (![A_5, B_6]: (k3_subset_1(A_5, k3_subset_1(A_5, k5_setfam_1(A_5, k7_setfam_1(A_5, B_6))))=k5_setfam_1(A_5, k7_setfam_1(A_5, B_6)) | ~m1_subset_1(B_6, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(resolution, [status(thm)], [c_6, c_73])).
% 2.12/1.29  tff(c_277, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_273, c_81])).
% 2.12/1.29  tff(c_281, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_277])).
% 2.12/1.29  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_281])).
% 2.12/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.29  
% 2.12/1.29  Inference rules
% 2.12/1.29  ----------------------
% 2.12/1.29  #Ref     : 0
% 2.12/1.29  #Sup     : 70
% 2.12/1.29  #Fact    : 0
% 2.12/1.29  #Define  : 0
% 2.12/1.29  #Split   : 0
% 2.12/1.29  #Chain   : 0
% 2.12/1.29  #Close   : 0
% 2.12/1.29  
% 2.12/1.29  Ordering : KBO
% 2.12/1.29  
% 2.12/1.29  Simplification rules
% 2.12/1.29  ----------------------
% 2.12/1.29  #Subsume      : 2
% 2.12/1.29  #Demod        : 15
% 2.12/1.29  #Tautology    : 34
% 2.12/1.29  #SimpNegUnit  : 6
% 2.12/1.29  #BackRed      : 0
% 2.12/1.29  
% 2.12/1.29  #Partial instantiations: 0
% 2.12/1.29  #Strategies tried      : 1
% 2.12/1.29  
% 2.12/1.29  Timing (in seconds)
% 2.12/1.29  ----------------------
% 2.12/1.30  Preprocessing        : 0.29
% 2.12/1.30  Parsing              : 0.15
% 2.12/1.30  CNF conversion       : 0.02
% 2.12/1.30  Main loop            : 0.22
% 2.12/1.30  Inferencing          : 0.08
% 2.12/1.30  Reduction            : 0.06
% 2.12/1.30  Demodulation         : 0.04
% 2.12/1.30  BG Simplification    : 0.01
% 2.12/1.30  Subsumption          : 0.05
% 2.12/1.30  Abstraction          : 0.01
% 2.12/1.30  MUC search           : 0.00
% 2.12/1.30  Cooper               : 0.00
% 2.12/1.30  Total                : 0.54
% 2.12/1.30  Index Insertion      : 0.00
% 2.12/1.30  Index Deletion       : 0.00
% 2.12/1.30  Index Matching       : 0.00
% 2.12/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
