%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:43 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  76 expanded)
%              Number of equality atoms :   31 (  41 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ~ ( B != k1_xboole_0
          & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

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

tff(f_56,axiom,(
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

tff(c_14,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_43,plain,(
    ! [A_19,B_20] :
      ( k7_setfam_1(A_19,B_20) != k1_xboole_0
      | k1_xboole_0 = B_20
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_50,plain,
    ( k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_43])).

tff(c_54,plain,(
    k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_50])).

tff(c_31,plain,(
    ! [A_17,B_18] :
      ( k7_setfam_1(A_17,k7_setfam_1(A_17,B_18)) = B_18
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_31])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k7_setfam_1(A_5,B_6),k1_zfmisc_1(k1_zfmisc_1(A_5)))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_107,plain,(
    ! [A_29,B_30] :
      ( k6_setfam_1(A_29,k7_setfam_1(A_29,B_30)) = k3_subset_1(A_29,k5_setfam_1(A_29,B_30))
      | k1_xboole_0 = B_30
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_258,plain,(
    ! [A_45,B_46] :
      ( k6_setfam_1(A_45,k7_setfam_1(A_45,k7_setfam_1(A_45,B_46))) = k3_subset_1(A_45,k5_setfam_1(A_45,k7_setfam_1(A_45,B_46)))
      | k7_setfam_1(A_45,B_46) = k1_xboole_0
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_265,plain,
    ( k6_setfam_1('#skF_1',k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_258])).

tff(c_269,plain,
    ( k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2')
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_265])).

tff(c_270,plain,(
    k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_269])).

tff(c_27,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k5_setfam_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1(A_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_subset_1(A_1,k3_subset_1(A_1,B_2)) = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    ! [A_23,B_24] :
      ( k3_subset_1(A_23,k3_subset_1(A_23,k5_setfam_1(A_23,B_24))) = k5_setfam_1(A_23,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k1_zfmisc_1(A_23))) ) ),
    inference(resolution,[status(thm)],[c_27,c_2])).

tff(c_78,plain,(
    ! [A_5,B_6] :
      ( k3_subset_1(A_5,k3_subset_1(A_5,k5_setfam_1(A_5,k7_setfam_1(A_5,B_6)))) = k5_setfam_1(A_5,k7_setfam_1(A_5,B_6))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_283,plain,
    ( k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_78])).

tff(c_287,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_283])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_287])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:13:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.27  
% 2.08/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.27  %$ m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.08/1.27  
% 2.08/1.27  %Foreground sorts:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Background operators:
% 2.08/1.27  
% 2.08/1.27  
% 2.08/1.27  %Foreground operators:
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.27  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.08/1.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.08/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.27  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.27  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.08/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.27  
% 2.08/1.28  tff(f_64, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tops_2)).
% 2.08/1.28  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.08/1.28  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.08/1.28  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 2.08/1.28  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tops_2)).
% 2.08/1.28  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.08/1.28  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.08/1.28  tff(c_14, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.28  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.28  tff(c_16, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.28  tff(c_43, plain, (![A_19, B_20]: (k7_setfam_1(A_19, B_20)!=k1_xboole_0 | k1_xboole_0=B_20 | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(A_19))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.08/1.28  tff(c_50, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_18, c_43])).
% 2.08/1.28  tff(c_54, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_16, c_50])).
% 2.08/1.28  tff(c_31, plain, (![A_17, B_18]: (k7_setfam_1(A_17, k7_setfam_1(A_17, B_18))=B_18 | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.28  tff(c_38, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_18, c_31])).
% 2.08/1.28  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k7_setfam_1(A_5, B_6), k1_zfmisc_1(k1_zfmisc_1(A_5))) | ~m1_subset_1(B_6, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.08/1.28  tff(c_107, plain, (![A_29, B_30]: (k6_setfam_1(A_29, k7_setfam_1(A_29, B_30))=k3_subset_1(A_29, k5_setfam_1(A_29, B_30)) | k1_xboole_0=B_30 | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(A_29))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.28  tff(c_258, plain, (![A_45, B_46]: (k6_setfam_1(A_45, k7_setfam_1(A_45, k7_setfam_1(A_45, B_46)))=k3_subset_1(A_45, k5_setfam_1(A_45, k7_setfam_1(A_45, B_46))) | k7_setfam_1(A_45, B_46)=k1_xboole_0 | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(A_45))))), inference(resolution, [status(thm)], [c_6, c_107])).
% 2.08/1.28  tff(c_265, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))) | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_258])).
% 2.08/1.28  tff(c_269, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2') | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_38, c_265])).
% 2.08/1.28  tff(c_270, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_269])).
% 2.08/1.28  tff(c_27, plain, (![A_15, B_16]: (m1_subset_1(k5_setfam_1(A_15, B_16), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(k1_zfmisc_1(A_15))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.28  tff(c_2, plain, (![A_1, B_2]: (k3_subset_1(A_1, k3_subset_1(A_1, B_2))=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.28  tff(c_70, plain, (![A_23, B_24]: (k3_subset_1(A_23, k3_subset_1(A_23, k5_setfam_1(A_23, B_24)))=k5_setfam_1(A_23, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(k1_zfmisc_1(A_23))))), inference(resolution, [status(thm)], [c_27, c_2])).
% 2.08/1.28  tff(c_78, plain, (![A_5, B_6]: (k3_subset_1(A_5, k3_subset_1(A_5, k5_setfam_1(A_5, k7_setfam_1(A_5, B_6))))=k5_setfam_1(A_5, k7_setfam_1(A_5, B_6)) | ~m1_subset_1(B_6, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(resolution, [status(thm)], [c_6, c_70])).
% 2.08/1.28  tff(c_283, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_270, c_78])).
% 2.08/1.28  tff(c_287, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_283])).
% 2.08/1.28  tff(c_289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_287])).
% 2.08/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.28  
% 2.08/1.28  Inference rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Ref     : 0
% 2.08/1.28  #Sup     : 72
% 2.08/1.28  #Fact    : 0
% 2.08/1.28  #Define  : 0
% 2.08/1.28  #Split   : 0
% 2.08/1.28  #Chain   : 0
% 2.08/1.28  #Close   : 0
% 2.08/1.28  
% 2.08/1.28  Ordering : KBO
% 2.08/1.28  
% 2.08/1.28  Simplification rules
% 2.08/1.28  ----------------------
% 2.08/1.28  #Subsume      : 2
% 2.08/1.28  #Demod        : 15
% 2.08/1.28  #Tautology    : 34
% 2.08/1.28  #SimpNegUnit  : 6
% 2.08/1.28  #BackRed      : 0
% 2.08/1.28  
% 2.08/1.28  #Partial instantiations: 0
% 2.08/1.28  #Strategies tried      : 1
% 2.08/1.28  
% 2.08/1.28  Timing (in seconds)
% 2.08/1.28  ----------------------
% 2.08/1.28  Preprocessing        : 0.29
% 2.08/1.28  Parsing              : 0.16
% 2.08/1.28  CNF conversion       : 0.02
% 2.08/1.28  Main loop            : 0.23
% 2.08/1.28  Inferencing          : 0.09
% 2.08/1.28  Reduction            : 0.06
% 2.08/1.28  Demodulation         : 0.04
% 2.08/1.28  BG Simplification    : 0.02
% 2.08/1.29  Subsumption          : 0.05
% 2.08/1.29  Abstraction          : 0.02
% 2.08/1.29  MUC search           : 0.00
% 2.08/1.29  Cooper               : 0.00
% 2.08/1.29  Total                : 0.55
% 2.08/1.29  Index Insertion      : 0.00
% 2.08/1.29  Index Deletion       : 0.00
% 2.08/1.29  Index Matching       : 0.00
% 2.08/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
