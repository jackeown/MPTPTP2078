%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:45 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   50 (  60 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   61 (  97 expanded)
%              Number of equality atoms :   20 (  25 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( ( r1_tarski(B,C)
                    & r1_xboole_0(D,C) )
                 => r1_tarski(B,k3_subset_1(A,D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_253,plain,(
    ! [B_40,A_41,C_42] :
      ( r1_tarski(B_40,k3_subset_1(A_41,C_42))
      | ~ r1_xboole_0(B_40,C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(A_41))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_259,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_253,c_18])).

tff(c_263,plain,(
    ~ r1_xboole_0('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_259])).

tff(c_271,plain,(
    k3_xboole_0('#skF_2','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_263])).

tff(c_12,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    ! [A_10] : k3_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_55])).

tff(c_75,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | k3_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [B_29,A_30] :
      ( r1_xboole_0(B_29,A_30)
      | k3_xboole_0(A_30,B_29) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_75,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_91,plain,(
    ! [B_31,A_32] :
      ( k3_xboole_0(B_31,A_32) = k1_xboole_0
      | k3_xboole_0(A_32,B_31) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_100,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_91])).

tff(c_20,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [B_20,A_21] :
      ( r1_xboole_0(B_20,A_21)
      | ~ r1_xboole_0(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_33,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_30])).

tff(c_38,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33,c_38])).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_63,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_55])).

tff(c_125,plain,(
    ! [A_34,B_35,C_36] : k3_xboole_0(k3_xboole_0(A_34,B_35),C_36) = k3_xboole_0(A_34,k3_xboole_0(B_35,C_36)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_272,plain,(
    ! [C_43] : k3_xboole_0('#skF_2',k3_xboole_0('#skF_3',C_43)) = k3_xboole_0('#skF_2',C_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_125])).

tff(c_293,plain,(
    k3_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_272])).

tff(c_300,plain,(
    k3_xboole_0('#skF_2','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_293])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:37:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.35  
% 2.22/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.35  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.22/1.35  
% 2.22/1.35  %Foreground sorts:
% 2.22/1.35  
% 2.22/1.35  
% 2.22/1.35  %Background operators:
% 2.22/1.35  
% 2.22/1.35  
% 2.22/1.35  %Foreground operators:
% 2.22/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.35  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.22/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.22/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.35  
% 2.22/1.36  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.22/1.36  tff(f_65, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_xboole_0(D, C)) => r1_tarski(B, k3_subset_1(A, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_subset_1)).
% 2.22/1.36  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 2.22/1.36  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.22/1.36  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.22/1.36  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.22/1.36  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.22/1.36  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.36  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.36  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.36  tff(c_253, plain, (![B_40, A_41, C_42]: (r1_tarski(B_40, k3_subset_1(A_41, C_42)) | ~r1_xboole_0(B_40, C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(A_41)) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.22/1.36  tff(c_18, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.36  tff(c_259, plain, (~r1_xboole_0('#skF_2', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_253, c_18])).
% 2.22/1.36  tff(c_263, plain, (~r1_xboole_0('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_259])).
% 2.22/1.36  tff(c_271, plain, (k3_xboole_0('#skF_2', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_263])).
% 2.22/1.36  tff(c_12, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.22/1.36  tff(c_55, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.22/1.36  tff(c_62, plain, (![A_10]: (k3_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_55])).
% 2.22/1.36  tff(c_75, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | k3_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.36  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.36  tff(c_83, plain, (![B_29, A_30]: (r1_xboole_0(B_29, A_30) | k3_xboole_0(A_30, B_29)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_75, c_6])).
% 2.22/1.36  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.36  tff(c_91, plain, (![B_31, A_32]: (k3_xboole_0(B_31, A_32)=k1_xboole_0 | k3_xboole_0(A_32, B_31)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_83, c_2])).
% 2.22/1.36  tff(c_100, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_62, c_91])).
% 2.22/1.36  tff(c_20, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.36  tff(c_30, plain, (![B_20, A_21]: (r1_xboole_0(B_20, A_21) | ~r1_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.22/1.36  tff(c_33, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_20, c_30])).
% 2.22/1.36  tff(c_38, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.36  tff(c_45, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_33, c_38])).
% 2.22/1.36  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.36  tff(c_63, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_22, c_55])).
% 2.22/1.36  tff(c_125, plain, (![A_34, B_35, C_36]: (k3_xboole_0(k3_xboole_0(A_34, B_35), C_36)=k3_xboole_0(A_34, k3_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.36  tff(c_272, plain, (![C_43]: (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', C_43))=k3_xboole_0('#skF_2', C_43))), inference(superposition, [status(thm), theory('equality')], [c_63, c_125])).
% 2.22/1.36  tff(c_293, plain, (k3_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_45, c_272])).
% 2.22/1.36  tff(c_300, plain, (k3_xboole_0('#skF_2', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_100, c_293])).
% 2.22/1.36  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_271, c_300])).
% 2.22/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.36  
% 2.22/1.36  Inference rules
% 2.22/1.36  ----------------------
% 2.22/1.36  #Ref     : 0
% 2.22/1.36  #Sup     : 73
% 2.22/1.36  #Fact    : 0
% 2.22/1.36  #Define  : 0
% 2.22/1.36  #Split   : 1
% 2.22/1.36  #Chain   : 0
% 2.22/1.36  #Close   : 0
% 2.22/1.36  
% 2.22/1.36  Ordering : KBO
% 2.22/1.36  
% 2.22/1.36  Simplification rules
% 2.22/1.36  ----------------------
% 2.22/1.36  #Subsume      : 1
% 2.22/1.36  #Demod        : 48
% 2.22/1.36  #Tautology    : 47
% 2.22/1.36  #SimpNegUnit  : 1
% 2.22/1.36  #BackRed      : 0
% 2.22/1.36  
% 2.22/1.36  #Partial instantiations: 0
% 2.22/1.36  #Strategies tried      : 1
% 2.22/1.36  
% 2.22/1.36  Timing (in seconds)
% 2.22/1.36  ----------------------
% 2.22/1.37  Preprocessing        : 0.33
% 2.22/1.37  Parsing              : 0.19
% 2.22/1.37  CNF conversion       : 0.02
% 2.22/1.37  Main loop            : 0.21
% 2.22/1.37  Inferencing          : 0.08
% 2.22/1.37  Reduction            : 0.07
% 2.22/1.37  Demodulation         : 0.05
% 2.22/1.37  BG Simplification    : 0.01
% 2.22/1.37  Subsumption          : 0.04
% 2.22/1.37  Abstraction          : 0.01
% 2.22/1.37  MUC search           : 0.00
% 2.22/1.37  Cooper               : 0.00
% 2.22/1.37  Total                : 0.57
% 2.22/1.37  Index Insertion      : 0.00
% 2.22/1.37  Index Deletion       : 0.00
% 2.22/1.37  Index Matching       : 0.00
% 2.22/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
