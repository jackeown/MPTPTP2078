%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:53 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :   54 (  60 expanded)
%              Number of leaves         :   29 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 (  75 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_349,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = k3_subset_1(A_64,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_370,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_349])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_21] : ~ v1_xboole_0(k1_zfmisc_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_127,plain,(
    ! [B_48,A_49] :
      ( r2_hidden(B_48,A_49)
      | ~ m1_subset_1(B_48,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_134,plain,(
    ! [B_48,A_10] :
      ( r1_tarski(B_48,A_10)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_127,c_10])).

tff(c_139,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(B_50,A_51)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_134])).

tff(c_155,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_139])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_169,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_155,c_6])).

tff(c_214,plain,(
    ! [A_54,B_55,C_56] : k4_xboole_0(k3_xboole_0(A_54,B_55),C_56) = k3_xboole_0(A_54,k4_xboole_0(B_55,C_56)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_229,plain,(
    ! [C_56] : k3_xboole_0('#skF_4',k4_xboole_0('#skF_3',C_56)) = k4_xboole_0('#skF_4',C_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_214])).

tff(c_386,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_229])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k3_subset_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_732,plain,(
    ! [A_80,B_81,C_82] :
      ( k9_subset_1(A_80,B_81,C_82) = k3_xboole_0(B_81,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2325,plain,(
    ! [A_138,B_139,B_140] :
      ( k9_subset_1(A_138,B_139,k3_subset_1(A_138,B_140)) = k3_xboole_0(B_139,k3_subset_1(A_138,B_140))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_138)) ) ),
    inference(resolution,[status(thm)],[c_32,c_732])).

tff(c_2347,plain,(
    ! [B_139] : k9_subset_1('#skF_3',B_139,k3_subset_1('#skF_3','#skF_5')) = k3_xboole_0(B_139,k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_2325])).

tff(c_468,plain,(
    ! [A_68,B_69,C_70] :
      ( k7_subset_1(A_68,B_69,C_70) = k4_xboole_0(B_69,C_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_483,plain,(
    ! [C_70] : k7_subset_1('#skF_3','#skF_4',C_70) = k4_xboole_0('#skF_4',C_70) ),
    inference(resolution,[status(thm)],[c_44,c_468])).

tff(c_40,plain,(
    k9_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_5')) != k7_subset_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_485,plain,(
    k9_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_5')) != k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_40])).

tff(c_2357,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) != k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2347,c_485])).

tff(c_2360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_2357])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:36:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.79  
% 4.45/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.79  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.45/1.79  
% 4.45/1.79  %Foreground sorts:
% 4.45/1.79  
% 4.45/1.79  
% 4.45/1.79  %Background operators:
% 4.45/1.79  
% 4.45/1.79  
% 4.45/1.79  %Foreground operators:
% 4.45/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.45/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.45/1.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.45/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.79  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.45/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.45/1.79  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.45/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.45/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.45/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.45/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.45/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.45/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.45/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.45/1.79  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.45/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.45/1.79  
% 4.48/1.81  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 4.48/1.81  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.48/1.81  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.48/1.81  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.48/1.81  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.48/1.81  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.48/1.81  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.48/1.81  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.48/1.81  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.48/1.81  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.48/1.81  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.48/1.81  tff(c_349, plain, (![A_64, B_65]: (k4_xboole_0(A_64, B_65)=k3_subset_1(A_64, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.48/1.81  tff(c_370, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_349])).
% 4.48/1.81  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.48/1.81  tff(c_34, plain, (![A_21]: (~v1_xboole_0(k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.48/1.81  tff(c_127, plain, (![B_48, A_49]: (r2_hidden(B_48, A_49) | ~m1_subset_1(B_48, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.48/1.81  tff(c_10, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.48/1.81  tff(c_134, plain, (![B_48, A_10]: (r1_tarski(B_48, A_10) | ~m1_subset_1(B_48, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_127, c_10])).
% 4.48/1.81  tff(c_139, plain, (![B_50, A_51]: (r1_tarski(B_50, A_51) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)))), inference(negUnitSimplification, [status(thm)], [c_34, c_134])).
% 4.48/1.81  tff(c_155, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_139])).
% 4.48/1.81  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.48/1.81  tff(c_169, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_155, c_6])).
% 4.48/1.81  tff(c_214, plain, (![A_54, B_55, C_56]: (k4_xboole_0(k3_xboole_0(A_54, B_55), C_56)=k3_xboole_0(A_54, k4_xboole_0(B_55, C_56)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.48/1.81  tff(c_229, plain, (![C_56]: (k3_xboole_0('#skF_4', k4_xboole_0('#skF_3', C_56))=k4_xboole_0('#skF_4', C_56))), inference(superposition, [status(thm), theory('equality')], [c_169, c_214])).
% 4.48/1.81  tff(c_386, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_370, c_229])).
% 4.48/1.81  tff(c_32, plain, (![A_19, B_20]: (m1_subset_1(k3_subset_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.48/1.81  tff(c_732, plain, (![A_80, B_81, C_82]: (k9_subset_1(A_80, B_81, C_82)=k3_xboole_0(B_81, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.48/1.81  tff(c_2325, plain, (![A_138, B_139, B_140]: (k9_subset_1(A_138, B_139, k3_subset_1(A_138, B_140))=k3_xboole_0(B_139, k3_subset_1(A_138, B_140)) | ~m1_subset_1(B_140, k1_zfmisc_1(A_138)))), inference(resolution, [status(thm)], [c_32, c_732])).
% 4.48/1.81  tff(c_2347, plain, (![B_139]: (k9_subset_1('#skF_3', B_139, k3_subset_1('#skF_3', '#skF_5'))=k3_xboole_0(B_139, k3_subset_1('#skF_3', '#skF_5')))), inference(resolution, [status(thm)], [c_42, c_2325])).
% 4.48/1.81  tff(c_468, plain, (![A_68, B_69, C_70]: (k7_subset_1(A_68, B_69, C_70)=k4_xboole_0(B_69, C_70) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.48/1.81  tff(c_483, plain, (![C_70]: (k7_subset_1('#skF_3', '#skF_4', C_70)=k4_xboole_0('#skF_4', C_70))), inference(resolution, [status(thm)], [c_44, c_468])).
% 4.48/1.81  tff(c_40, plain, (k9_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k7_subset_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.48/1.81  tff(c_485, plain, (k9_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_483, c_40])).
% 4.48/1.81  tff(c_2357, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2347, c_485])).
% 4.48/1.81  tff(c_2360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_386, c_2357])).
% 4.48/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.81  
% 4.48/1.81  Inference rules
% 4.48/1.81  ----------------------
% 4.48/1.81  #Ref     : 0
% 4.48/1.81  #Sup     : 619
% 4.48/1.81  #Fact    : 0
% 4.48/1.81  #Define  : 0
% 4.48/1.81  #Split   : 0
% 4.48/1.81  #Chain   : 0
% 4.48/1.81  #Close   : 0
% 4.48/1.81  
% 4.48/1.81  Ordering : KBO
% 4.48/1.81  
% 4.48/1.81  Simplification rules
% 4.48/1.81  ----------------------
% 4.48/1.81  #Subsume      : 26
% 4.48/1.81  #Demod        : 182
% 4.48/1.81  #Tautology    : 291
% 4.48/1.81  #SimpNegUnit  : 9
% 4.48/1.81  #BackRed      : 6
% 4.48/1.81  
% 4.48/1.81  #Partial instantiations: 0
% 4.48/1.81  #Strategies tried      : 1
% 4.48/1.81  
% 4.48/1.81  Timing (in seconds)
% 4.48/1.81  ----------------------
% 4.55/1.82  Preprocessing        : 0.33
% 4.55/1.82  Parsing              : 0.18
% 4.55/1.82  CNF conversion       : 0.02
% 4.55/1.82  Main loop            : 0.71
% 4.55/1.82  Inferencing          : 0.24
% 4.55/1.82  Reduction            : 0.27
% 4.55/1.82  Demodulation         : 0.20
% 4.55/1.82  BG Simplification    : 0.03
% 4.55/1.82  Subsumption          : 0.12
% 4.55/1.82  Abstraction          : 0.04
% 4.55/1.82  MUC search           : 0.00
% 4.55/1.82  Cooper               : 0.00
% 4.55/1.82  Total                : 1.08
% 4.55/1.82  Index Insertion      : 0.00
% 4.55/1.82  Index Deletion       : 0.00
% 4.55/1.82  Index Matching       : 0.00
% 4.57/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
