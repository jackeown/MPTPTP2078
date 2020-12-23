%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:43 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 145 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :   79 ( 205 expanded)
%              Number of equality atoms :    9 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [A_38,B_39] : k1_setfam_1(k2_tarski(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_93,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(B_43,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_69])).

tff(c_12,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_99,plain,(
    ! [B_43,A_42] : k3_xboole_0(B_43,A_42) = k3_xboole_0(A_42,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_12])).

tff(c_156,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k4_xboole_0(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_165,plain,(
    ! [A_48,B_49] : r1_tarski(k3_xboole_0(A_48,B_49),A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_4])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_191,plain,(
    ! [A_54,B_55] :
      ( v1_relat_1(A_54)
      | ~ v1_relat_1(B_55)
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_16,c_151])).

tff(c_204,plain,(
    ! [A_56,B_57] :
      ( v1_relat_1(k3_xboole_0(A_56,B_57))
      | ~ v1_relat_1(A_56) ) ),
    inference(resolution,[status(thm)],[c_165,c_191])).

tff(c_210,plain,(
    ! [A_42,B_43] :
      ( v1_relat_1(k3_xboole_0(A_42,B_43))
      | ~ v1_relat_1(B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_204])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_174,plain,(
    ! [A_50,B_51] : r1_tarski(k3_xboole_0(A_50,B_51),A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_4])).

tff(c_177,plain,(
    ! [B_43,A_42] : r1_tarski(k3_xboole_0(B_43,A_42),A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_174])).

tff(c_476,plain,(
    ! [C_84,A_85,B_86] :
      ( r1_tarski(k5_relat_1(C_84,A_85),k5_relat_1(C_84,B_86))
      | ~ r1_tarski(A_85,B_86)
      | ~ v1_relat_1(C_84)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_356,plain,(
    ! [C_74,A_75,B_76] :
      ( r1_tarski(k5_relat_1(C_74,A_75),k5_relat_1(C_74,B_76))
      | ~ r1_tarski(A_75,B_76)
      | ~ v1_relat_1(C_74)
      | ~ v1_relat_1(B_76)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_222,plain,(
    ! [A_62,B_63,C_64] :
      ( r1_tarski(A_62,k3_xboole_0(B_63,C_64))
      | ~ r1_tarski(A_62,C_64)
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_116,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_99,c_22])).

tff(c_236,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_222,c_116])).

tff(c_263,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_359,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_356,c_263])).

tff(c_365,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_165,c_359])).

tff(c_369,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_210,c_365])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_369])).

tff(c_377,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_479,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_476,c_377])).

tff(c_485,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_177,c_479])).

tff(c_489,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_210,c_485])).

tff(c_496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.34  
% 2.33/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.35  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.33/1.35  
% 2.33/1.35  %Foreground sorts:
% 2.33/1.35  
% 2.33/1.35  
% 2.33/1.35  %Background operators:
% 2.33/1.35  
% 2.33/1.35  
% 2.33/1.35  %Foreground operators:
% 2.33/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.33/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.33/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.33/1.35  
% 2.33/1.36  tff(f_75, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 2.33/1.36  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.33/1.36  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.33/1.36  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.33/1.36  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.33/1.36  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.33/1.36  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.33/1.36  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 2.33/1.36  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.33/1.36  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.33/1.36  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.33/1.36  tff(c_69, plain, (![A_38, B_39]: (k1_setfam_1(k2_tarski(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.36  tff(c_93, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(B_43, A_42))), inference(superposition, [status(thm), theory('equality')], [c_8, c_69])).
% 2.33/1.36  tff(c_12, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.33/1.36  tff(c_99, plain, (![B_43, A_42]: (k3_xboole_0(B_43, A_42)=k3_xboole_0(A_42, B_43))), inference(superposition, [status(thm), theory('equality')], [c_93, c_12])).
% 2.33/1.36  tff(c_156, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k4_xboole_0(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.36  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.33/1.36  tff(c_165, plain, (![A_48, B_49]: (r1_tarski(k3_xboole_0(A_48, B_49), A_48))), inference(superposition, [status(thm), theory('equality')], [c_156, c_4])).
% 2.33/1.36  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.33/1.36  tff(c_151, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.36  tff(c_191, plain, (![A_54, B_55]: (v1_relat_1(A_54) | ~v1_relat_1(B_55) | ~r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_16, c_151])).
% 2.33/1.36  tff(c_204, plain, (![A_56, B_57]: (v1_relat_1(k3_xboole_0(A_56, B_57)) | ~v1_relat_1(A_56))), inference(resolution, [status(thm)], [c_165, c_191])).
% 2.33/1.36  tff(c_210, plain, (![A_42, B_43]: (v1_relat_1(k3_xboole_0(A_42, B_43)) | ~v1_relat_1(B_43))), inference(superposition, [status(thm), theory('equality')], [c_99, c_204])).
% 2.33/1.36  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.33/1.36  tff(c_174, plain, (![A_50, B_51]: (r1_tarski(k3_xboole_0(A_50, B_51), A_50))), inference(superposition, [status(thm), theory('equality')], [c_156, c_4])).
% 2.33/1.36  tff(c_177, plain, (![B_43, A_42]: (r1_tarski(k3_xboole_0(B_43, A_42), A_42))), inference(superposition, [status(thm), theory('equality')], [c_99, c_174])).
% 2.33/1.36  tff(c_476, plain, (![C_84, A_85, B_86]: (r1_tarski(k5_relat_1(C_84, A_85), k5_relat_1(C_84, B_86)) | ~r1_tarski(A_85, B_86) | ~v1_relat_1(C_84) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.33/1.36  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.33/1.36  tff(c_356, plain, (![C_74, A_75, B_76]: (r1_tarski(k5_relat_1(C_74, A_75), k5_relat_1(C_74, B_76)) | ~r1_tarski(A_75, B_76) | ~v1_relat_1(C_74) | ~v1_relat_1(B_76) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.33/1.36  tff(c_222, plain, (![A_62, B_63, C_64]: (r1_tarski(A_62, k3_xboole_0(B_63, C_64)) | ~r1_tarski(A_62, C_64) | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.36  tff(c_22, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.33/1.36  tff(c_116, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_99, c_22])).
% 2.33/1.36  tff(c_236, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_222, c_116])).
% 2.33/1.36  tff(c_263, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_236])).
% 2.33/1.36  tff(c_359, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_356, c_263])).
% 2.33/1.36  tff(c_365, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_165, c_359])).
% 2.33/1.36  tff(c_369, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_210, c_365])).
% 2.33/1.36  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_369])).
% 2.33/1.36  tff(c_377, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_236])).
% 2.33/1.36  tff(c_479, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_476, c_377])).
% 2.33/1.36  tff(c_485, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_177, c_479])).
% 2.33/1.36  tff(c_489, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_210, c_485])).
% 2.33/1.36  tff(c_496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_489])).
% 2.33/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.36  
% 2.33/1.36  Inference rules
% 2.33/1.36  ----------------------
% 2.33/1.36  #Ref     : 0
% 2.33/1.36  #Sup     : 117
% 2.33/1.36  #Fact    : 0
% 2.33/1.36  #Define  : 0
% 2.33/1.36  #Split   : 2
% 2.33/1.36  #Chain   : 0
% 2.33/1.36  #Close   : 0
% 2.33/1.36  
% 2.33/1.36  Ordering : KBO
% 2.33/1.36  
% 2.33/1.36  Simplification rules
% 2.33/1.36  ----------------------
% 2.33/1.36  #Subsume      : 21
% 2.33/1.36  #Demod        : 32
% 2.33/1.36  #Tautology    : 61
% 2.33/1.36  #SimpNegUnit  : 0
% 2.33/1.36  #BackRed      : 1
% 2.33/1.36  
% 2.33/1.36  #Partial instantiations: 0
% 2.33/1.36  #Strategies tried      : 1
% 2.33/1.36  
% 2.33/1.36  Timing (in seconds)
% 2.33/1.36  ----------------------
% 2.54/1.36  Preprocessing        : 0.28
% 2.54/1.36  Parsing              : 0.15
% 2.54/1.36  CNF conversion       : 0.02
% 2.54/1.36  Main loop            : 0.25
% 2.54/1.36  Inferencing          : 0.10
% 2.54/1.36  Reduction            : 0.09
% 2.54/1.36  Demodulation         : 0.07
% 2.54/1.36  BG Simplification    : 0.01
% 2.54/1.36  Subsumption          : 0.04
% 2.54/1.36  Abstraction          : 0.02
% 2.54/1.36  MUC search           : 0.00
% 2.54/1.36  Cooper               : 0.00
% 2.54/1.36  Total                : 0.57
% 2.54/1.36  Index Insertion      : 0.00
% 2.54/1.36  Index Deletion       : 0.00
% 2.54/1.36  Index Matching       : 0.00
% 2.54/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
