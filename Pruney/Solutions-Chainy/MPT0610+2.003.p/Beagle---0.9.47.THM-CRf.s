%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:36 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   54 (  69 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   60 (  88 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_79,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k3_xboole_0(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_97,plain,(
    ! [A_35,B_34] :
      ( v1_relat_1(k3_xboole_0(A_35,B_34))
      | ~ v1_relat_1(B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_28])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_280,plain,(
    ! [A_48,B_49] :
      ( r1_xboole_0(A_48,B_49)
      | k3_xboole_0(A_48,B_49) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_288,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_280,c_38])).

tff(c_292,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_288])).

tff(c_16,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_120,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_79])).

tff(c_24,plain,(
    ! [B_17] : k2_zfmisc_1(k1_xboole_0,B_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_212,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = k1_xboole_0
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_228,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),k1_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_212])).

tff(c_554,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_70,B_71)),k3_xboole_0(k1_relat_1(A_70),k1_relat_1(B_71)))
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_572,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0('#skF_2','#skF_3')),k1_xboole_0)
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_554])).

tff(c_596,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_3','#skF_2')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2,c_572])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_603,plain,(
    k3_xboole_0(k1_relat_1(k3_xboole_0('#skF_3','#skF_2')),k1_xboole_0) = k1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_596,c_14])).

tff(c_605,plain,(
    k1_relat_1(k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_603])).

tff(c_32,plain,(
    ! [A_25] :
      ( k3_xboole_0(A_25,k2_zfmisc_1(k1_relat_1(A_25),k2_relat_1(A_25))) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_619,plain,
    ( k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k3_xboole_0('#skF_3','#skF_2')))) = k3_xboole_0('#skF_3','#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_32])).

tff(c_626,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_2,c_24,c_619])).

tff(c_627,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_626])).

tff(c_637,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_97,c_627])).

tff(c_644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_637])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:20:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.41  
% 2.50/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.50/1.41  
% 2.50/1.41  %Foreground sorts:
% 2.50/1.41  
% 2.50/1.41  
% 2.50/1.41  %Background operators:
% 2.50/1.41  
% 2.50/1.41  
% 2.50/1.41  %Foreground operators:
% 2.50/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.50/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.50/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.50/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.50/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.50/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.50/1.41  
% 2.78/1.42  tff(f_96, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t214_relat_1)).
% 2.78/1.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.78/1.42  tff(f_69, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.78/1.42  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.78/1.42  tff(f_55, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.78/1.42  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.78/1.42  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relat_1)).
% 2.78/1.42  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.78/1.42  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 2.78/1.42  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.78/1.42  tff(c_79, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.78/1.42  tff(c_28, plain, (![A_20, B_21]: (v1_relat_1(k3_xboole_0(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.78/1.42  tff(c_97, plain, (![A_35, B_34]: (v1_relat_1(k3_xboole_0(A_35, B_34)) | ~v1_relat_1(B_34))), inference(superposition, [status(thm), theory('equality')], [c_79, c_28])).
% 2.78/1.42  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.78/1.42  tff(c_280, plain, (![A_48, B_49]: (r1_xboole_0(A_48, B_49) | k3_xboole_0(A_48, B_49)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.42  tff(c_38, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.78/1.42  tff(c_288, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_280, c_38])).
% 2.78/1.42  tff(c_292, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_288])).
% 2.78/1.42  tff(c_16, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.78/1.42  tff(c_120, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_79])).
% 2.78/1.42  tff(c_24, plain, (![B_17]: (k2_zfmisc_1(k1_xboole_0, B_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.78/1.42  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.78/1.42  tff(c_40, plain, (r1_xboole_0(k1_relat_1('#skF_2'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.78/1.42  tff(c_212, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=k1_xboole_0 | ~r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.42  tff(c_228, plain, (k3_xboole_0(k1_relat_1('#skF_2'), k1_relat_1('#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_212])).
% 2.78/1.42  tff(c_554, plain, (![A_70, B_71]: (r1_tarski(k1_relat_1(k3_xboole_0(A_70, B_71)), k3_xboole_0(k1_relat_1(A_70), k1_relat_1(B_71))) | ~v1_relat_1(B_71) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.78/1.42  tff(c_572, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_2', '#skF_3')), k1_xboole_0) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_228, c_554])).
% 2.78/1.42  tff(c_596, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_3', '#skF_2')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_2, c_572])).
% 2.78/1.42  tff(c_14, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.78/1.42  tff(c_603, plain, (k3_xboole_0(k1_relat_1(k3_xboole_0('#skF_3', '#skF_2')), k1_xboole_0)=k1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_596, c_14])).
% 2.78/1.42  tff(c_605, plain, (k1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_603])).
% 2.78/1.42  tff(c_32, plain, (![A_25]: (k3_xboole_0(A_25, k2_zfmisc_1(k1_relat_1(A_25), k2_relat_1(A_25)))=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.78/1.42  tff(c_619, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k3_xboole_0('#skF_3', '#skF_2'))))=k3_xboole_0('#skF_3', '#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_605, c_32])).
% 2.78/1.42  tff(c_626, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_2, c_24, c_619])).
% 2.78/1.42  tff(c_627, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_292, c_626])).
% 2.78/1.42  tff(c_637, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_97, c_627])).
% 2.78/1.42  tff(c_644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_637])).
% 2.78/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.42  
% 2.78/1.42  Inference rules
% 2.78/1.42  ----------------------
% 2.78/1.42  #Ref     : 0
% 2.78/1.42  #Sup     : 143
% 2.78/1.42  #Fact    : 0
% 2.78/1.42  #Define  : 0
% 2.78/1.42  #Split   : 5
% 2.78/1.42  #Chain   : 0
% 2.78/1.42  #Close   : 0
% 2.78/1.42  
% 2.78/1.42  Ordering : KBO
% 2.78/1.42  
% 2.78/1.42  Simplification rules
% 2.78/1.42  ----------------------
% 2.78/1.42  #Subsume      : 21
% 2.78/1.43  #Demod        : 70
% 2.78/1.43  #Tautology    : 77
% 2.78/1.43  #SimpNegUnit  : 14
% 2.78/1.43  #BackRed      : 3
% 2.78/1.43  
% 2.78/1.43  #Partial instantiations: 0
% 2.78/1.43  #Strategies tried      : 1
% 2.78/1.43  
% 2.78/1.43  Timing (in seconds)
% 2.78/1.43  ----------------------
% 2.78/1.43  Preprocessing        : 0.29
% 2.78/1.43  Parsing              : 0.16
% 2.78/1.43  CNF conversion       : 0.02
% 2.78/1.43  Main loop            : 0.29
% 2.78/1.43  Inferencing          : 0.10
% 2.78/1.43  Reduction            : 0.10
% 2.78/1.43  Demodulation         : 0.08
% 2.78/1.43  BG Simplification    : 0.01
% 2.78/1.43  Subsumption          : 0.05
% 2.78/1.43  Abstraction          : 0.01
% 2.78/1.43  MUC search           : 0.00
% 2.78/1.43  Cooper               : 0.00
% 2.78/1.43  Total                : 0.62
% 2.78/1.43  Index Insertion      : 0.00
% 2.78/1.43  Index Deletion       : 0.00
% 2.78/1.43  Index Matching       : 0.00
% 2.78/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
