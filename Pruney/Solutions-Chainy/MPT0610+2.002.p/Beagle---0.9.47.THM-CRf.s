%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:36 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   56 (  67 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   65 (  91 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   1 average)

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

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_57,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_92,plain,(
    ! [B_38,A_39] : k3_xboole_0(B_38,A_39) = k3_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k3_xboole_0(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_107,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(k3_xboole_0(B_38,A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_32])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_253,plain,(
    ! [A_46,B_47] :
      ( r1_xboole_0(A_46,B_47)
      | k3_xboole_0(A_46,B_47) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_261,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_253,c_42])).

tff(c_265,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_261])).

tff(c_22,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_138,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_154,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_138])).

tff(c_28,plain,(
    ! [B_17] : k2_zfmisc_1(k1_xboole_0,B_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_44,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_153,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),k1_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_138])).

tff(c_581,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_73,B_74)),k3_xboole_0(k1_relat_1(A_73),k1_relat_1(B_74)))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_598,plain,
    ( r1_tarski(k1_relat_1(k3_xboole_0('#skF_2','#skF_3')),k1_xboole_0)
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_581])).

tff(c_622,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_3','#skF_2')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2,c_598])).

tff(c_20,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_356,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_361,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_356])).

tff(c_632,plain,(
    k1_relat_1(k3_xboole_0('#skF_3','#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_622,c_361])).

tff(c_36,plain,(
    ! [A_25] :
      ( k3_xboole_0(A_25,k2_zfmisc_1(k1_relat_1(A_25),k2_relat_1(A_25))) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_650,plain,
    ( k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k3_xboole_0('#skF_3','#skF_2')))) = k3_xboole_0('#skF_3','#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_36])).

tff(c_657,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_28,c_650])).

tff(c_658,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_657])).

tff(c_662,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_107,c_658])).

tff(c_669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.43  
% 2.67/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.67/1.43  
% 2.67/1.43  %Foreground sorts:
% 2.67/1.43  
% 2.67/1.43  
% 2.67/1.43  %Background operators:
% 2.67/1.43  
% 2.67/1.43  
% 2.67/1.43  %Foreground operators:
% 2.67/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.67/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.67/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.67/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.67/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.67/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.67/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.67/1.43  
% 2.67/1.44  tff(f_98, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t214_relat_1)).
% 2.67/1.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.67/1.44  tff(f_71, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.67/1.44  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.67/1.44  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.67/1.44  tff(f_65, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.67/1.44  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 2.67/1.44  tff(f_57, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.67/1.44  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.67/1.44  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 2.67/1.44  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.67/1.44  tff(c_92, plain, (![B_38, A_39]: (k3_xboole_0(B_38, A_39)=k3_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.44  tff(c_32, plain, (![A_20, B_21]: (v1_relat_1(k3_xboole_0(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.67/1.44  tff(c_107, plain, (![B_38, A_39]: (v1_relat_1(k3_xboole_0(B_38, A_39)) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_92, c_32])).
% 2.67/1.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.44  tff(c_253, plain, (![A_46, B_47]: (r1_xboole_0(A_46, B_47) | k3_xboole_0(A_46, B_47)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.44  tff(c_42, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.67/1.44  tff(c_261, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_253, c_42])).
% 2.67/1.44  tff(c_265, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_261])).
% 2.67/1.44  tff(c_22, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.44  tff(c_138, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.44  tff(c_154, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_138])).
% 2.67/1.44  tff(c_28, plain, (![B_17]: (k2_zfmisc_1(k1_xboole_0, B_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.67/1.44  tff(c_46, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.67/1.44  tff(c_44, plain, (r1_xboole_0(k1_relat_1('#skF_2'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.67/1.44  tff(c_153, plain, (k3_xboole_0(k1_relat_1('#skF_2'), k1_relat_1('#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_138])).
% 2.67/1.44  tff(c_581, plain, (![A_73, B_74]: (r1_tarski(k1_relat_1(k3_xboole_0(A_73, B_74)), k3_xboole_0(k1_relat_1(A_73), k1_relat_1(B_74))) | ~v1_relat_1(B_74) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.67/1.44  tff(c_598, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_2', '#skF_3')), k1_xboole_0) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_153, c_581])).
% 2.67/1.44  tff(c_622, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_3', '#skF_2')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2, c_598])).
% 2.67/1.44  tff(c_20, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.67/1.44  tff(c_356, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.67/1.44  tff(c_361, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_356])).
% 2.67/1.44  tff(c_632, plain, (k1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_622, c_361])).
% 2.67/1.44  tff(c_36, plain, (![A_25]: (k3_xboole_0(A_25, k2_zfmisc_1(k1_relat_1(A_25), k2_relat_1(A_25)))=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.67/1.44  tff(c_650, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k3_xboole_0('#skF_3', '#skF_2'))))=k3_xboole_0('#skF_3', '#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_632, c_36])).
% 2.67/1.44  tff(c_657, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_28, c_650])).
% 2.67/1.44  tff(c_658, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_265, c_657])).
% 2.67/1.44  tff(c_662, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_107, c_658])).
% 2.67/1.44  tff(c_669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_662])).
% 2.67/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.44  
% 2.67/1.44  Inference rules
% 2.67/1.44  ----------------------
% 2.67/1.44  #Ref     : 0
% 2.67/1.44  #Sup     : 147
% 2.67/1.44  #Fact    : 0
% 2.67/1.44  #Define  : 0
% 2.67/1.44  #Split   : 4
% 2.67/1.44  #Chain   : 0
% 2.67/1.44  #Close   : 0
% 2.67/1.44  
% 2.67/1.44  Ordering : KBO
% 2.67/1.44  
% 2.67/1.44  Simplification rules
% 2.67/1.44  ----------------------
% 2.67/1.44  #Subsume      : 22
% 2.67/1.44  #Demod        : 64
% 2.67/1.44  #Tautology    : 80
% 2.67/1.44  #SimpNegUnit  : 16
% 2.67/1.44  #BackRed      : 3
% 2.67/1.44  
% 2.67/1.44  #Partial instantiations: 0
% 2.67/1.44  #Strategies tried      : 1
% 2.67/1.44  
% 2.67/1.44  Timing (in seconds)
% 2.67/1.44  ----------------------
% 2.67/1.44  Preprocessing        : 0.31
% 2.67/1.44  Parsing              : 0.18
% 2.67/1.44  CNF conversion       : 0.02
% 2.67/1.45  Main loop            : 0.33
% 2.67/1.45  Inferencing          : 0.11
% 2.67/1.45  Reduction            : 0.11
% 2.67/1.45  Demodulation         : 0.09
% 2.67/1.45  BG Simplification    : 0.02
% 2.67/1.45  Subsumption          : 0.06
% 2.67/1.45  Abstraction          : 0.01
% 2.67/1.45  MUC search           : 0.00
% 2.67/1.45  Cooper               : 0.00
% 2.67/1.45  Total                : 0.67
% 2.67/1.45  Index Insertion      : 0.00
% 2.67/1.45  Index Deletion       : 0.00
% 2.67/1.45  Index Matching       : 0.00
% 2.67/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
