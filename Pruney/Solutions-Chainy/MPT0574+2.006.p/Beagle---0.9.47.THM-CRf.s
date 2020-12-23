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
% DateTime   : Thu Dec  3 10:01:51 EST 2020

% Result     : Theorem 10.47s
% Output     : CNFRefutation 10.47s
% Verified   : 
% Statistics : Number of formulae       :   54 (  57 expanded)
%              Number of leaves         :   28 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 (  63 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_69,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_104,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_119,plain,(
    ! [B_42,A_43] : k3_tarski(k2_tarski(B_42,A_43)) = k2_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_104])).

tff(c_30,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_125,plain,(
    ! [B_42,A_43] : k2_xboole_0(B_42,A_43) = k2_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_30])).

tff(c_8,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_423,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(B_70,C_69)
      | ~ r1_tarski(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_441,plain,(
    ! [A_68] :
      ( r1_tarski(A_68,'#skF_2')
      | ~ r1_tarski(A_68,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_36,c_423])).

tff(c_300,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_xboole_0(A_53,k4_xboole_0(C_54,B_55))
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_11] :
      ( ~ r1_xboole_0(A_11,A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_722,plain,(
    ! [C_96,B_97] :
      ( k4_xboole_0(C_96,B_97) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(C_96,B_97),B_97) ) ),
    inference(resolution,[status(thm)],[c_300,c_18])).

tff(c_960,plain,(
    ! [C_102] :
      ( k4_xboole_0(C_102,'#skF_2') = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(C_102,'#skF_2'),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_441,c_722])).

tff(c_988,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_960])).

tff(c_14,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1019,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_14])).

tff(c_1035,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_8,c_1019])).

tff(c_536,plain,(
    ! [C_78,A_79,B_80] :
      ( k2_xboole_0(k10_relat_1(C_78,A_79),k10_relat_1(C_78,B_80)) = k10_relat_1(C_78,k2_xboole_0(A_79,B_80))
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1569,plain,(
    ! [C_119,A_120,B_121] :
      ( r1_tarski(k10_relat_1(C_119,A_120),k10_relat_1(C_119,k2_xboole_0(A_120,B_121)))
      | ~ v1_relat_1(C_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_20])).

tff(c_29700,plain,(
    ! [C_461] :
      ( r1_tarski(k10_relat_1(C_461,'#skF_1'),k10_relat_1(C_461,'#skF_2'))
      | ~ v1_relat_1(C_461) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1035,c_1569])).

tff(c_34,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_29718,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_29700,c_34])).

tff(c_29729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_29718])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:43:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.47/4.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.47/4.39  
% 10.47/4.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.47/4.40  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.47/4.40  
% 10.47/4.40  %Foreground sorts:
% 10.47/4.40  
% 10.47/4.40  
% 10.47/4.40  %Background operators:
% 10.47/4.40  
% 10.47/4.40  
% 10.47/4.40  %Foreground operators:
% 10.47/4.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.47/4.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.47/4.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.47/4.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.47/4.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.47/4.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.47/4.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.47/4.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.47/4.40  tff('#skF_2', type, '#skF_2': $i).
% 10.47/4.40  tff('#skF_3', type, '#skF_3': $i).
% 10.47/4.40  tff('#skF_1', type, '#skF_1': $i).
% 10.47/4.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.47/4.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.47/4.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.47/4.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.47/4.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.47/4.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.47/4.40  
% 10.47/4.41  tff(f_80, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 10.47/4.41  tff(f_63, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.47/4.41  tff(f_69, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.47/4.41  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 10.47/4.41  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.47/4.41  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.47/4.41  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 10.47/4.41  tff(f_55, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 10.47/4.41  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.47/4.41  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 10.47/4.41  tff(f_57, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.47/4.41  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.47/4.41  tff(c_24, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.47/4.41  tff(c_104, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.47/4.41  tff(c_119, plain, (![B_42, A_43]: (k3_tarski(k2_tarski(B_42, A_43))=k2_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_24, c_104])).
% 10.47/4.41  tff(c_30, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.47/4.41  tff(c_125, plain, (![B_42, A_43]: (k2_xboole_0(B_42, A_43)=k2_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_119, c_30])).
% 10.47/4.41  tff(c_8, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.47/4.41  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.47/4.41  tff(c_36, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.47/4.41  tff(c_423, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(B_70, C_69) | ~r1_tarski(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.47/4.41  tff(c_441, plain, (![A_68]: (r1_tarski(A_68, '#skF_2') | ~r1_tarski(A_68, '#skF_1'))), inference(resolution, [status(thm)], [c_36, c_423])).
% 10.47/4.41  tff(c_300, plain, (![A_53, C_54, B_55]: (r1_xboole_0(A_53, k4_xboole_0(C_54, B_55)) | ~r1_tarski(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.47/4.41  tff(c_18, plain, (![A_11]: (~r1_xboole_0(A_11, A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.47/4.41  tff(c_722, plain, (![C_96, B_97]: (k4_xboole_0(C_96, B_97)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(C_96, B_97), B_97))), inference(resolution, [status(thm)], [c_300, c_18])).
% 10.47/4.41  tff(c_960, plain, (![C_102]: (k4_xboole_0(C_102, '#skF_2')=k1_xboole_0 | ~r1_tarski(k4_xboole_0(C_102, '#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_441, c_722])).
% 10.47/4.41  tff(c_988, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_960])).
% 10.47/4.41  tff(c_14, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.47/4.41  tff(c_1019, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_988, c_14])).
% 10.47/4.41  tff(c_1035, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_8, c_1019])).
% 10.47/4.41  tff(c_536, plain, (![C_78, A_79, B_80]: (k2_xboole_0(k10_relat_1(C_78, A_79), k10_relat_1(C_78, B_80))=k10_relat_1(C_78, k2_xboole_0(A_79, B_80)) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.47/4.41  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.47/4.41  tff(c_1569, plain, (![C_119, A_120, B_121]: (r1_tarski(k10_relat_1(C_119, A_120), k10_relat_1(C_119, k2_xboole_0(A_120, B_121))) | ~v1_relat_1(C_119))), inference(superposition, [status(thm), theory('equality')], [c_536, c_20])).
% 10.47/4.41  tff(c_29700, plain, (![C_461]: (r1_tarski(k10_relat_1(C_461, '#skF_1'), k10_relat_1(C_461, '#skF_2')) | ~v1_relat_1(C_461))), inference(superposition, [status(thm), theory('equality')], [c_1035, c_1569])).
% 10.47/4.41  tff(c_34, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.47/4.41  tff(c_29718, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_29700, c_34])).
% 10.47/4.41  tff(c_29729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_29718])).
% 10.47/4.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.47/4.41  
% 10.47/4.41  Inference rules
% 10.47/4.41  ----------------------
% 10.47/4.41  #Ref     : 0
% 10.47/4.41  #Sup     : 7396
% 10.47/4.41  #Fact    : 0
% 10.47/4.41  #Define  : 0
% 10.47/4.41  #Split   : 2
% 10.47/4.41  #Chain   : 0
% 10.47/4.41  #Close   : 0
% 10.47/4.41  
% 10.47/4.41  Ordering : KBO
% 10.47/4.41  
% 10.47/4.41  Simplification rules
% 10.47/4.41  ----------------------
% 10.47/4.41  #Subsume      : 1361
% 10.47/4.41  #Demod        : 6564
% 10.47/4.41  #Tautology    : 4245
% 10.47/4.41  #SimpNegUnit  : 0
% 10.47/4.41  #BackRed      : 0
% 10.47/4.41  
% 10.47/4.41  #Partial instantiations: 0
% 10.47/4.41  #Strategies tried      : 1
% 10.47/4.41  
% 10.47/4.41  Timing (in seconds)
% 10.47/4.41  ----------------------
% 10.47/4.41  Preprocessing        : 0.30
% 10.47/4.41  Parsing              : 0.16
% 10.47/4.41  CNF conversion       : 0.02
% 10.47/4.41  Main loop            : 3.35
% 10.47/4.41  Inferencing          : 0.64
% 10.47/4.41  Reduction            : 1.72
% 10.47/4.41  Demodulation         : 1.49
% 10.47/4.41  BG Simplification    : 0.07
% 10.47/4.41  Subsumption          : 0.76
% 10.47/4.41  Abstraction          : 0.11
% 10.47/4.41  MUC search           : 0.00
% 10.47/4.41  Cooper               : 0.00
% 10.47/4.41  Total                : 3.68
% 10.47/4.41  Index Insertion      : 0.00
% 10.47/4.41  Index Deletion       : 0.00
% 10.47/4.41  Index Matching       : 0.00
% 10.47/4.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
