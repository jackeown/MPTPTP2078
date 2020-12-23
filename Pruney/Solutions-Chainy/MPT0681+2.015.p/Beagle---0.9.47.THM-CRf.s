%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:27 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   53 (  66 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 119 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

tff(c_24,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_69,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ r1_xboole_0(A_26,B_27)
      | ~ r2_hidden(C_28,k3_xboole_0(A_26,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73,plain,(
    ! [A_29,C_30] :
      ( ~ r1_xboole_0(A_29,A_29)
      | ~ r2_hidden(C_30,A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_69])).

tff(c_77,plain,(
    ! [C_30] : ~ r2_hidden(C_30,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_73])).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_79,plain,(
    ! [B_32,A_33] :
      ( k9_relat_1(B_32,A_33) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_32),A_33)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_85,plain,(
    ! [B_34] :
      ( k9_relat_1(B_34,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_8,c_79])).

tff(c_89,plain,(
    k9_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_85])).

tff(c_28,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_90,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_1'(A_35,B_36),k3_xboole_0(A_35,B_36))
      | r1_xboole_0(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_102,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_1'(A_37,A_37),A_37)
      | r1_xboole_0(A_37,A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_90])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_164,plain,(
    ! [A_44,B_45] :
      ( ~ r1_xboole_0(A_44,B_45)
      | r1_xboole_0(k3_xboole_0(A_44,B_45),k3_xboole_0(A_44,B_45)) ) ),
    inference(resolution,[status(thm)],[c_102,c_6])).

tff(c_12,plain,(
    ! [A_9] :
      ( ~ r1_xboole_0(A_9,A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_186,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = k1_xboole_0
      | ~ r1_xboole_0(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_164,c_12])).

tff(c_203,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_186])).

tff(c_128,plain,(
    ! [C_40,A_41,B_42] :
      ( k3_xboole_0(k9_relat_1(C_40,A_41),k9_relat_1(C_40,B_42)) = k9_relat_1(C_40,k3_xboole_0(A_41,B_42))
      | ~ v2_funct_1(C_40)
      | ~ v1_funct_1(C_40)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_508,plain,(
    ! [C_65,A_66,B_67] :
      ( r2_hidden('#skF_1'(k9_relat_1(C_65,A_66),k9_relat_1(C_65,B_67)),k9_relat_1(C_65,k3_xboole_0(A_66,B_67)))
      | r1_xboole_0(k9_relat_1(C_65,A_66),k9_relat_1(C_65,B_67))
      | ~ v2_funct_1(C_65)
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_4])).

tff(c_626,plain,(
    ! [C_72] :
      ( r2_hidden('#skF_1'(k9_relat_1(C_72,'#skF_2'),k9_relat_1(C_72,'#skF_3')),k9_relat_1(C_72,k1_xboole_0))
      | r1_xboole_0(k9_relat_1(C_72,'#skF_2'),k9_relat_1(C_72,'#skF_3'))
      | ~ v2_funct_1(C_72)
      | ~ v1_funct_1(C_72)
      | ~ v1_relat_1(C_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_508])).

tff(c_629,plain,
    ( r2_hidden('#skF_1'(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')),k1_xboole_0)
    | r1_xboole_0(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_626])).

tff(c_631,plain,
    ( r2_hidden('#skF_1'(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')),k1_xboole_0)
    | r1_xboole_0(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_629])).

tff(c_633,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_77,c_631])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:17:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.40  
% 2.64/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.40  %$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.64/1.40  
% 2.64/1.40  %Foreground sorts:
% 2.64/1.40  
% 2.64/1.40  
% 2.64/1.40  %Background operators:
% 2.64/1.40  
% 2.64/1.40  
% 2.64/1.40  %Foreground operators:
% 2.64/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.64/1.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.64/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.64/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.64/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.64/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.64/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.64/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.64/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.64/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.64/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.64/1.40  
% 2.64/1.41  tff(f_84, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_funct_1)).
% 2.64/1.41  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.64/1.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.64/1.41  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.64/1.41  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.64/1.41  tff(f_55, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.64/1.41  tff(f_73, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 2.64/1.41  tff(c_24, plain, (~r1_xboole_0(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.64/1.41  tff(c_8, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.64/1.41  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.64/1.41  tff(c_69, plain, (![A_26, B_27, C_28]: (~r1_xboole_0(A_26, B_27) | ~r2_hidden(C_28, k3_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.64/1.41  tff(c_73, plain, (![A_29, C_30]: (~r1_xboole_0(A_29, A_29) | ~r2_hidden(C_30, A_29))), inference(superposition, [status(thm), theory('equality')], [c_2, c_69])).
% 2.64/1.41  tff(c_77, plain, (![C_30]: (~r2_hidden(C_30, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_73])).
% 2.64/1.41  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.64/1.41  tff(c_30, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.64/1.41  tff(c_26, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.64/1.41  tff(c_79, plain, (![B_32, A_33]: (k9_relat_1(B_32, A_33)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_32), A_33) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.64/1.41  tff(c_85, plain, (![B_34]: (k9_relat_1(B_34, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_8, c_79])).
% 2.64/1.41  tff(c_89, plain, (k9_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_85])).
% 2.64/1.41  tff(c_28, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.64/1.41  tff(c_90, plain, (![A_35, B_36]: (r2_hidden('#skF_1'(A_35, B_36), k3_xboole_0(A_35, B_36)) | r1_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.64/1.41  tff(c_102, plain, (![A_37]: (r2_hidden('#skF_1'(A_37, A_37), A_37) | r1_xboole_0(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_2, c_90])).
% 2.64/1.41  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.64/1.41  tff(c_164, plain, (![A_44, B_45]: (~r1_xboole_0(A_44, B_45) | r1_xboole_0(k3_xboole_0(A_44, B_45), k3_xboole_0(A_44, B_45)))), inference(resolution, [status(thm)], [c_102, c_6])).
% 2.64/1.41  tff(c_12, plain, (![A_9]: (~r1_xboole_0(A_9, A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.64/1.41  tff(c_186, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=k1_xboole_0 | ~r1_xboole_0(A_46, B_47))), inference(resolution, [status(thm)], [c_164, c_12])).
% 2.64/1.41  tff(c_203, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_186])).
% 2.64/1.41  tff(c_128, plain, (![C_40, A_41, B_42]: (k3_xboole_0(k9_relat_1(C_40, A_41), k9_relat_1(C_40, B_42))=k9_relat_1(C_40, k3_xboole_0(A_41, B_42)) | ~v2_funct_1(C_40) | ~v1_funct_1(C_40) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.64/1.41  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.64/1.41  tff(c_508, plain, (![C_65, A_66, B_67]: (r2_hidden('#skF_1'(k9_relat_1(C_65, A_66), k9_relat_1(C_65, B_67)), k9_relat_1(C_65, k3_xboole_0(A_66, B_67))) | r1_xboole_0(k9_relat_1(C_65, A_66), k9_relat_1(C_65, B_67)) | ~v2_funct_1(C_65) | ~v1_funct_1(C_65) | ~v1_relat_1(C_65))), inference(superposition, [status(thm), theory('equality')], [c_128, c_4])).
% 2.64/1.41  tff(c_626, plain, (![C_72]: (r2_hidden('#skF_1'(k9_relat_1(C_72, '#skF_2'), k9_relat_1(C_72, '#skF_3')), k9_relat_1(C_72, k1_xboole_0)) | r1_xboole_0(k9_relat_1(C_72, '#skF_2'), k9_relat_1(C_72, '#skF_3')) | ~v2_funct_1(C_72) | ~v1_funct_1(C_72) | ~v1_relat_1(C_72))), inference(superposition, [status(thm), theory('equality')], [c_203, c_508])).
% 2.64/1.41  tff(c_629, plain, (r2_hidden('#skF_1'(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3')), k1_xboole_0) | r1_xboole_0(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_89, c_626])).
% 2.64/1.41  tff(c_631, plain, (r2_hidden('#skF_1'(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3')), k1_xboole_0) | r1_xboole_0(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_629])).
% 2.64/1.41  tff(c_633, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_77, c_631])).
% 2.64/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.41  
% 2.64/1.41  Inference rules
% 2.64/1.41  ----------------------
% 2.64/1.41  #Ref     : 0
% 2.64/1.41  #Sup     : 140
% 2.64/1.41  #Fact    : 0
% 2.64/1.41  #Define  : 0
% 2.64/1.41  #Split   : 0
% 2.64/1.41  #Chain   : 0
% 2.64/1.41  #Close   : 0
% 2.64/1.41  
% 2.64/1.41  Ordering : KBO
% 2.64/1.41  
% 2.64/1.41  Simplification rules
% 2.64/1.41  ----------------------
% 2.64/1.41  #Subsume      : 18
% 2.64/1.41  #Demod        : 153
% 2.64/1.41  #Tautology    : 62
% 2.64/1.41  #SimpNegUnit  : 6
% 2.64/1.41  #BackRed      : 0
% 2.64/1.41  
% 2.64/1.41  #Partial instantiations: 0
% 2.64/1.41  #Strategies tried      : 1
% 2.64/1.41  
% 2.64/1.41  Timing (in seconds)
% 2.64/1.41  ----------------------
% 2.64/1.42  Preprocessing        : 0.32
% 2.64/1.42  Parsing              : 0.17
% 2.64/1.42  CNF conversion       : 0.02
% 2.64/1.42  Main loop            : 0.33
% 2.64/1.42  Inferencing          : 0.12
% 2.64/1.42  Reduction            : 0.12
% 2.64/1.42  Demodulation         : 0.09
% 2.64/1.42  BG Simplification    : 0.02
% 2.64/1.42  Subsumption          : 0.06
% 2.64/1.42  Abstraction          : 0.02
% 2.64/1.42  MUC search           : 0.00
% 2.64/1.42  Cooper               : 0.00
% 2.64/1.42  Total                : 0.67
% 2.64/1.42  Index Insertion      : 0.00
% 2.64/1.42  Index Deletion       : 0.00
% 2.64/1.42  Index Matching       : 0.00
% 2.64/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
