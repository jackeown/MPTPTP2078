%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:42 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   54 (  62 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  78 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_xboole_0(A_8,k4_xboole_0(C_10,B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_157,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),k3_xboole_0(A_44,B_45))
      | r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,(
    ! [B_31,A_32] : k1_setfam_1(k2_tarski(B_31,A_32)) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_70])).

tff(c_14,plain,(
    ! [A_15,B_16] : k1_setfam_1(k2_tarski(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_91,plain,(
    ! [B_31,A_32] : k3_xboole_0(B_31,A_32) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_14])).

tff(c_142,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,k3_xboole_0(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_145,plain,(
    ! [A_32,B_31,C_37] :
      ( ~ r1_xboole_0(A_32,B_31)
      | ~ r2_hidden(C_37,k3_xboole_0(B_31,A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_142])).

tff(c_172,plain,(
    ! [B_46,A_47] :
      ( ~ r1_xboole_0(B_46,A_47)
      | r1_xboole_0(A_47,B_46) ) ),
    inference(resolution,[status(thm)],[c_157,c_145])).

tff(c_175,plain,(
    ! [C_10,B_9,A_8] :
      ( r1_xboole_0(k4_xboole_0(C_10,B_9),A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_8,c_172])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [C_22,A_20,B_21] :
      ( k7_relat_1(C_22,k6_subset_1(A_20,B_21)) = k6_subset_1(C_22,k7_relat_1(C_22,B_21))
      | ~ r1_tarski(k1_relat_1(C_22),A_20)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_210,plain,(
    ! [C_56,A_57,B_58] :
      ( k7_relat_1(C_56,k4_xboole_0(A_57,B_58)) = k4_xboole_0(C_56,k7_relat_1(C_56,B_58))
      | ~ r1_tarski(k1_relat_1(C_56),A_57)
      | ~ v1_relat_1(C_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_18])).

tff(c_215,plain,(
    ! [C_59,B_60,B_61] :
      ( k7_relat_1(C_59,k4_xboole_0(k2_xboole_0(k1_relat_1(C_59),B_60),B_61)) = k4_xboole_0(C_59,k7_relat_1(C_59,B_61))
      | ~ v1_relat_1(C_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_210])).

tff(c_16,plain,(
    ! [C_19,A_17,B_18] :
      ( k7_relat_1(k7_relat_1(C_19,A_17),B_18) = k1_xboole_0
      | ~ r1_xboole_0(A_17,B_18)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_252,plain,(
    ! [C_76,B_77,B_78,B_79] :
      ( k7_relat_1(k4_xboole_0(C_76,k7_relat_1(C_76,B_77)),B_78) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_76),B_79),B_77),B_78)
      | ~ v1_relat_1(C_76)
      | ~ v1_relat_1(C_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_16])).

tff(c_261,plain,(
    ! [C_80,B_81,A_82] :
      ( k7_relat_1(k4_xboole_0(C_80,k7_relat_1(C_80,B_81)),A_82) = k1_xboole_0
      | ~ v1_relat_1(C_80)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(resolution,[status(thm)],[c_175,c_252])).

tff(c_20,plain,(
    k7_relat_1(k6_subset_1('#skF_4',k7_relat_1('#skF_4','#skF_3')),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    k7_relat_1(k4_xboole_0('#skF_4',k7_relat_1('#skF_4','#skF_3')),'#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20])).

tff(c_281,plain,
    ( ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_26])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:01:19 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.23  
% 2.10/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.10/1.24  
% 2.10/1.24  %Foreground sorts:
% 2.10/1.24  
% 2.10/1.24  
% 2.10/1.24  %Background operators:
% 2.10/1.24  
% 2.10/1.24  
% 2.10/1.24  %Foreground operators:
% 2.10/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.10/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.24  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.10/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.10/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.10/1.24  
% 2.10/1.25  tff(f_70, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 2.10/1.25  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.10/1.25  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.10/1.25  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.10/1.25  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.10/1.25  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.10/1.25  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.10/1.25  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 2.10/1.25  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 2.10/1.25  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.10/1.25  tff(c_24, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.10/1.25  tff(c_8, plain, (![A_8, C_10, B_9]: (r1_xboole_0(A_8, k4_xboole_0(C_10, B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.10/1.25  tff(c_157, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), k3_xboole_0(A_44, B_45)) | r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.25  tff(c_10, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.25  tff(c_70, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.10/1.25  tff(c_85, plain, (![B_31, A_32]: (k1_setfam_1(k2_tarski(B_31, A_32))=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_10, c_70])).
% 2.10/1.25  tff(c_14, plain, (![A_15, B_16]: (k1_setfam_1(k2_tarski(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.10/1.25  tff(c_91, plain, (![B_31, A_32]: (k3_xboole_0(B_31, A_32)=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_85, c_14])).
% 2.10/1.25  tff(c_142, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, k3_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.25  tff(c_145, plain, (![A_32, B_31, C_37]: (~r1_xboole_0(A_32, B_31) | ~r2_hidden(C_37, k3_xboole_0(B_31, A_32)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_142])).
% 2.10/1.25  tff(c_172, plain, (![B_46, A_47]: (~r1_xboole_0(B_46, A_47) | r1_xboole_0(A_47, B_46))), inference(resolution, [status(thm)], [c_157, c_145])).
% 2.10/1.25  tff(c_175, plain, (![C_10, B_9, A_8]: (r1_xboole_0(k4_xboole_0(C_10, B_9), A_8) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_8, c_172])).
% 2.10/1.25  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.25  tff(c_12, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.10/1.25  tff(c_18, plain, (![C_22, A_20, B_21]: (k7_relat_1(C_22, k6_subset_1(A_20, B_21))=k6_subset_1(C_22, k7_relat_1(C_22, B_21)) | ~r1_tarski(k1_relat_1(C_22), A_20) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.10/1.25  tff(c_210, plain, (![C_56, A_57, B_58]: (k7_relat_1(C_56, k4_xboole_0(A_57, B_58))=k4_xboole_0(C_56, k7_relat_1(C_56, B_58)) | ~r1_tarski(k1_relat_1(C_56), A_57) | ~v1_relat_1(C_56))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_18])).
% 2.10/1.25  tff(c_215, plain, (![C_59, B_60, B_61]: (k7_relat_1(C_59, k4_xboole_0(k2_xboole_0(k1_relat_1(C_59), B_60), B_61))=k4_xboole_0(C_59, k7_relat_1(C_59, B_61)) | ~v1_relat_1(C_59))), inference(resolution, [status(thm)], [c_6, c_210])).
% 2.10/1.25  tff(c_16, plain, (![C_19, A_17, B_18]: (k7_relat_1(k7_relat_1(C_19, A_17), B_18)=k1_xboole_0 | ~r1_xboole_0(A_17, B_18) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.10/1.25  tff(c_252, plain, (![C_76, B_77, B_78, B_79]: (k7_relat_1(k4_xboole_0(C_76, k7_relat_1(C_76, B_77)), B_78)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k2_xboole_0(k1_relat_1(C_76), B_79), B_77), B_78) | ~v1_relat_1(C_76) | ~v1_relat_1(C_76))), inference(superposition, [status(thm), theory('equality')], [c_215, c_16])).
% 2.10/1.25  tff(c_261, plain, (![C_80, B_81, A_82]: (k7_relat_1(k4_xboole_0(C_80, k7_relat_1(C_80, B_81)), A_82)=k1_xboole_0 | ~v1_relat_1(C_80) | ~r1_tarski(A_82, B_81))), inference(resolution, [status(thm)], [c_175, c_252])).
% 2.10/1.25  tff(c_20, plain, (k7_relat_1(k6_subset_1('#skF_4', k7_relat_1('#skF_4', '#skF_3')), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.10/1.25  tff(c_26, plain, (k7_relat_1(k4_xboole_0('#skF_4', k7_relat_1('#skF_4', '#skF_3')), '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20])).
% 2.10/1.25  tff(c_281, plain, (~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_261, c_26])).
% 2.10/1.25  tff(c_302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_281])).
% 2.10/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  Inference rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Ref     : 0
% 2.10/1.25  #Sup     : 72
% 2.10/1.25  #Fact    : 0
% 2.10/1.25  #Define  : 0
% 2.10/1.25  #Split   : 0
% 2.10/1.25  #Chain   : 0
% 2.10/1.25  #Close   : 0
% 2.10/1.25  
% 2.10/1.25  Ordering : KBO
% 2.10/1.25  
% 2.10/1.25  Simplification rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Subsume      : 10
% 2.10/1.25  #Demod        : 8
% 2.10/1.25  #Tautology    : 32
% 2.10/1.25  #SimpNegUnit  : 0
% 2.10/1.25  #BackRed      : 0
% 2.10/1.25  
% 2.10/1.25  #Partial instantiations: 0
% 2.10/1.25  #Strategies tried      : 1
% 2.10/1.25  
% 2.10/1.25  Timing (in seconds)
% 2.10/1.25  ----------------------
% 2.10/1.25  Preprocessing        : 0.29
% 2.10/1.25  Parsing              : 0.16
% 2.10/1.25  CNF conversion       : 0.02
% 2.10/1.25  Main loop            : 0.20
% 2.10/1.25  Inferencing          : 0.08
% 2.10/1.25  Reduction            : 0.06
% 2.10/1.25  Demodulation         : 0.05
% 2.10/1.25  BG Simplification    : 0.01
% 2.10/1.25  Subsumption          : 0.03
% 2.10/1.25  Abstraction          : 0.01
% 2.10/1.25  MUC search           : 0.00
% 2.10/1.25  Cooper               : 0.00
% 2.10/1.25  Total                : 0.52
% 2.10/1.25  Index Insertion      : 0.00
% 2.10/1.25  Index Deletion       : 0.00
% 2.10/1.26  Index Matching       : 0.00
% 2.10/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
