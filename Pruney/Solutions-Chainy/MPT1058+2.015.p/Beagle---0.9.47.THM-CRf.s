%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:24 EST 2020

% Result     : Theorem 13.87s
% Output     : CNFRefutation 13.87s
% Verified   : 
% Statistics : Number of formulae       :   58 (  76 expanded)
%              Number of leaves         :   36 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 (  94 expanded)
%              Number of equality atoms :   22 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_94,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_76,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_72,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') != k10_relat_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_78,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_74,plain,(
    r1_tarski(k10_relat_1('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_60,plain,(
    ! [A_46] : v1_relat_1(k6_relat_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_377,plain,(
    ! [A_90,B_91] : k4_xboole_0(A_90,k4_xboole_0(A_90,B_91)) = k3_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_390,plain,(
    ! [A_90,B_91] : r1_tarski(k3_xboole_0(A_90,B_91),A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_14])).

tff(c_40,plain,(
    ! [A_33] : k2_relat_1(k6_relat_1(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    ! [B_31,A_30] :
      ( k10_relat_1(B_31,k3_xboole_0(k2_relat_1(B_31),A_30)) = k10_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_62,plain,(
    ! [A_46] : v1_funct_1(k6_relat_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2718,plain,(
    ! [B_186,A_187] :
      ( k9_relat_1(B_186,k10_relat_1(B_186,A_187)) = A_187
      | ~ r1_tarski(A_187,k2_relat_1(B_186))
      | ~ v1_funct_1(B_186)
      | ~ v1_relat_1(B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2759,plain,(
    ! [A_33,A_187] :
      ( k9_relat_1(k6_relat_1(A_33),k10_relat_1(k6_relat_1(A_33),A_187)) = A_187
      | ~ r1_tarski(A_187,A_33)
      | ~ v1_funct_1(k6_relat_1(A_33))
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2718])).

tff(c_10308,plain,(
    ! [A_368,A_369] :
      ( k9_relat_1(k6_relat_1(A_368),k10_relat_1(k6_relat_1(A_368),A_369)) = A_369
      | ~ r1_tarski(A_369,A_368) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_2759])).

tff(c_10335,plain,(
    ! [A_368,A_30] :
      ( k9_relat_1(k6_relat_1(A_368),k10_relat_1(k6_relat_1(A_368),A_30)) = k3_xboole_0(k2_relat_1(k6_relat_1(A_368)),A_30)
      | ~ r1_tarski(k3_xboole_0(k2_relat_1(k6_relat_1(A_368)),A_30),A_368)
      | ~ v1_relat_1(k6_relat_1(A_368)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_10308])).

tff(c_10357,plain,(
    ! [A_368,A_30] : k9_relat_1(k6_relat_1(A_368),k10_relat_1(k6_relat_1(A_368),A_30)) = k3_xboole_0(A_368,A_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_390,c_40,c_40,c_10335])).

tff(c_2777,plain,(
    ! [A_33,A_187] :
      ( k9_relat_1(k6_relat_1(A_33),k10_relat_1(k6_relat_1(A_33),A_187)) = A_187
      | ~ r1_tarski(A_187,A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_2759])).

tff(c_35596,plain,(
    ! [A_779,A_780] :
      ( k3_xboole_0(A_779,A_780) = A_780
      | ~ r1_tarski(A_780,A_779) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10357,c_2777])).

tff(c_36159,plain,(
    k3_xboole_0('#skF_5',k10_relat_1('#skF_4','#skF_6')) = k10_relat_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_74,c_35596])).

tff(c_66,plain,(
    ! [A_50,C_52,B_51] :
      ( k3_xboole_0(A_50,k10_relat_1(C_52,B_51)) = k10_relat_1(k7_relat_1(C_52,A_50),B_51)
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36364,plain,
    ( k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_36159,c_66])).

tff(c_36473,plain,(
    k10_relat_1(k7_relat_1('#skF_4','#skF_5'),'#skF_6') = k10_relat_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_36364])).

tff(c_36475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_36473])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:20:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.87/6.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.87/6.02  
% 13.87/6.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.87/6.02  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 13.87/6.02  
% 13.87/6.02  %Foreground sorts:
% 13.87/6.02  
% 13.87/6.02  
% 13.87/6.02  %Background operators:
% 13.87/6.02  
% 13.87/6.02  
% 13.87/6.02  %Foreground operators:
% 13.87/6.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.87/6.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.87/6.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.87/6.02  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.87/6.02  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 13.87/6.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.87/6.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.87/6.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.87/6.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.87/6.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.87/6.02  tff('#skF_5', type, '#skF_5': $i).
% 13.87/6.02  tff('#skF_6', type, '#skF_6': $i).
% 13.87/6.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.87/6.02  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.87/6.02  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 13.87/6.02  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.87/6.02  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.87/6.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.87/6.02  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.87/6.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.87/6.02  tff('#skF_4', type, '#skF_4': $i).
% 13.87/6.02  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 13.87/6.02  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.87/6.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.87/6.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.87/6.02  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 13.87/6.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.87/6.02  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.87/6.02  
% 13.87/6.03  tff(f_127, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 13.87/6.03  tff(f_94, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 13.87/6.03  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.87/6.03  tff(f_44, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 13.87/6.03  tff(f_76, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 13.87/6.03  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 13.87/6.03  tff(f_112, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 13.87/6.03  tff(f_104, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 13.87/6.03  tff(c_72, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k10_relat_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.87/6.03  tff(c_78, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.87/6.03  tff(c_74, plain, (r1_tarski(k10_relat_1('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.87/6.03  tff(c_60, plain, (![A_46]: (v1_relat_1(k6_relat_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.87/6.03  tff(c_377, plain, (![A_90, B_91]: (k4_xboole_0(A_90, k4_xboole_0(A_90, B_91))=k3_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.87/6.03  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.87/6.03  tff(c_390, plain, (![A_90, B_91]: (r1_tarski(k3_xboole_0(A_90, B_91), A_90))), inference(superposition, [status(thm), theory('equality')], [c_377, c_14])).
% 13.87/6.03  tff(c_40, plain, (![A_33]: (k2_relat_1(k6_relat_1(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.87/6.03  tff(c_34, plain, (![B_31, A_30]: (k10_relat_1(B_31, k3_xboole_0(k2_relat_1(B_31), A_30))=k10_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.87/6.03  tff(c_62, plain, (![A_46]: (v1_funct_1(k6_relat_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.87/6.03  tff(c_2718, plain, (![B_186, A_187]: (k9_relat_1(B_186, k10_relat_1(B_186, A_187))=A_187 | ~r1_tarski(A_187, k2_relat_1(B_186)) | ~v1_funct_1(B_186) | ~v1_relat_1(B_186))), inference(cnfTransformation, [status(thm)], [f_112])).
% 13.87/6.03  tff(c_2759, plain, (![A_33, A_187]: (k9_relat_1(k6_relat_1(A_33), k10_relat_1(k6_relat_1(A_33), A_187))=A_187 | ~r1_tarski(A_187, A_33) | ~v1_funct_1(k6_relat_1(A_33)) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2718])).
% 13.87/6.03  tff(c_10308, plain, (![A_368, A_369]: (k9_relat_1(k6_relat_1(A_368), k10_relat_1(k6_relat_1(A_368), A_369))=A_369 | ~r1_tarski(A_369, A_368))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_2759])).
% 13.87/6.03  tff(c_10335, plain, (![A_368, A_30]: (k9_relat_1(k6_relat_1(A_368), k10_relat_1(k6_relat_1(A_368), A_30))=k3_xboole_0(k2_relat_1(k6_relat_1(A_368)), A_30) | ~r1_tarski(k3_xboole_0(k2_relat_1(k6_relat_1(A_368)), A_30), A_368) | ~v1_relat_1(k6_relat_1(A_368)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_10308])).
% 13.87/6.03  tff(c_10357, plain, (![A_368, A_30]: (k9_relat_1(k6_relat_1(A_368), k10_relat_1(k6_relat_1(A_368), A_30))=k3_xboole_0(A_368, A_30))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_390, c_40, c_40, c_10335])).
% 13.87/6.03  tff(c_2777, plain, (![A_33, A_187]: (k9_relat_1(k6_relat_1(A_33), k10_relat_1(k6_relat_1(A_33), A_187))=A_187 | ~r1_tarski(A_187, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_2759])).
% 13.87/6.03  tff(c_35596, plain, (![A_779, A_780]: (k3_xboole_0(A_779, A_780)=A_780 | ~r1_tarski(A_780, A_779))), inference(demodulation, [status(thm), theory('equality')], [c_10357, c_2777])).
% 13.87/6.03  tff(c_36159, plain, (k3_xboole_0('#skF_5', k10_relat_1('#skF_4', '#skF_6'))=k10_relat_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_74, c_35596])).
% 13.87/6.03  tff(c_66, plain, (![A_50, C_52, B_51]: (k3_xboole_0(A_50, k10_relat_1(C_52, B_51))=k10_relat_1(k7_relat_1(C_52, A_50), B_51) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_104])).
% 13.87/6.03  tff(c_36364, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_36159, c_66])).
% 13.87/6.03  tff(c_36473, plain, (k10_relat_1(k7_relat_1('#skF_4', '#skF_5'), '#skF_6')=k10_relat_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_36364])).
% 13.87/6.03  tff(c_36475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_36473])).
% 13.87/6.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.87/6.03  
% 13.87/6.03  Inference rules
% 13.87/6.03  ----------------------
% 13.87/6.03  #Ref     : 0
% 13.87/6.03  #Sup     : 8335
% 13.87/6.03  #Fact    : 0
% 13.87/6.03  #Define  : 0
% 13.87/6.03  #Split   : 0
% 13.87/6.03  #Chain   : 0
% 13.87/6.03  #Close   : 0
% 13.87/6.03  
% 13.87/6.03  Ordering : KBO
% 13.87/6.03  
% 13.87/6.03  Simplification rules
% 13.87/6.03  ----------------------
% 13.87/6.03  #Subsume      : 426
% 13.87/6.03  #Demod        : 10217
% 13.87/6.03  #Tautology    : 5299
% 13.87/6.03  #SimpNegUnit  : 30
% 13.87/6.03  #BackRed      : 2
% 13.87/6.03  
% 13.87/6.03  #Partial instantiations: 0
% 13.87/6.03  #Strategies tried      : 1
% 13.87/6.03  
% 13.87/6.03  Timing (in seconds)
% 13.87/6.03  ----------------------
% 13.87/6.03  Preprocessing        : 0.36
% 13.87/6.03  Parsing              : 0.18
% 13.87/6.03  CNF conversion       : 0.03
% 13.87/6.03  Main loop            : 4.92
% 13.87/6.03  Inferencing          : 0.89
% 13.87/6.03  Reduction            : 2.80
% 13.87/6.03  Demodulation         : 2.49
% 13.87/6.03  BG Simplification    : 0.09
% 13.87/6.03  Subsumption          : 0.91
% 13.87/6.03  Abstraction          : 0.14
% 13.87/6.03  MUC search           : 0.00
% 13.87/6.03  Cooper               : 0.00
% 13.87/6.04  Total                : 5.30
% 13.87/6.04  Index Insertion      : 0.00
% 13.87/6.04  Index Deletion       : 0.00
% 13.87/6.04  Index Matching       : 0.00
% 13.87/6.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
