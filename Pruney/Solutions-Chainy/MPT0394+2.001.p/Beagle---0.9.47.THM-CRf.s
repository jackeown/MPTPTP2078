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
% DateTime   : Thu Dec  3 09:57:21 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 111 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   62 ( 137 expanded)
%              Number of equality atoms :   45 (  92 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_73,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_93,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_91,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_193,plain,(
    ! [B_51,A_52] : k3_xboole_0(B_51,A_52) = k3_xboole_0(A_52,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_209,plain,(
    ! [A_52] : k3_xboole_0(k1_xboole_0,A_52) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_42])).

tff(c_425,plain,(
    ! [B_81,A_82] :
      ( r2_hidden(B_81,A_82)
      | k3_xboole_0(A_82,k1_tarski(B_81)) != k1_tarski(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_444,plain,(
    ! [B_83] :
      ( r2_hidden(B_83,k1_xboole_0)
      | k1_tarski(B_83) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_425])).

tff(c_44,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_286,plain,(
    ! [A_54,B_55] : k4_xboole_0(A_54,k4_xboole_0(A_54,B_55)) = k3_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_305,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_286])).

tff(c_316,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_305])).

tff(c_362,plain,(
    ! [D_62,A_63,B_64] :
      ( r2_hidden(D_62,A_63)
      | ~ r2_hidden(D_62,k4_xboole_0(A_63,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_365,plain,(
    ! [D_62,A_18] :
      ( r2_hidden(D_62,A_18)
      | ~ r2_hidden(D_62,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_362])).

tff(c_449,plain,(
    ! [B_83,A_18] :
      ( r2_hidden(B_83,A_18)
      | k1_tarski(B_83) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_444,c_365])).

tff(c_348,plain,(
    ! [D_57,B_58,A_59] :
      ( ~ r2_hidden(D_57,B_58)
      | ~ r2_hidden(D_57,k4_xboole_0(A_59,B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_357,plain,(
    ! [D_57,A_18] :
      ( ~ r2_hidden(D_57,k1_xboole_0)
      | ~ r2_hidden(D_57,A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_348])).

tff(c_486,plain,(
    ! [B_88,A_89] :
      ( ~ r2_hidden(B_88,A_89)
      | k1_tarski(B_88) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_444,c_357])).

tff(c_499,plain,(
    ! [B_83] : k1_tarski(B_83) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_449,c_486])).

tff(c_78,plain,(
    ! [A_39] : k1_setfam_1(k1_tarski(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_64,plain,(
    ! [A_29,B_30] : k2_xboole_0(k1_tarski(A_29),k1_tarski(B_30)) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1313,plain,(
    ! [A_149,B_150] :
      ( k3_xboole_0(k1_setfam_1(A_149),k1_setfam_1(B_150)) = k1_setfam_1(k2_xboole_0(A_149,B_150))
      | k1_xboole_0 = B_150
      | k1_xboole_0 = A_149 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1357,plain,(
    ! [A_149,A_39] :
      ( k1_setfam_1(k2_xboole_0(A_149,k1_tarski(A_39))) = k3_xboole_0(k1_setfam_1(A_149),A_39)
      | k1_tarski(A_39) = k1_xboole_0
      | k1_xboole_0 = A_149 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_1313])).

tff(c_1961,plain,(
    ! [A_175,A_176] :
      ( k1_setfam_1(k2_xboole_0(A_175,k1_tarski(A_176))) = k3_xboole_0(k1_setfam_1(A_175),A_176)
      | k1_xboole_0 = A_175 ) ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_1357])).

tff(c_1984,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(A_29)),B_30) = k1_setfam_1(k2_tarski(A_29,B_30))
      | k1_tarski(A_29) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1961])).

tff(c_1991,plain,(
    ! [A_29,B_30] :
      ( k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(A_29,B_30)
      | k1_tarski(A_29) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1984])).

tff(c_1992,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_1991])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_80,plain,(
    k1_setfam_1(k2_tarski('#skF_7','#skF_8')) != k3_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_81,plain,(
    k1_setfam_1(k2_tarski('#skF_8','#skF_7')) != k3_xboole_0('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_80])).

tff(c_82,plain,(
    k1_setfam_1(k2_tarski('#skF_8','#skF_7')) != k3_xboole_0('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_81])).

tff(c_2046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1992,c_82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n021.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 18:39:49 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.04/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.82  
% 4.04/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.82  %$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_5
% 4.04/1.82  
% 4.04/1.82  %Foreground sorts:
% 4.04/1.82  
% 4.04/1.82  
% 4.04/1.82  %Background operators:
% 4.04/1.82  
% 4.04/1.82  
% 4.04/1.82  %Foreground operators:
% 4.04/1.82  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.04/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.04/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.04/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.04/1.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.04/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.04/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.04/1.82  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.04/1.82  tff('#skF_7', type, '#skF_7': $i).
% 4.04/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.04/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.04/1.82  tff('#skF_8', type, '#skF_8': $i).
% 4.04/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.04/1.82  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.04/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.04/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.04/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.04/1.82  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.04/1.82  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.04/1.82  
% 4.04/1.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.04/1.83  tff(f_50, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.04/1.83  tff(f_73, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 4.04/1.83  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.04/1.83  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.04/1.83  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.04/1.83  tff(f_93, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 4.04/1.83  tff(f_67, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 4.04/1.83  tff(f_91, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_setfam_1)).
% 4.04/1.83  tff(f_58, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.04/1.83  tff(f_96, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.04/1.83  tff(c_193, plain, (![B_51, A_52]: (k3_xboole_0(B_51, A_52)=k3_xboole_0(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.04/1.83  tff(c_42, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.04/1.83  tff(c_209, plain, (![A_52]: (k3_xboole_0(k1_xboole_0, A_52)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_193, c_42])).
% 4.04/1.83  tff(c_425, plain, (![B_81, A_82]: (r2_hidden(B_81, A_82) | k3_xboole_0(A_82, k1_tarski(B_81))!=k1_tarski(B_81))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.04/1.83  tff(c_444, plain, (![B_83]: (r2_hidden(B_83, k1_xboole_0) | k1_tarski(B_83)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_209, c_425])).
% 4.04/1.83  tff(c_44, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.04/1.83  tff(c_286, plain, (![A_54, B_55]: (k4_xboole_0(A_54, k4_xboole_0(A_54, B_55))=k3_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.04/1.83  tff(c_305, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_286])).
% 4.04/1.83  tff(c_316, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_305])).
% 4.04/1.83  tff(c_362, plain, (![D_62, A_63, B_64]: (r2_hidden(D_62, A_63) | ~r2_hidden(D_62, k4_xboole_0(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.04/1.83  tff(c_365, plain, (![D_62, A_18]: (r2_hidden(D_62, A_18) | ~r2_hidden(D_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_316, c_362])).
% 4.04/1.83  tff(c_449, plain, (![B_83, A_18]: (r2_hidden(B_83, A_18) | k1_tarski(B_83)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_444, c_365])).
% 4.04/1.83  tff(c_348, plain, (![D_57, B_58, A_59]: (~r2_hidden(D_57, B_58) | ~r2_hidden(D_57, k4_xboole_0(A_59, B_58)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.04/1.83  tff(c_357, plain, (![D_57, A_18]: (~r2_hidden(D_57, k1_xboole_0) | ~r2_hidden(D_57, A_18))), inference(superposition, [status(thm), theory('equality')], [c_44, c_348])).
% 4.04/1.83  tff(c_486, plain, (![B_88, A_89]: (~r2_hidden(B_88, A_89) | k1_tarski(B_88)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_444, c_357])).
% 4.04/1.83  tff(c_499, plain, (![B_83]: (k1_tarski(B_83)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_449, c_486])).
% 4.04/1.83  tff(c_78, plain, (![A_39]: (k1_setfam_1(k1_tarski(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.04/1.83  tff(c_64, plain, (![A_29, B_30]: (k2_xboole_0(k1_tarski(A_29), k1_tarski(B_30))=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.04/1.83  tff(c_1313, plain, (![A_149, B_150]: (k3_xboole_0(k1_setfam_1(A_149), k1_setfam_1(B_150))=k1_setfam_1(k2_xboole_0(A_149, B_150)) | k1_xboole_0=B_150 | k1_xboole_0=A_149)), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.04/1.83  tff(c_1357, plain, (![A_149, A_39]: (k1_setfam_1(k2_xboole_0(A_149, k1_tarski(A_39)))=k3_xboole_0(k1_setfam_1(A_149), A_39) | k1_tarski(A_39)=k1_xboole_0 | k1_xboole_0=A_149)), inference(superposition, [status(thm), theory('equality')], [c_78, c_1313])).
% 4.04/1.83  tff(c_1961, plain, (![A_175, A_176]: (k1_setfam_1(k2_xboole_0(A_175, k1_tarski(A_176)))=k3_xboole_0(k1_setfam_1(A_175), A_176) | k1_xboole_0=A_175)), inference(negUnitSimplification, [status(thm)], [c_499, c_1357])).
% 4.04/1.83  tff(c_1984, plain, (![A_29, B_30]: (k3_xboole_0(k1_setfam_1(k1_tarski(A_29)), B_30)=k1_setfam_1(k2_tarski(A_29, B_30)) | k1_tarski(A_29)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_64, c_1961])).
% 4.04/1.83  tff(c_1991, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(A_29, B_30) | k1_tarski(A_29)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1984])).
% 4.04/1.83  tff(c_1992, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(negUnitSimplification, [status(thm)], [c_499, c_1991])).
% 4.04/1.83  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.04/1.83  tff(c_50, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.04/1.83  tff(c_80, plain, (k1_setfam_1(k2_tarski('#skF_7', '#skF_8'))!=k3_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.04/1.83  tff(c_81, plain, (k1_setfam_1(k2_tarski('#skF_8', '#skF_7'))!=k3_xboole_0('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_80])).
% 4.04/1.83  tff(c_82, plain, (k1_setfam_1(k2_tarski('#skF_8', '#skF_7'))!=k3_xboole_0('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_81])).
% 4.04/1.83  tff(c_2046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1992, c_82])).
% 4.04/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/1.83  
% 4.04/1.83  Inference rules
% 4.04/1.83  ----------------------
% 4.04/1.83  #Ref     : 0
% 4.04/1.83  #Sup     : 456
% 4.04/1.83  #Fact    : 6
% 4.04/1.83  #Define  : 0
% 4.04/1.83  #Split   : 0
% 4.04/1.83  #Chain   : 0
% 4.04/1.83  #Close   : 0
% 4.04/1.83  
% 4.04/1.83  Ordering : KBO
% 4.04/1.83  
% 4.04/1.83  Simplification rules
% 4.04/1.83  ----------------------
% 4.04/1.83  #Subsume      : 94
% 4.04/1.83  #Demod        : 201
% 4.04/1.83  #Tautology    : 169
% 4.04/1.83  #SimpNegUnit  : 18
% 4.04/1.83  #BackRed      : 1
% 4.04/1.83  
% 4.04/1.83  #Partial instantiations: 0
% 4.04/1.83  #Strategies tried      : 1
% 4.04/1.83  
% 4.04/1.83  Timing (in seconds)
% 4.04/1.83  ----------------------
% 4.04/1.84  Preprocessing        : 0.42
% 4.04/1.84  Parsing              : 0.21
% 4.04/1.84  CNF conversion       : 0.03
% 4.04/1.84  Main loop            : 0.55
% 4.04/1.84  Inferencing          : 0.18
% 4.04/1.84  Reduction            : 0.20
% 4.04/1.84  Demodulation         : 0.16
% 4.04/1.84  BG Simplification    : 0.03
% 4.04/1.84  Subsumption          : 0.10
% 4.04/1.84  Abstraction          : 0.03
% 4.04/1.84  MUC search           : 0.00
% 4.04/1.84  Cooper               : 0.00
% 4.04/1.84  Total                : 1.00
% 4.04/1.84  Index Insertion      : 0.00
% 4.04/1.84  Index Deletion       : 0.00
% 4.04/1.84  Index Matching       : 0.00
% 4.04/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
