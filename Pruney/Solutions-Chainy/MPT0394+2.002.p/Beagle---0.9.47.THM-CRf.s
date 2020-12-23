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
% DateTime   : Thu Dec  3 09:57:21 EST 2020

% Result     : Theorem 6.44s
% Output     : CNFRefutation 6.58s
% Verified   : 
% Statistics : Number of formulae       :   57 (  85 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 (  95 expanded)
%              Number of equality atoms :   45 (  70 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_88,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_105,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_103,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & k1_setfam_1(k2_xboole_0(A,B)) != k3_xboole_0(k1_setfam_1(A),k1_setfam_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_126,plain,(
    ! [A_65] : k2_tarski(A_65,A_65) = k1_tarski(A_65) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,(
    ! [D_44,A_39] : r2_hidden(D_44,k2_tarski(A_39,D_44)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_132,plain,(
    ! [A_65] : r2_hidden(A_65,k1_tarski(A_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_42])).

tff(c_68,plain,(
    ! [A_52] : k1_setfam_1(k1_tarski(A_52)) = A_52 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_433,plain,(
    ! [B_89,A_90] :
      ( r1_tarski(k1_setfam_1(B_89),A_90)
      | ~ r2_hidden(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_441,plain,(
    ! [A_91,A_92] :
      ( r1_tarski(A_91,A_92)
      | ~ r2_hidden(A_92,k1_tarski(A_91)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_433])).

tff(c_446,plain,(
    ! [A_93] : r1_tarski(A_93,A_93) ),
    inference(resolution,[status(thm)],[c_132,c_441])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_450,plain,(
    ! [A_93] : k4_xboole_0(A_93,A_93) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_446,c_10])).

tff(c_62,plain,(
    ! [B_49] : k4_xboole_0(k1_tarski(B_49),k1_tarski(B_49)) != k1_tarski(B_49) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_463,plain,(
    ! [B_49] : k1_tarski(B_49) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_62])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_523,plain,(
    ! [A_101,B_102] : k2_xboole_0(k1_tarski(A_101),k1_tarski(B_102)) = k2_tarski(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_541,plain,(
    ! [B_102,A_101] : k2_xboole_0(k1_tarski(B_102),k1_tarski(A_101)) = k2_tarski(A_101,B_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_523])).

tff(c_2110,plain,(
    ! [A_151,B_152] :
      ( k3_xboole_0(k1_setfam_1(A_151),k1_setfam_1(B_152)) = k1_setfam_1(k2_xboole_0(A_151,B_152))
      | k1_xboole_0 = B_152
      | k1_xboole_0 = A_151 ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2169,plain,(
    ! [A_151,A_52] :
      ( k1_setfam_1(k2_xboole_0(A_151,k1_tarski(A_52))) = k3_xboole_0(k1_setfam_1(A_151),A_52)
      | k1_tarski(A_52) = k1_xboole_0
      | k1_xboole_0 = A_151 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2110])).

tff(c_7743,plain,(
    ! [A_3798,A_3799] :
      ( k1_setfam_1(k2_xboole_0(A_3798,k1_tarski(A_3799))) = k3_xboole_0(k1_setfam_1(A_3798),A_3799)
      | k1_xboole_0 = A_3798 ) ),
    inference(negUnitSimplification,[status(thm)],[c_463,c_2169])).

tff(c_7780,plain,(
    ! [B_102,A_101] :
      ( k3_xboole_0(k1_setfam_1(k1_tarski(B_102)),A_101) = k1_setfam_1(k2_tarski(A_101,B_102))
      | k1_tarski(B_102) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_7743])).

tff(c_7809,plain,(
    ! [A_101,B_102] :
      ( k1_setfam_1(k2_tarski(A_101,B_102)) = k3_xboole_0(B_102,A_101)
      | k1_tarski(B_102) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_7780])).

tff(c_7810,plain,(
    ! [A_101,B_102] : k1_setfam_1(k2_tarski(A_101,B_102)) = k3_xboole_0(B_102,A_101) ),
    inference(negUnitSimplification,[status(thm)],[c_463,c_7809])).

tff(c_4831,plain,(
    ! [B_2709,A_2710] : k2_xboole_0(k1_tarski(B_2709),k1_tarski(A_2710)) = k2_tarski(A_2710,B_2709) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_523])).

tff(c_58,plain,(
    ! [A_45,B_46] : k2_xboole_0(k1_tarski(A_45),k1_tarski(B_46)) = k2_tarski(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4868,plain,(
    ! [B_2709,A_2710] : k2_tarski(B_2709,A_2710) = k2_tarski(A_2710,B_2709) ),
    inference(superposition,[status(thm),theory(equality)],[c_4831,c_58])).

tff(c_72,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_73,plain,(
    k1_setfam_1(k2_tarski('#skF_3','#skF_4')) != k3_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_72])).

tff(c_4929,plain,(
    k1_setfam_1(k2_tarski('#skF_4','#skF_3')) != k3_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4868,c_73])).

tff(c_7817,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k3_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7810,c_4929])).

tff(c_7820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_7817])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.44/2.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.44/2.42  
% 6.44/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.58/2.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 6.58/2.43  
% 6.58/2.43  %Foreground sorts:
% 6.58/2.43  
% 6.58/2.43  
% 6.58/2.43  %Background operators:
% 6.58/2.43  
% 6.58/2.43  
% 6.58/2.43  %Foreground operators:
% 6.58/2.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.58/2.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.58/2.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.58/2.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.58/2.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.58/2.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.58/2.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.58/2.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.58/2.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.58/2.43  tff('#skF_3', type, '#skF_3': $i).
% 6.58/2.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.58/2.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.58/2.43  tff('#skF_4', type, '#skF_4': $i).
% 6.58/2.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.58/2.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.58/2.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.58/2.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.58/2.43  
% 6.58/2.44  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.58/2.44  tff(f_88, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.58/2.44  tff(f_84, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 6.58/2.44  tff(f_105, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 6.58/2.44  tff(f_109, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 6.58/2.44  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.58/2.44  tff(f_93, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 6.58/2.44  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.58/2.44  tff(f_86, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 6.58/2.44  tff(f_103, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(k1_setfam_1(k2_xboole_0(A, B)) = k3_xboole_0(k1_setfam_1(A), k1_setfam_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_setfam_1)).
% 6.58/2.44  tff(f_112, negated_conjecture, ~(![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.58/2.44  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.58/2.44  tff(c_126, plain, (![A_65]: (k2_tarski(A_65, A_65)=k1_tarski(A_65))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.58/2.44  tff(c_42, plain, (![D_44, A_39]: (r2_hidden(D_44, k2_tarski(A_39, D_44)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.58/2.44  tff(c_132, plain, (![A_65]: (r2_hidden(A_65, k1_tarski(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_42])).
% 6.58/2.44  tff(c_68, plain, (![A_52]: (k1_setfam_1(k1_tarski(A_52))=A_52)), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.58/2.44  tff(c_433, plain, (![B_89, A_90]: (r1_tarski(k1_setfam_1(B_89), A_90) | ~r2_hidden(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.58/2.44  tff(c_441, plain, (![A_91, A_92]: (r1_tarski(A_91, A_92) | ~r2_hidden(A_92, k1_tarski(A_91)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_433])).
% 6.58/2.44  tff(c_446, plain, (![A_93]: (r1_tarski(A_93, A_93))), inference(resolution, [status(thm)], [c_132, c_441])).
% 6.58/2.44  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.58/2.44  tff(c_450, plain, (![A_93]: (k4_xboole_0(A_93, A_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_446, c_10])).
% 6.58/2.44  tff(c_62, plain, (![B_49]: (k4_xboole_0(k1_tarski(B_49), k1_tarski(B_49))!=k1_tarski(B_49))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.58/2.44  tff(c_463, plain, (![B_49]: (k1_tarski(B_49)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_450, c_62])).
% 6.58/2.44  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.58/2.44  tff(c_523, plain, (![A_101, B_102]: (k2_xboole_0(k1_tarski(A_101), k1_tarski(B_102))=k2_tarski(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.58/2.44  tff(c_541, plain, (![B_102, A_101]: (k2_xboole_0(k1_tarski(B_102), k1_tarski(A_101))=k2_tarski(A_101, B_102))), inference(superposition, [status(thm), theory('equality')], [c_2, c_523])).
% 6.58/2.44  tff(c_2110, plain, (![A_151, B_152]: (k3_xboole_0(k1_setfam_1(A_151), k1_setfam_1(B_152))=k1_setfam_1(k2_xboole_0(A_151, B_152)) | k1_xboole_0=B_152 | k1_xboole_0=A_151)), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.58/2.44  tff(c_2169, plain, (![A_151, A_52]: (k1_setfam_1(k2_xboole_0(A_151, k1_tarski(A_52)))=k3_xboole_0(k1_setfam_1(A_151), A_52) | k1_tarski(A_52)=k1_xboole_0 | k1_xboole_0=A_151)), inference(superposition, [status(thm), theory('equality')], [c_68, c_2110])).
% 6.58/2.44  tff(c_7743, plain, (![A_3798, A_3799]: (k1_setfam_1(k2_xboole_0(A_3798, k1_tarski(A_3799)))=k3_xboole_0(k1_setfam_1(A_3798), A_3799) | k1_xboole_0=A_3798)), inference(negUnitSimplification, [status(thm)], [c_463, c_2169])).
% 6.58/2.44  tff(c_7780, plain, (![B_102, A_101]: (k3_xboole_0(k1_setfam_1(k1_tarski(B_102)), A_101)=k1_setfam_1(k2_tarski(A_101, B_102)) | k1_tarski(B_102)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_541, c_7743])).
% 6.58/2.44  tff(c_7809, plain, (![A_101, B_102]: (k1_setfam_1(k2_tarski(A_101, B_102))=k3_xboole_0(B_102, A_101) | k1_tarski(B_102)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_7780])).
% 6.58/2.44  tff(c_7810, plain, (![A_101, B_102]: (k1_setfam_1(k2_tarski(A_101, B_102))=k3_xboole_0(B_102, A_101))), inference(negUnitSimplification, [status(thm)], [c_463, c_7809])).
% 6.58/2.44  tff(c_4831, plain, (![B_2709, A_2710]: (k2_xboole_0(k1_tarski(B_2709), k1_tarski(A_2710))=k2_tarski(A_2710, B_2709))), inference(superposition, [status(thm), theory('equality')], [c_2, c_523])).
% 6.58/2.44  tff(c_58, plain, (![A_45, B_46]: (k2_xboole_0(k1_tarski(A_45), k1_tarski(B_46))=k2_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.58/2.44  tff(c_4868, plain, (![B_2709, A_2710]: (k2_tarski(B_2709, A_2710)=k2_tarski(A_2710, B_2709))), inference(superposition, [status(thm), theory('equality')], [c_4831, c_58])).
% 6.58/2.44  tff(c_72, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.58/2.44  tff(c_73, plain, (k1_setfam_1(k2_tarski('#skF_3', '#skF_4'))!=k3_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_72])).
% 6.58/2.44  tff(c_4929, plain, (k1_setfam_1(k2_tarski('#skF_4', '#skF_3'))!=k3_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4868, c_73])).
% 6.58/2.44  tff(c_7817, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k3_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7810, c_4929])).
% 6.58/2.44  tff(c_7820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_7817])).
% 6.58/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.58/2.44  
% 6.58/2.44  Inference rules
% 6.58/2.44  ----------------------
% 6.58/2.44  #Ref     : 1
% 6.58/2.44  #Sup     : 1641
% 6.58/2.44  #Fact    : 6
% 6.58/2.44  #Define  : 0
% 6.58/2.44  #Split   : 1
% 6.58/2.44  #Chain   : 0
% 6.58/2.44  #Close   : 0
% 6.58/2.44  
% 6.58/2.44  Ordering : KBO
% 6.58/2.44  
% 6.58/2.44  Simplification rules
% 6.58/2.44  ----------------------
% 6.58/2.44  #Subsume      : 49
% 6.58/2.44  #Demod        : 1237
% 6.58/2.44  #Tautology    : 977
% 6.58/2.44  #SimpNegUnit  : 15
% 6.58/2.44  #BackRed      : 6
% 6.58/2.44  
% 6.58/2.44  #Partial instantiations: 2420
% 6.58/2.44  #Strategies tried      : 1
% 6.58/2.44  
% 6.58/2.44  Timing (in seconds)
% 6.58/2.44  ----------------------
% 6.58/2.44  Preprocessing        : 0.34
% 6.58/2.44  Parsing              : 0.18
% 6.58/2.44  CNF conversion       : 0.02
% 6.58/2.44  Main loop            : 1.32
% 6.58/2.44  Inferencing          : 0.48
% 6.58/2.44  Reduction            : 0.52
% 6.58/2.44  Demodulation         : 0.43
% 6.66/2.44  BG Simplification    : 0.05
% 6.66/2.44  Subsumption          : 0.20
% 6.66/2.44  Abstraction          : 0.06
% 6.66/2.44  MUC search           : 0.00
% 6.66/2.44  Cooper               : 0.00
% 6.66/2.44  Total                : 1.69
% 6.66/2.44  Index Insertion      : 0.00
% 6.66/2.44  Index Deletion       : 0.00
% 6.66/2.44  Index Matching       : 0.00
% 6.66/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
