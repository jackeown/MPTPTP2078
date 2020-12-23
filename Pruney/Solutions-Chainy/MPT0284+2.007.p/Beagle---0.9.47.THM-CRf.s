%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:27 EST 2020

% Result     : Theorem 12.06s
% Output     : CNFRefutation 12.06s
% Verified   : 
% Statistics : Number of formulae       :   52 (  74 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 ( 102 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_235,plain,(
    ! [A_62,B_63] : k2_xboole_0(k4_xboole_0(A_62,B_63),k4_xboole_0(B_63,A_62)) = k5_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_260,plain,(
    ! [B_63,A_62] : k2_xboole_0(k4_xboole_0(B_63,A_62),k4_xboole_0(A_62,B_63)) = k5_xboole_0(A_62,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_2])).

tff(c_131,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),A_48)
      | r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [C_26,A_22] :
      ( r1_tarski(C_26,A_22)
      | ~ r2_hidden(C_26,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_136,plain,(
    ! [A_22,B_49] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_22),B_49),A_22)
      | r1_tarski(k1_zfmisc_1(A_22),B_49) ) ),
    inference(resolution,[status(thm)],[c_131,c_22])).

tff(c_120,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,k2_xboole_0(C_46,B_47))
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_129,plain,(
    ! [A_45,A_1,B_2] :
      ( r1_tarski(A_45,k2_xboole_0(A_1,B_2))
      | ~ r1_tarski(A_45,A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_120])).

tff(c_24,plain,(
    ! [C_26,A_22] :
      ( r2_hidden(C_26,k1_zfmisc_1(A_22))
      | ~ r1_tarski(C_26,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_137,plain,(
    ! [A_50,B_51] :
      ( ~ r2_hidden('#skF_1'(A_50,B_51),B_51)
      | r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16651,plain,(
    ! [A_412,A_413] :
      ( r1_tarski(A_412,k1_zfmisc_1(A_413))
      | ~ r1_tarski('#skF_1'(A_412,k1_zfmisc_1(A_413)),A_413) ) ),
    inference(resolution,[status(thm)],[c_24,c_137])).

tff(c_29324,plain,(
    ! [A_631,A_632,B_633] :
      ( r1_tarski(A_631,k1_zfmisc_1(k2_xboole_0(A_632,B_633)))
      | ~ r1_tarski('#skF_1'(A_631,k1_zfmisc_1(k2_xboole_0(A_632,B_633))),A_632) ) ),
    inference(resolution,[status(thm)],[c_129,c_16651])).

tff(c_29498,plain,(
    ! [A_634,B_635] : r1_tarski(k1_zfmisc_1(A_634),k1_zfmisc_1(k2_xboole_0(A_634,B_635))) ),
    inference(resolution,[status(thm)],[c_136,c_29324])).

tff(c_29603,plain,(
    ! [B_63,A_62] : r1_tarski(k1_zfmisc_1(k4_xboole_0(B_63,A_62)),k1_zfmisc_1(k5_xboole_0(A_62,B_63))) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_29498])).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(k4_xboole_0(A_8,B_9),k4_xboole_0(B_9,A_8)) = k5_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_tarski(A_12,k2_xboole_0(C_14,B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1435,plain,(
    ! [A_110,A_111] :
      ( r1_tarski(A_110,k1_zfmisc_1(A_111))
      | ~ r1_tarski('#skF_1'(A_110,k1_zfmisc_1(A_111)),A_111) ) ),
    inference(resolution,[status(thm)],[c_24,c_137])).

tff(c_14410,plain,(
    ! [A_343,C_344,B_345] :
      ( r1_tarski(A_343,k1_zfmisc_1(k2_xboole_0(C_344,B_345)))
      | ~ r1_tarski('#skF_1'(A_343,k1_zfmisc_1(k2_xboole_0(C_344,B_345))),B_345) ) ),
    inference(resolution,[status(thm)],[c_14,c_1435])).

tff(c_14571,plain,(
    ! [A_346,C_347] : r1_tarski(k1_zfmisc_1(A_346),k1_zfmisc_1(k2_xboole_0(C_347,A_346))) ),
    inference(resolution,[status(thm)],[c_136,c_14410])).

tff(c_14976,plain,(
    ! [A_352,B_353] : r1_tarski(k1_zfmisc_1(A_352),k1_zfmisc_1(k2_xboole_0(A_352,B_353))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_14571])).

tff(c_15088,plain,(
    ! [A_8,B_9] : r1_tarski(k1_zfmisc_1(k4_xboole_0(A_8,B_9)),k1_zfmisc_1(k5_xboole_0(A_8,B_9))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_14976])).

tff(c_377,plain,(
    ! [A_71,C_72,B_73] :
      ( r1_tarski(k2_xboole_0(A_71,C_72),B_73)
      | ~ r1_tarski(C_72,B_73)
      | ~ r1_tarski(A_71,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_4','#skF_5')),k1_zfmisc_1(k4_xboole_0('#skF_5','#skF_4'))),k1_zfmisc_1(k5_xboole_0('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_402,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_5','#skF_4')),k1_zfmisc_1(k5_xboole_0('#skF_4','#skF_5')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_4','#skF_5')),k1_zfmisc_1(k5_xboole_0('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_377,c_36])).

tff(c_565,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_4','#skF_5')),k1_zfmisc_1(k5_xboole_0('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_402])).

tff(c_15856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15088,c_565])).

tff(c_15857,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_5','#skF_4')),k1_zfmisc_1(k5_xboole_0('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_402])).

tff(c_31269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_29603,c_15857])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:02:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.06/4.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.06/4.82  
% 12.06/4.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.06/4.82  %$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 12.06/4.82  
% 12.06/4.82  %Foreground sorts:
% 12.06/4.82  
% 12.06/4.82  
% 12.06/4.82  %Background operators:
% 12.06/4.82  
% 12.06/4.82  
% 12.06/4.82  %Foreground operators:
% 12.06/4.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.06/4.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.06/4.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.06/4.82  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.06/4.82  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.06/4.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.06/4.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.06/4.82  tff('#skF_5', type, '#skF_5': $i).
% 12.06/4.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.06/4.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.06/4.82  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.06/4.82  tff('#skF_4', type, '#skF_4': $i).
% 12.06/4.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.06/4.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.06/4.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.06/4.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.06/4.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.06/4.82  
% 12.06/4.83  tff(f_36, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 12.06/4.83  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 12.06/4.83  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 12.06/4.83  tff(f_61, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 12.06/4.83  tff(f_42, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 12.06/4.83  tff(f_54, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 12.06/4.83  tff(f_66, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 12.06/4.83  tff(c_235, plain, (![A_62, B_63]: (k2_xboole_0(k4_xboole_0(A_62, B_63), k4_xboole_0(B_63, A_62))=k5_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.06/4.83  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.06/4.83  tff(c_260, plain, (![B_63, A_62]: (k2_xboole_0(k4_xboole_0(B_63, A_62), k4_xboole_0(A_62, B_63))=k5_xboole_0(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_235, c_2])).
% 12.06/4.83  tff(c_131, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), A_48) | r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.06/4.83  tff(c_22, plain, (![C_26, A_22]: (r1_tarski(C_26, A_22) | ~r2_hidden(C_26, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.06/4.83  tff(c_136, plain, (![A_22, B_49]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_22), B_49), A_22) | r1_tarski(k1_zfmisc_1(A_22), B_49))), inference(resolution, [status(thm)], [c_131, c_22])).
% 12.06/4.83  tff(c_120, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, k2_xboole_0(C_46, B_47)) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.06/4.83  tff(c_129, plain, (![A_45, A_1, B_2]: (r1_tarski(A_45, k2_xboole_0(A_1, B_2)) | ~r1_tarski(A_45, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_120])).
% 12.06/4.83  tff(c_24, plain, (![C_26, A_22]: (r2_hidden(C_26, k1_zfmisc_1(A_22)) | ~r1_tarski(C_26, A_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.06/4.83  tff(c_137, plain, (![A_50, B_51]: (~r2_hidden('#skF_1'(A_50, B_51), B_51) | r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_34])).
% 12.06/4.83  tff(c_16651, plain, (![A_412, A_413]: (r1_tarski(A_412, k1_zfmisc_1(A_413)) | ~r1_tarski('#skF_1'(A_412, k1_zfmisc_1(A_413)), A_413))), inference(resolution, [status(thm)], [c_24, c_137])).
% 12.06/4.83  tff(c_29324, plain, (![A_631, A_632, B_633]: (r1_tarski(A_631, k1_zfmisc_1(k2_xboole_0(A_632, B_633))) | ~r1_tarski('#skF_1'(A_631, k1_zfmisc_1(k2_xboole_0(A_632, B_633))), A_632))), inference(resolution, [status(thm)], [c_129, c_16651])).
% 12.06/4.83  tff(c_29498, plain, (![A_634, B_635]: (r1_tarski(k1_zfmisc_1(A_634), k1_zfmisc_1(k2_xboole_0(A_634, B_635))))), inference(resolution, [status(thm)], [c_136, c_29324])).
% 12.06/4.83  tff(c_29603, plain, (![B_63, A_62]: (r1_tarski(k1_zfmisc_1(k4_xboole_0(B_63, A_62)), k1_zfmisc_1(k5_xboole_0(A_62, B_63))))), inference(superposition, [status(thm), theory('equality')], [c_260, c_29498])).
% 12.06/4.83  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(k4_xboole_0(A_8, B_9), k4_xboole_0(B_9, A_8))=k5_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 12.06/4.83  tff(c_14, plain, (![A_12, C_14, B_13]: (r1_tarski(A_12, k2_xboole_0(C_14, B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.06/4.83  tff(c_1435, plain, (![A_110, A_111]: (r1_tarski(A_110, k1_zfmisc_1(A_111)) | ~r1_tarski('#skF_1'(A_110, k1_zfmisc_1(A_111)), A_111))), inference(resolution, [status(thm)], [c_24, c_137])).
% 12.06/4.83  tff(c_14410, plain, (![A_343, C_344, B_345]: (r1_tarski(A_343, k1_zfmisc_1(k2_xboole_0(C_344, B_345))) | ~r1_tarski('#skF_1'(A_343, k1_zfmisc_1(k2_xboole_0(C_344, B_345))), B_345))), inference(resolution, [status(thm)], [c_14, c_1435])).
% 12.06/4.83  tff(c_14571, plain, (![A_346, C_347]: (r1_tarski(k1_zfmisc_1(A_346), k1_zfmisc_1(k2_xboole_0(C_347, A_346))))), inference(resolution, [status(thm)], [c_136, c_14410])).
% 12.06/4.83  tff(c_14976, plain, (![A_352, B_353]: (r1_tarski(k1_zfmisc_1(A_352), k1_zfmisc_1(k2_xboole_0(A_352, B_353))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_14571])).
% 12.06/4.83  tff(c_15088, plain, (![A_8, B_9]: (r1_tarski(k1_zfmisc_1(k4_xboole_0(A_8, B_9)), k1_zfmisc_1(k5_xboole_0(A_8, B_9))))), inference(superposition, [status(thm), theory('equality')], [c_10, c_14976])).
% 12.06/4.83  tff(c_377, plain, (![A_71, C_72, B_73]: (r1_tarski(k2_xboole_0(A_71, C_72), B_73) | ~r1_tarski(C_72, B_73) | ~r1_tarski(A_71, B_73))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.06/4.83  tff(c_36, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_4', '#skF_5')), k1_zfmisc_1(k4_xboole_0('#skF_5', '#skF_4'))), k1_zfmisc_1(k5_xboole_0('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 12.06/4.83  tff(c_402, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_5', '#skF_4')), k1_zfmisc_1(k5_xboole_0('#skF_4', '#skF_5'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_4', '#skF_5')), k1_zfmisc_1(k5_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_377, c_36])).
% 12.06/4.83  tff(c_565, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_4', '#skF_5')), k1_zfmisc_1(k5_xboole_0('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_402])).
% 12.06/4.83  tff(c_15856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15088, c_565])).
% 12.06/4.83  tff(c_15857, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_5', '#skF_4')), k1_zfmisc_1(k5_xboole_0('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_402])).
% 12.06/4.83  tff(c_31269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_29603, c_15857])).
% 12.06/4.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.06/4.83  
% 12.06/4.83  Inference rules
% 12.06/4.83  ----------------------
% 12.06/4.83  #Ref     : 0
% 12.06/4.83  #Sup     : 7989
% 12.06/4.83  #Fact    : 0
% 12.06/4.83  #Define  : 0
% 12.06/4.83  #Split   : 1
% 12.06/4.83  #Chain   : 0
% 12.06/4.83  #Close   : 0
% 12.06/4.83  
% 12.06/4.83  Ordering : KBO
% 12.06/4.83  
% 12.06/4.83  Simplification rules
% 12.06/4.83  ----------------------
% 12.06/4.83  #Subsume      : 1074
% 12.06/4.83  #Demod        : 6669
% 12.32/4.83  #Tautology    : 3811
% 12.32/4.83  #SimpNegUnit  : 0
% 12.32/4.83  #BackRed      : 6
% 12.32/4.84  
% 12.32/4.84  #Partial instantiations: 0
% 12.32/4.84  #Strategies tried      : 1
% 12.32/4.84  
% 12.32/4.84  Timing (in seconds)
% 12.32/4.84  ----------------------
% 12.32/4.84  Preprocessing        : 0.27
% 12.32/4.84  Parsing              : 0.15
% 12.32/4.84  CNF conversion       : 0.02
% 12.32/4.84  Main loop            : 3.80
% 12.32/4.84  Inferencing          : 0.73
% 12.32/4.84  Reduction            : 1.94
% 12.32/4.84  Demodulation         : 1.71
% 12.32/4.84  BG Simplification    : 0.10
% 12.32/4.84  Subsumption          : 0.81
% 12.32/4.84  Abstraction          : 0.15
% 12.32/4.84  MUC search           : 0.00
% 12.32/4.84  Cooper               : 0.00
% 12.32/4.84  Total                : 4.10
% 12.32/4.84  Index Insertion      : 0.00
% 12.32/4.84  Index Deletion       : 0.00
% 12.32/4.84  Index Matching       : 0.00
% 12.32/4.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
