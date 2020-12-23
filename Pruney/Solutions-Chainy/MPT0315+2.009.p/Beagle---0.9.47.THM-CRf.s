%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:57 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 131 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 163 expanded)
%              Number of equality atoms :   44 (  99 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_55,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,B)
          | r1_xboole_0(C,D) )
       => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_18,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_325,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_343,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_325])).

tff(c_346,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_343])).

tff(c_20,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_84,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_102,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_84])).

tff(c_105,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_102])).

tff(c_26,plain,
    ( r1_xboole_0('#skF_4','#skF_5')
    | r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_65,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_71,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = A_24
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_65,c_71])).

tff(c_99,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_84])).

tff(c_146,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_99])).

tff(c_22,plain,(
    ! [A_14,C_16,B_15,D_17] : k3_xboole_0(k2_zfmisc_1(A_14,C_16),k2_zfmisc_1(B_15,D_17)) = k2_zfmisc_1(k3_xboole_0(A_14,B_15),k3_xboole_0(C_16,D_17)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),k3_xboole_0(A_1,B_2))
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_106,plain,(
    ! [A_28] : k4_xboole_0(A_28,A_28) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_102])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,(
    ! [A_28] : k4_xboole_0(A_28,k1_xboole_0) = k3_xboole_0(A_28,A_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_10])).

tff(c_123,plain,(
    ! [A_28] : k3_xboole_0(A_28,A_28) = A_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_111])).

tff(c_162,plain,(
    ! [A_32,B_33,C_34] :
      ( ~ r1_xboole_0(A_32,B_33)
      | ~ r2_hidden(C_34,k3_xboole_0(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_198,plain,(
    ! [A_39,C_40] :
      ( ~ r1_xboole_0(A_39,A_39)
      | ~ r2_hidden(C_40,A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_162])).

tff(c_204,plain,(
    ! [C_40,B_11] :
      ( ~ r2_hidden(C_40,B_11)
      | k4_xboole_0(B_11,B_11) != B_11 ) ),
    inference(resolution,[status(thm)],[c_14,c_198])).

tff(c_209,plain,(
    ! [C_41,B_42] :
      ( ~ r2_hidden(C_41,B_42)
      | k1_xboole_0 != B_42 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_204])).

tff(c_214,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) != k1_xboole_0
      | r1_xboole_0(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_2,c_209])).

tff(c_24,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_2','#skF_4'),k2_zfmisc_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_227,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_2','#skF_4'),k2_zfmisc_1('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_214,c_24])).

tff(c_294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_146,c_22,c_227])).

tff(c_295,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_297,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = A_51
      | ~ r1_xboole_0(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_301,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_295,c_297])).

tff(c_340,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_325])).

tff(c_390,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_340])).

tff(c_419,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_1'(A_69,B_70),k3_xboole_0(A_69,B_70))
      | r1_xboole_0(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_347,plain,(
    ! [A_61] : k4_xboole_0(A_61,A_61) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_343])).

tff(c_352,plain,(
    ! [A_61] : k4_xboole_0(A_61,k1_xboole_0) = k3_xboole_0(A_61,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_10])).

tff(c_368,plain,(
    ! [A_62] : k3_xboole_0(A_62,A_62) = A_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_352])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_400,plain,(
    ! [A_63,C_64] :
      ( ~ r1_xboole_0(A_63,A_63)
      | ~ r2_hidden(C_64,A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_4])).

tff(c_403,plain,(
    ! [C_64,B_11] :
      ( ~ r2_hidden(C_64,B_11)
      | k4_xboole_0(B_11,B_11) != B_11 ) ),
    inference(resolution,[status(thm)],[c_14,c_400])).

tff(c_405,plain,(
    ! [C_64,B_11] :
      ( ~ r2_hidden(C_64,B_11)
      | k1_xboole_0 != B_11 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_403])).

tff(c_450,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(A_72,B_73) != k1_xboole_0
      | r1_xboole_0(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_419,c_405])).

tff(c_467,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_2','#skF_4'),k2_zfmisc_1('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_450,c_24])).

tff(c_587,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_2','#skF_3'),k3_xboole_0('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_467])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_390,c_587])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:21:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.39  
% 2.18/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.39  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.18/1.39  
% 2.18/1.39  %Foreground sorts:
% 2.18/1.39  
% 2.18/1.39  
% 2.18/1.39  %Background operators:
% 2.18/1.39  
% 2.18/1.39  
% 2.18/1.39  %Foreground operators:
% 2.18/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.18/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.18/1.39  
% 2.18/1.41  tff(f_55, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.18/1.41  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.18/1.41  tff(f_43, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.18/1.41  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.18/1.41  tff(f_64, negated_conjecture, ~(![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.18/1.41  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.18/1.41  tff(f_57, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 2.18/1.41  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.18/1.41  tff(c_18, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.18/1.41  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.18/1.41  tff(c_8, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.18/1.41  tff(c_325, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.18/1.41  tff(c_343, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_325])).
% 2.18/1.41  tff(c_346, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_343])).
% 2.18/1.41  tff(c_20, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.18/1.41  tff(c_84, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.18/1.41  tff(c_102, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_84])).
% 2.18/1.41  tff(c_105, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_102])).
% 2.18/1.41  tff(c_26, plain, (r1_xboole_0('#skF_4', '#skF_5') | r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.18/1.41  tff(c_65, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_26])).
% 2.18/1.41  tff(c_71, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=A_24 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.18/1.41  tff(c_79, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_65, c_71])).
% 2.18/1.41  tff(c_99, plain, (k4_xboole_0('#skF_2', '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_79, c_84])).
% 2.18/1.41  tff(c_146, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_105, c_99])).
% 2.18/1.41  tff(c_22, plain, (![A_14, C_16, B_15, D_17]: (k3_xboole_0(k2_zfmisc_1(A_14, C_16), k2_zfmisc_1(B_15, D_17))=k2_zfmisc_1(k3_xboole_0(A_14, B_15), k3_xboole_0(C_16, D_17)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.18/1.41  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), k3_xboole_0(A_1, B_2)) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.41  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.18/1.41  tff(c_106, plain, (![A_28]: (k4_xboole_0(A_28, A_28)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_102])).
% 2.18/1.41  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.18/1.41  tff(c_111, plain, (![A_28]: (k4_xboole_0(A_28, k1_xboole_0)=k3_xboole_0(A_28, A_28))), inference(superposition, [status(thm), theory('equality')], [c_106, c_10])).
% 2.18/1.41  tff(c_123, plain, (![A_28]: (k3_xboole_0(A_28, A_28)=A_28)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_111])).
% 2.18/1.41  tff(c_162, plain, (![A_32, B_33, C_34]: (~r1_xboole_0(A_32, B_33) | ~r2_hidden(C_34, k3_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.41  tff(c_198, plain, (![A_39, C_40]: (~r1_xboole_0(A_39, A_39) | ~r2_hidden(C_40, A_39))), inference(superposition, [status(thm), theory('equality')], [c_123, c_162])).
% 2.18/1.41  tff(c_204, plain, (![C_40, B_11]: (~r2_hidden(C_40, B_11) | k4_xboole_0(B_11, B_11)!=B_11)), inference(resolution, [status(thm)], [c_14, c_198])).
% 2.18/1.41  tff(c_209, plain, (![C_41, B_42]: (~r2_hidden(C_41, B_42) | k1_xboole_0!=B_42)), inference(demodulation, [status(thm), theory('equality')], [c_105, c_204])).
% 2.18/1.41  tff(c_214, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)!=k1_xboole_0 | r1_xboole_0(A_43, B_44))), inference(resolution, [status(thm)], [c_2, c_209])).
% 2.18/1.41  tff(c_24, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.18/1.41  tff(c_227, plain, (k3_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_214, c_24])).
% 2.18/1.41  tff(c_294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_146, c_22, c_227])).
% 2.18/1.41  tff(c_295, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 2.18/1.41  tff(c_297, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=A_51 | ~r1_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.18/1.41  tff(c_301, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_295, c_297])).
% 2.18/1.41  tff(c_340, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_301, c_325])).
% 2.18/1.41  tff(c_390, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_346, c_340])).
% 2.18/1.41  tff(c_419, plain, (![A_69, B_70]: (r2_hidden('#skF_1'(A_69, B_70), k3_xboole_0(A_69, B_70)) | r1_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.41  tff(c_347, plain, (![A_61]: (k4_xboole_0(A_61, A_61)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_343])).
% 2.18/1.41  tff(c_352, plain, (![A_61]: (k4_xboole_0(A_61, k1_xboole_0)=k3_xboole_0(A_61, A_61))), inference(superposition, [status(thm), theory('equality')], [c_347, c_10])).
% 2.18/1.41  tff(c_368, plain, (![A_62]: (k3_xboole_0(A_62, A_62)=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_352])).
% 2.18/1.41  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.18/1.41  tff(c_400, plain, (![A_63, C_64]: (~r1_xboole_0(A_63, A_63) | ~r2_hidden(C_64, A_63))), inference(superposition, [status(thm), theory('equality')], [c_368, c_4])).
% 2.18/1.41  tff(c_403, plain, (![C_64, B_11]: (~r2_hidden(C_64, B_11) | k4_xboole_0(B_11, B_11)!=B_11)), inference(resolution, [status(thm)], [c_14, c_400])).
% 2.18/1.41  tff(c_405, plain, (![C_64, B_11]: (~r2_hidden(C_64, B_11) | k1_xboole_0!=B_11)), inference(demodulation, [status(thm), theory('equality')], [c_346, c_403])).
% 2.18/1.41  tff(c_450, plain, (![A_72, B_73]: (k3_xboole_0(A_72, B_73)!=k1_xboole_0 | r1_xboole_0(A_72, B_73))), inference(resolution, [status(thm)], [c_419, c_405])).
% 2.18/1.41  tff(c_467, plain, (k3_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_450, c_24])).
% 2.18/1.41  tff(c_587, plain, (k2_zfmisc_1(k3_xboole_0('#skF_2', '#skF_3'), k3_xboole_0('#skF_4', '#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_467])).
% 2.18/1.41  tff(c_590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_390, c_587])).
% 2.18/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.41  
% 2.18/1.41  Inference rules
% 2.18/1.41  ----------------------
% 2.18/1.41  #Ref     : 0
% 2.18/1.41  #Sup     : 129
% 2.18/1.41  #Fact    : 0
% 2.18/1.41  #Define  : 0
% 2.18/1.41  #Split   : 2
% 2.18/1.41  #Chain   : 0
% 2.18/1.41  #Close   : 0
% 2.18/1.41  
% 2.18/1.41  Ordering : KBO
% 2.18/1.41  
% 2.18/1.41  Simplification rules
% 2.18/1.41  ----------------------
% 2.18/1.41  #Subsume      : 10
% 2.18/1.41  #Demod        : 52
% 2.18/1.41  #Tautology    : 74
% 2.18/1.41  #SimpNegUnit  : 4
% 2.18/1.41  #BackRed      : 1
% 2.18/1.41  
% 2.18/1.41  #Partial instantiations: 0
% 2.18/1.41  #Strategies tried      : 1
% 2.18/1.41  
% 2.18/1.41  Timing (in seconds)
% 2.18/1.41  ----------------------
% 2.18/1.41  Preprocessing        : 0.26
% 2.18/1.41  Parsing              : 0.14
% 2.18/1.41  CNF conversion       : 0.02
% 2.18/1.41  Main loop            : 0.25
% 2.18/1.41  Inferencing          : 0.10
% 2.18/1.41  Reduction            : 0.08
% 2.18/1.41  Demodulation         : 0.06
% 2.18/1.41  BG Simplification    : 0.01
% 2.18/1.41  Subsumption          : 0.03
% 2.18/1.41  Abstraction          : 0.01
% 2.18/1.41  MUC search           : 0.00
% 2.18/1.41  Cooper               : 0.00
% 2.18/1.41  Total                : 0.54
% 2.18/1.41  Index Insertion      : 0.00
% 2.18/1.41  Index Deletion       : 0.00
% 2.18/1.41  Index Matching       : 0.00
% 2.18/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
