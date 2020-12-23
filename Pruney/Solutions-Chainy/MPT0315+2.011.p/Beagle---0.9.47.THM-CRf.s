%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:57 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 155 expanded)
%              Number of leaves         :   22 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :   80 ( 203 expanded)
%              Number of equality atoms :   44 ( 107 expanded)
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

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,B)
          | r1_xboole_0(C,D) )
       => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

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

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_308,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = A_53
      | ~ r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_320,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(resolution,[status(thm)],[c_10,c_308])).

tff(c_345,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_360,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_345])).

tff(c_366,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_360])).

tff(c_20,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_59,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = A_24
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_71,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(resolution,[status(thm)],[c_10,c_59])).

tff(c_107,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_125,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_107])).

tff(c_128,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_125])).

tff(c_26,plain,
    ( r1_xboole_0('#skF_4','#skF_5')
    | r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_57,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_70,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_57,c_59])).

tff(c_122,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_107])).

tff(c_185,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_122])).

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

tff(c_139,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_125])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_144,plain,(
    ! [A_37] : k4_xboole_0(A_37,k1_xboole_0) = k3_xboole_0(A_37,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_8])).

tff(c_160,plain,(
    ! [A_38] : k3_xboole_0(A_38,A_38) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_144])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_200,plain,(
    ! [A_39,C_40] :
      ( ~ r1_xboole_0(A_39,A_39)
      | ~ r2_hidden(C_40,A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_4])).

tff(c_203,plain,(
    ! [C_40,B_11] :
      ( ~ r2_hidden(C_40,B_11)
      | k4_xboole_0(B_11,B_11) != B_11 ) ),
    inference(resolution,[status(thm)],[c_14,c_200])).

tff(c_211,plain,(
    ! [C_41,B_42] :
      ( ~ r2_hidden(C_41,B_42)
      | k1_xboole_0 != B_42 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_203])).

tff(c_216,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) != k1_xboole_0
      | r1_xboole_0(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_2,c_211])).

tff(c_24,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_2','#skF_4'),k2_zfmisc_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_228,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_2','#skF_4'),k2_zfmisc_1('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_216,c_24])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_185,c_22,c_228])).

tff(c_297,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_319,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_297,c_308])).

tff(c_363,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_345])).

tff(c_407,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_363])).

tff(c_367,plain,(
    ! [A_60] : k4_xboole_0(A_60,A_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_360])).

tff(c_372,plain,(
    ! [A_60] : k4_xboole_0(A_60,k1_xboole_0) = k3_xboole_0(A_60,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_8])).

tff(c_384,plain,(
    ! [A_60] : k3_xboole_0(A_60,A_60) = A_60 ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_372])).

tff(c_412,plain,(
    ! [A_62,B_63,C_64] :
      ( ~ r1_xboole_0(A_62,B_63)
      | ~ r2_hidden(C_64,k3_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_427,plain,(
    ! [A_66,C_67] :
      ( ~ r1_xboole_0(A_66,A_66)
      | ~ r2_hidden(C_67,A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_412])).

tff(c_430,plain,(
    ! [C_67,B_11] :
      ( ~ r2_hidden(C_67,B_11)
      | k4_xboole_0(B_11,B_11) != B_11 ) ),
    inference(resolution,[status(thm)],[c_14,c_427])).

tff(c_456,plain,(
    ! [C_70,B_71] :
      ( ~ r2_hidden(C_70,B_71)
      | k1_xboole_0 != B_71 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_430])).

tff(c_461,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(A_72,B_73) != k1_xboole_0
      | r1_xboole_0(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_2,c_456])).

tff(c_477,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_2','#skF_4'),k2_zfmisc_1('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_461,c_24])).

tff(c_599,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_2','#skF_3'),k3_xboole_0('#skF_4','#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_477])).

tff(c_602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_407,c_599])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.31  
% 2.21/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.31  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.37/1.31  
% 2.37/1.31  %Foreground sorts:
% 2.37/1.31  
% 2.37/1.31  
% 2.37/1.31  %Background operators:
% 2.37/1.31  
% 2.37/1.31  
% 2.37/1.31  %Foreground operators:
% 2.37/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.37/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.37/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.37/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.37/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.37/1.31  
% 2.37/1.32  tff(f_55, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.37/1.32  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.37/1.32  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.37/1.32  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.37/1.32  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.37/1.32  tff(f_64, negated_conjecture, ~(![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.37/1.32  tff(f_57, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 2.37/1.32  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.37/1.32  tff(c_18, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.32  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.37/1.32  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.37/1.32  tff(c_308, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=A_53 | ~r1_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.37/1.32  tff(c_320, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(resolution, [status(thm)], [c_10, c_308])).
% 2.37/1.32  tff(c_345, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.37/1.32  tff(c_360, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_320, c_345])).
% 2.37/1.32  tff(c_366, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_360])).
% 2.37/1.32  tff(c_20, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.37/1.32  tff(c_59, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=A_24 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.37/1.32  tff(c_71, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(resolution, [status(thm)], [c_10, c_59])).
% 2.37/1.32  tff(c_107, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.37/1.32  tff(c_125, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_71, c_107])).
% 2.37/1.32  tff(c_128, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_125])).
% 2.37/1.32  tff(c_26, plain, (r1_xboole_0('#skF_4', '#skF_5') | r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.37/1.32  tff(c_57, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_26])).
% 2.37/1.32  tff(c_70, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_57, c_59])).
% 2.37/1.32  tff(c_122, plain, (k4_xboole_0('#skF_2', '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_70, c_107])).
% 2.37/1.32  tff(c_185, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_128, c_122])).
% 2.37/1.32  tff(c_22, plain, (![A_14, C_16, B_15, D_17]: (k3_xboole_0(k2_zfmisc_1(A_14, C_16), k2_zfmisc_1(B_15, D_17))=k2_zfmisc_1(k3_xboole_0(A_14, B_15), k3_xboole_0(C_16, D_17)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.37/1.32  tff(c_2, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), k3_xboole_0(A_1, B_2)) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.37/1.32  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.37/1.32  tff(c_139, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_125])).
% 2.37/1.32  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.37/1.32  tff(c_144, plain, (![A_37]: (k4_xboole_0(A_37, k1_xboole_0)=k3_xboole_0(A_37, A_37))), inference(superposition, [status(thm), theory('equality')], [c_139, c_8])).
% 2.37/1.32  tff(c_160, plain, (![A_38]: (k3_xboole_0(A_38, A_38)=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_144])).
% 2.37/1.32  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.37/1.32  tff(c_200, plain, (![A_39, C_40]: (~r1_xboole_0(A_39, A_39) | ~r2_hidden(C_40, A_39))), inference(superposition, [status(thm), theory('equality')], [c_160, c_4])).
% 2.37/1.32  tff(c_203, plain, (![C_40, B_11]: (~r2_hidden(C_40, B_11) | k4_xboole_0(B_11, B_11)!=B_11)), inference(resolution, [status(thm)], [c_14, c_200])).
% 2.37/1.32  tff(c_211, plain, (![C_41, B_42]: (~r2_hidden(C_41, B_42) | k1_xboole_0!=B_42)), inference(demodulation, [status(thm), theory('equality')], [c_128, c_203])).
% 2.37/1.32  tff(c_216, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)!=k1_xboole_0 | r1_xboole_0(A_43, B_44))), inference(resolution, [status(thm)], [c_2, c_211])).
% 2.37/1.32  tff(c_24, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.37/1.32  tff(c_228, plain, (k3_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_216, c_24])).
% 2.37/1.32  tff(c_296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_185, c_22, c_228])).
% 2.37/1.32  tff(c_297, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 2.37/1.32  tff(c_319, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_297, c_308])).
% 2.37/1.32  tff(c_363, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_319, c_345])).
% 2.37/1.32  tff(c_407, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_366, c_363])).
% 2.37/1.32  tff(c_367, plain, (![A_60]: (k4_xboole_0(A_60, A_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_360])).
% 2.37/1.32  tff(c_372, plain, (![A_60]: (k4_xboole_0(A_60, k1_xboole_0)=k3_xboole_0(A_60, A_60))), inference(superposition, [status(thm), theory('equality')], [c_367, c_8])).
% 2.37/1.32  tff(c_384, plain, (![A_60]: (k3_xboole_0(A_60, A_60)=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_320, c_372])).
% 2.37/1.32  tff(c_412, plain, (![A_62, B_63, C_64]: (~r1_xboole_0(A_62, B_63) | ~r2_hidden(C_64, k3_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.37/1.32  tff(c_427, plain, (![A_66, C_67]: (~r1_xboole_0(A_66, A_66) | ~r2_hidden(C_67, A_66))), inference(superposition, [status(thm), theory('equality')], [c_384, c_412])).
% 2.37/1.32  tff(c_430, plain, (![C_67, B_11]: (~r2_hidden(C_67, B_11) | k4_xboole_0(B_11, B_11)!=B_11)), inference(resolution, [status(thm)], [c_14, c_427])).
% 2.37/1.32  tff(c_456, plain, (![C_70, B_71]: (~r2_hidden(C_70, B_71) | k1_xboole_0!=B_71)), inference(demodulation, [status(thm), theory('equality')], [c_366, c_430])).
% 2.37/1.32  tff(c_461, plain, (![A_72, B_73]: (k3_xboole_0(A_72, B_73)!=k1_xboole_0 | r1_xboole_0(A_72, B_73))), inference(resolution, [status(thm)], [c_2, c_456])).
% 2.37/1.32  tff(c_477, plain, (k3_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_461, c_24])).
% 2.37/1.32  tff(c_599, plain, (k2_zfmisc_1(k3_xboole_0('#skF_2', '#skF_3'), k3_xboole_0('#skF_4', '#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_477])).
% 2.37/1.32  tff(c_602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_407, c_599])).
% 2.37/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.32  
% 2.37/1.32  Inference rules
% 2.37/1.32  ----------------------
% 2.37/1.32  #Ref     : 0
% 2.37/1.32  #Sup     : 131
% 2.37/1.32  #Fact    : 0
% 2.37/1.32  #Define  : 0
% 2.37/1.32  #Split   : 1
% 2.37/1.32  #Chain   : 0
% 2.37/1.32  #Close   : 0
% 2.37/1.32  
% 2.37/1.32  Ordering : KBO
% 2.37/1.32  
% 2.37/1.32  Simplification rules
% 2.37/1.32  ----------------------
% 2.37/1.32  #Subsume      : 10
% 2.37/1.32  #Demod        : 55
% 2.37/1.32  #Tautology    : 77
% 2.37/1.32  #SimpNegUnit  : 4
% 2.37/1.32  #BackRed      : 1
% 2.37/1.32  
% 2.37/1.32  #Partial instantiations: 0
% 2.37/1.32  #Strategies tried      : 1
% 2.37/1.32  
% 2.37/1.32  Timing (in seconds)
% 2.37/1.32  ----------------------
% 2.37/1.33  Preprocessing        : 0.28
% 2.37/1.33  Parsing              : 0.15
% 2.37/1.33  CNF conversion       : 0.02
% 2.37/1.33  Main loop            : 0.24
% 2.37/1.33  Inferencing          : 0.10
% 2.37/1.33  Reduction            : 0.08
% 2.37/1.33  Demodulation         : 0.06
% 2.37/1.33  BG Simplification    : 0.01
% 2.37/1.33  Subsumption          : 0.03
% 2.37/1.33  Abstraction          : 0.01
% 2.37/1.33  MUC search           : 0.00
% 2.37/1.33  Cooper               : 0.00
% 2.37/1.33  Total                : 0.56
% 2.37/1.33  Index Insertion      : 0.00
% 2.37/1.33  Index Deletion       : 0.00
% 2.37/1.33  Index Matching       : 0.00
% 2.37/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
