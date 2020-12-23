%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:29 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 201 expanded)
%              Number of leaves         :   22 (  71 expanded)
%              Depth                    :    9
%              Number of atoms          :  104 ( 409 expanded)
%              Number of equality atoms :   36 ( 123 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_6','#skF_5'))
    | r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_66,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_269,plain,(
    ! [A_61,C_62,B_63,D_64] :
      ( r1_tarski(A_61,C_62)
      | k2_zfmisc_1(A_61,B_63) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_61,B_63),k2_zfmisc_1(C_62,D_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_285,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_269])).

tff(c_291,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k2_zfmisc_1(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_308,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_16])).

tff(c_310,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_116,plain,(
    ! [A_44,C_45,B_46,D_47] :
      ( r1_tarski(A_44,C_45)
      | k2_zfmisc_1(A_44,B_46) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_44,B_46),k2_zfmisc_1(C_45,D_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_132,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_116])).

tff(c_137,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_154,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_16])).

tff(c_156,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_85,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,B_39)
      | ~ r2_hidden(C_40,A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_95,plain,(
    ! [C_41,A_42] :
      ( ~ r2_hidden(C_41,k1_xboole_0)
      | ~ r2_hidden(C_41,A_42) ) ),
    inference(resolution,[status(thm)],[c_14,c_85])).

tff(c_108,plain,(
    ! [A_42] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0),A_42)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_95])).

tff(c_110,plain,(
    ! [A_43] : ~ r2_hidden('#skF_1'(k1_xboole_0),A_43) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_115,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_110])).

tff(c_158,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_115])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_158])).

tff(c_169,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_12,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_206,plain,(
    ! [A_10] : r1_tarski('#skF_4',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_12])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_26])).

tff(c_220,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_232,plain,(
    ! [B_54,D_55,A_56,C_57] :
      ( r1_tarski(B_54,D_55)
      | k2_zfmisc_1(A_56,B_54) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_56,B_54),k2_zfmisc_1(C_57,D_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_235,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_232])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_26,c_235])).

tff(c_252,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_314,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_252])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_314])).

tff(c_323,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_360,plain,(
    ! [A_10] : r1_tarski('#skF_4',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_12])).

tff(c_372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_26])).

tff(c_374,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_384,plain,(
    ! [B_72,D_73,A_74,C_75] :
      ( r1_tarski(B_72,D_73)
      | k2_zfmisc_1(A_74,B_72) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_74,B_72),k2_zfmisc_1(C_75,D_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_387,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_384])).

tff(c_403,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_374,c_26,c_387])).

tff(c_404,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_449,plain,(
    ! [A_89,C_90,B_91,D_92] :
      ( r1_tarski(A_89,C_90)
      | k2_zfmisc_1(A_89,B_91) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_89,B_91),k2_zfmisc_1(C_90,D_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_452,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_404,c_449])).

tff(c_467,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_452])).

tff(c_488,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_16])).

tff(c_490,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_488])).

tff(c_497,plain,(
    ! [A_10] : r1_tarski('#skF_4',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_12])).

tff(c_509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_26])).

tff(c_510,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_488])).

tff(c_518,plain,(
    ! [A_10] : r1_tarski('#skF_3',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_12])).

tff(c_20,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_517,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_3',B_13) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_510,c_20])).

tff(c_405,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_560,plain,(
    ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_405])).

tff(c_563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_560])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:40:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.34  
% 2.05/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 2.05/1.34  
% 2.05/1.34  %Foreground sorts:
% 2.05/1.34  
% 2.05/1.34  
% 2.05/1.34  %Background operators:
% 2.05/1.34  
% 2.05/1.34  
% 2.05/1.34  %Foreground operators:
% 2.05/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.05/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.05/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.05/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.05/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.05/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.05/1.34  
% 2.37/1.35  tff(f_78, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.37/1.35  tff(f_67, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.37/1.35  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.37/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.37/1.35  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.37/1.35  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.37/1.35  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.37/1.35  tff(c_26, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.37/1.35  tff(c_30, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.37/1.35  tff(c_28, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_5')) | r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.37/1.35  tff(c_66, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_28])).
% 2.37/1.35  tff(c_269, plain, (![A_61, C_62, B_63, D_64]: (r1_tarski(A_61, C_62) | k2_zfmisc_1(A_61, B_63)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_61, B_63), k2_zfmisc_1(C_62, D_64)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.37/1.35  tff(c_285, plain, (r1_tarski('#skF_3', '#skF_5') | k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_269])).
% 2.37/1.35  tff(c_291, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_285])).
% 2.37/1.35  tff(c_16, plain, (![B_13, A_12]: (k1_xboole_0=B_13 | k1_xboole_0=A_12 | k2_zfmisc_1(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.37/1.35  tff(c_308, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_291, c_16])).
% 2.37/1.35  tff(c_310, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_308])).
% 2.37/1.35  tff(c_116, plain, (![A_44, C_45, B_46, D_47]: (r1_tarski(A_44, C_45) | k2_zfmisc_1(A_44, B_46)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_44, B_46), k2_zfmisc_1(C_45, D_47)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.37/1.35  tff(c_132, plain, (r1_tarski('#skF_3', '#skF_5') | k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_116])).
% 2.37/1.35  tff(c_137, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_132])).
% 2.37/1.35  tff(c_154, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_137, c_16])).
% 2.37/1.35  tff(c_156, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_154])).
% 2.37/1.35  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.37/1.35  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.37/1.35  tff(c_85, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, B_39) | ~r2_hidden(C_40, A_38))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.37/1.35  tff(c_95, plain, (![C_41, A_42]: (~r2_hidden(C_41, k1_xboole_0) | ~r2_hidden(C_41, A_42))), inference(resolution, [status(thm)], [c_14, c_85])).
% 2.37/1.35  tff(c_108, plain, (![A_42]: (~r2_hidden('#skF_1'(k1_xboole_0), A_42) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_95])).
% 2.37/1.35  tff(c_110, plain, (![A_43]: (~r2_hidden('#skF_1'(k1_xboole_0), A_43))), inference(splitLeft, [status(thm)], [c_108])).
% 2.37/1.35  tff(c_115, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_110])).
% 2.37/1.35  tff(c_158, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_115])).
% 2.37/1.35  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_158])).
% 2.37/1.35  tff(c_169, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_154])).
% 2.37/1.35  tff(c_12, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.37/1.35  tff(c_206, plain, (![A_10]: (r1_tarski('#skF_4', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_12])).
% 2.37/1.35  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_206, c_26])).
% 2.37/1.35  tff(c_220, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_132])).
% 2.37/1.35  tff(c_232, plain, (![B_54, D_55, A_56, C_57]: (r1_tarski(B_54, D_55) | k2_zfmisc_1(A_56, B_54)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_56, B_54), k2_zfmisc_1(C_57, D_55)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.37/1.35  tff(c_235, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_232])).
% 2.37/1.35  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_220, c_26, c_235])).
% 2.37/1.35  tff(c_252, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_108])).
% 2.37/1.35  tff(c_314, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_310, c_252])).
% 2.37/1.35  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_314])).
% 2.37/1.35  tff(c_323, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_308])).
% 2.37/1.35  tff(c_360, plain, (![A_10]: (r1_tarski('#skF_4', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_12])).
% 2.37/1.35  tff(c_372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_360, c_26])).
% 2.37/1.35  tff(c_374, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_285])).
% 2.37/1.35  tff(c_384, plain, (![B_72, D_73, A_74, C_75]: (r1_tarski(B_72, D_73) | k2_zfmisc_1(A_74, B_72)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_74, B_72), k2_zfmisc_1(C_75, D_73)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.37/1.35  tff(c_387, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_384])).
% 2.37/1.35  tff(c_403, plain, $false, inference(negUnitSimplification, [status(thm)], [c_374, c_26, c_387])).
% 2.37/1.35  tff(c_404, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_28])).
% 2.37/1.35  tff(c_449, plain, (![A_89, C_90, B_91, D_92]: (r1_tarski(A_89, C_90) | k2_zfmisc_1(A_89, B_91)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_89, B_91), k2_zfmisc_1(C_90, D_92)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.37/1.35  tff(c_452, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_404, c_449])).
% 2.37/1.35  tff(c_467, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_26, c_452])).
% 2.37/1.35  tff(c_488, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_467, c_16])).
% 2.37/1.35  tff(c_490, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_488])).
% 2.37/1.35  tff(c_497, plain, (![A_10]: (r1_tarski('#skF_4', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_490, c_12])).
% 2.37/1.35  tff(c_509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_497, c_26])).
% 2.37/1.35  tff(c_510, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_488])).
% 2.37/1.35  tff(c_518, plain, (![A_10]: (r1_tarski('#skF_3', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_12])).
% 2.37/1.35  tff(c_20, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.37/1.35  tff(c_517, plain, (![B_13]: (k2_zfmisc_1('#skF_3', B_13)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_510, c_510, c_20])).
% 2.37/1.35  tff(c_405, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_28])).
% 2.37/1.35  tff(c_560, plain, (~r1_tarski('#skF_3', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_517, c_405])).
% 2.37/1.35  tff(c_563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_518, c_560])).
% 2.37/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.35  
% 2.37/1.35  Inference rules
% 2.37/1.35  ----------------------
% 2.37/1.35  #Ref     : 0
% 2.37/1.35  #Sup     : 109
% 2.37/1.35  #Fact    : 0
% 2.37/1.35  #Define  : 0
% 2.37/1.35  #Split   : 8
% 2.37/1.35  #Chain   : 0
% 2.37/1.35  #Close   : 0
% 2.37/1.35  
% 2.37/1.35  Ordering : KBO
% 2.37/1.35  
% 2.37/1.35  Simplification rules
% 2.37/1.35  ----------------------
% 2.37/1.35  #Subsume      : 5
% 2.37/1.35  #Demod        : 148
% 2.37/1.35  #Tautology    : 62
% 2.37/1.35  #SimpNegUnit  : 5
% 2.37/1.35  #BackRed      : 67
% 2.37/1.35  
% 2.37/1.35  #Partial instantiations: 0
% 2.37/1.35  #Strategies tried      : 1
% 2.37/1.35  
% 2.37/1.35  Timing (in seconds)
% 2.37/1.35  ----------------------
% 2.37/1.36  Preprocessing        : 0.28
% 2.37/1.36  Parsing              : 0.16
% 2.37/1.36  CNF conversion       : 0.02
% 2.37/1.36  Main loop            : 0.27
% 2.37/1.36  Inferencing          : 0.10
% 2.37/1.36  Reduction            : 0.08
% 2.37/1.36  Demodulation         : 0.06
% 2.37/1.36  BG Simplification    : 0.02
% 2.37/1.36  Subsumption          : 0.05
% 2.37/1.36  Abstraction          : 0.01
% 2.37/1.36  MUC search           : 0.00
% 2.37/1.36  Cooper               : 0.00
% 2.37/1.36  Total                : 0.58
% 2.37/1.36  Index Insertion      : 0.00
% 2.37/1.36  Index Deletion       : 0.00
% 2.37/1.36  Index Matching       : 0.00
% 2.37/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
