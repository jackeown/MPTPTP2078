%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:28 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 127 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 259 expanded)
%              Number of equality atoms :   27 (  69 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_6','#skF_5'))
    | r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_78,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_223,plain,(
    ! [A_60,C_61,B_62,D_63] :
      ( r1_tarski(A_60,C_61)
      | k2_zfmisc_1(A_60,B_62) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_60,B_62),k2_zfmisc_1(C_61,D_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_243,plain,
    ( r1_tarski('#skF_3','#skF_5')
    | k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_223])).

tff(c_250,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_243])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( k1_xboole_0 = B_17
      | k1_xboole_0 = A_16
      | k2_zfmisc_1(A_16,B_17) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_268,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_26])).

tff(c_270,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_18,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_71,plain,(
    ! [B_29,A_30] :
      ( ~ r1_xboole_0(B_29,A_30)
      | ~ r1_tarski(B_29,A_30)
      | v1_xboole_0(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_74,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_71])).

tff(c_77,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_74])).

tff(c_281,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_77])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_281])).

tff(c_287,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [A_43,B_44,C_45] :
      ( ~ r1_xboole_0(A_43,B_44)
      | ~ r2_hidden(C_45,B_44)
      | ~ r2_hidden(C_45,A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_114,plain,(
    ! [C_46] : ~ r2_hidden(C_46,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_110])).

tff(c_129,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_327,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_129])).

tff(c_363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_36])).

tff(c_365,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_243])).

tff(c_369,plain,(
    ! [B_70,D_71,A_72,C_73] :
      ( r1_tarski(B_70,D_71)
      | k2_zfmisc_1(A_72,B_70) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_72,B_70),k2_zfmisc_1(C_73,D_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_372,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_369])).

tff(c_392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_36,c_372])).

tff(c_393,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_531,plain,(
    ! [A_101,C_102,B_103,D_104] :
      ( r1_tarski(A_101,C_102)
      | k2_zfmisc_1(A_101,B_103) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_101,B_103),k2_zfmisc_1(C_102,D_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_534,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_393,c_531])).

tff(c_553,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_534])).

tff(c_577,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_26])).

tff(c_579,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_577])).

tff(c_426,plain,(
    ! [A_86,B_87,C_88] :
      ( ~ r1_xboole_0(A_86,B_87)
      | ~ r2_hidden(C_88,B_87)
      | ~ r2_hidden(C_88,A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_440,plain,(
    ! [C_92] : ~ r2_hidden(C_92,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_426])).

tff(c_455,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_440])).

tff(c_584,plain,(
    ! [B_2] : r1_tarski('#skF_4',B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_455])).

tff(c_603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_36])).

tff(c_604,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_615,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_77])).

tff(c_620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_615])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:33:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.31  
% 2.51/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.51/1.32  
% 2.51/1.32  %Foreground sorts:
% 2.51/1.32  
% 2.51/1.32  
% 2.51/1.32  %Background operators:
% 2.51/1.32  
% 2.51/1.32  
% 2.51/1.32  %Foreground operators:
% 2.51/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.51/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.51/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.51/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.51/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.51/1.32  
% 2.51/1.33  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.51/1.33  tff(f_90, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.51/1.33  tff(f_82, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.51/1.33  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.51/1.33  tff(f_68, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.51/1.33  tff(f_76, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.51/1.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.51/1.33  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.51/1.33  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.51/1.33  tff(c_36, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.51/1.33  tff(c_38, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_5')) | r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.51/1.33  tff(c_78, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_38])).
% 2.51/1.33  tff(c_223, plain, (![A_60, C_61, B_62, D_63]: (r1_tarski(A_60, C_61) | k2_zfmisc_1(A_60, B_62)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_60, B_62), k2_zfmisc_1(C_61, D_63)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.51/1.33  tff(c_243, plain, (r1_tarski('#skF_3', '#skF_5') | k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_78, c_223])).
% 2.51/1.33  tff(c_250, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_243])).
% 2.51/1.33  tff(c_26, plain, (![B_17, A_16]: (k1_xboole_0=B_17 | k1_xboole_0=A_16 | k2_zfmisc_1(A_16, B_17)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.51/1.33  tff(c_268, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_250, c_26])).
% 2.51/1.33  tff(c_270, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_268])).
% 2.51/1.33  tff(c_18, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.33  tff(c_20, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.51/1.33  tff(c_71, plain, (![B_29, A_30]: (~r1_xboole_0(B_29, A_30) | ~r1_tarski(B_29, A_30) | v1_xboole_0(B_29))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.51/1.33  tff(c_74, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_71])).
% 2.51/1.33  tff(c_77, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_74])).
% 2.51/1.33  tff(c_281, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_77])).
% 2.51/1.33  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_281])).
% 2.51/1.33  tff(c_287, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_268])).
% 2.51/1.33  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.51/1.33  tff(c_110, plain, (![A_43, B_44, C_45]: (~r1_xboole_0(A_43, B_44) | ~r2_hidden(C_45, B_44) | ~r2_hidden(C_45, A_43))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.51/1.33  tff(c_114, plain, (![C_46]: (~r2_hidden(C_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_110])).
% 2.51/1.33  tff(c_129, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_114])).
% 2.51/1.33  tff(c_327, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_287, c_129])).
% 2.51/1.33  tff(c_363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_327, c_36])).
% 2.51/1.33  tff(c_365, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_243])).
% 2.51/1.33  tff(c_369, plain, (![B_70, D_71, A_72, C_73]: (r1_tarski(B_70, D_71) | k2_zfmisc_1(A_72, B_70)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_72, B_70), k2_zfmisc_1(C_73, D_71)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.51/1.33  tff(c_372, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_78, c_369])).
% 2.51/1.33  tff(c_392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_365, c_36, c_372])).
% 2.51/1.33  tff(c_393, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_38])).
% 2.51/1.33  tff(c_531, plain, (![A_101, C_102, B_103, D_104]: (r1_tarski(A_101, C_102) | k2_zfmisc_1(A_101, B_103)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_101, B_103), k2_zfmisc_1(C_102, D_104)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.51/1.33  tff(c_534, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_393, c_531])).
% 2.51/1.33  tff(c_553, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_36, c_534])).
% 2.51/1.33  tff(c_577, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_553, c_26])).
% 2.51/1.33  tff(c_579, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_577])).
% 2.51/1.33  tff(c_426, plain, (![A_86, B_87, C_88]: (~r1_xboole_0(A_86, B_87) | ~r2_hidden(C_88, B_87) | ~r2_hidden(C_88, A_86))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.51/1.33  tff(c_440, plain, (![C_92]: (~r2_hidden(C_92, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_426])).
% 2.51/1.33  tff(c_455, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_440])).
% 2.51/1.33  tff(c_584, plain, (![B_2]: (r1_tarski('#skF_4', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_579, c_455])).
% 2.51/1.33  tff(c_603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_584, c_36])).
% 2.51/1.33  tff(c_604, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_577])).
% 2.51/1.33  tff(c_615, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_604, c_77])).
% 2.51/1.33  tff(c_620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_615])).
% 2.51/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.33  
% 2.51/1.33  Inference rules
% 2.51/1.33  ----------------------
% 2.51/1.33  #Ref     : 0
% 2.51/1.33  #Sup     : 110
% 2.51/1.33  #Fact    : 0
% 2.51/1.33  #Define  : 0
% 2.51/1.33  #Split   : 6
% 2.51/1.33  #Chain   : 0
% 2.51/1.33  #Close   : 0
% 2.51/1.33  
% 2.51/1.33  Ordering : KBO
% 2.51/1.33  
% 2.51/1.33  Simplification rules
% 2.51/1.33  ----------------------
% 2.51/1.33  #Subsume      : 14
% 2.51/1.33  #Demod        : 123
% 2.51/1.33  #Tautology    : 60
% 2.51/1.33  #SimpNegUnit  : 4
% 2.51/1.33  #BackRed      : 62
% 2.51/1.33  
% 2.51/1.33  #Partial instantiations: 0
% 2.51/1.33  #Strategies tried      : 1
% 2.51/1.33  
% 2.51/1.33  Timing (in seconds)
% 2.51/1.33  ----------------------
% 2.51/1.33  Preprocessing        : 0.28
% 2.51/1.33  Parsing              : 0.16
% 2.51/1.34  CNF conversion       : 0.02
% 2.51/1.34  Main loop            : 0.29
% 2.51/1.34  Inferencing          : 0.10
% 2.51/1.34  Reduction            : 0.09
% 2.51/1.34  Demodulation         : 0.06
% 2.51/1.34  BG Simplification    : 0.02
% 2.51/1.34  Subsumption          : 0.06
% 2.51/1.34  Abstraction          : 0.01
% 2.51/1.34  MUC search           : 0.00
% 2.51/1.34  Cooper               : 0.00
% 2.51/1.34  Total                : 0.61
% 2.51/1.34  Index Insertion      : 0.00
% 2.51/1.34  Index Deletion       : 0.00
% 2.51/1.34  Index Matching       : 0.00
% 2.51/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
