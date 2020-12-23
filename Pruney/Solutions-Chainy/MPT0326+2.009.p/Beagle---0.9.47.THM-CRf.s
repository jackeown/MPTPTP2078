%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:29 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 136 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :    8
%              Number of atoms          :   81 ( 236 expanded)
%              Number of equality atoms :   24 (  64 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B,C,D] :
            ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
              | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
           => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_14,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_6','#skF_5'))
    | r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_66,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_243,plain,(
    ! [B_55,D_56,A_57,C_58] :
      ( r1_tarski(B_55,D_56)
      | k2_zfmisc_1(A_57,B_55) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_57,B_55),k2_zfmisc_1(C_58,D_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_246,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_243])).

tff(c_261,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_246])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k1_xboole_0 = B_15
      | k1_xboole_0 = A_14
      | k2_zfmisc_1(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_289,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_16])).

tff(c_291,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_61,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = A_30
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65,plain,(
    ! [A_12] : k3_xboole_0(k1_xboole_0,A_12) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_61])).

tff(c_89,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,k3_xboole_0(A_35,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,(
    ! [A_12,C_37] :
      ( ~ r1_xboole_0(k1_xboole_0,A_12)
      | ~ r2_hidden(C_37,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_89])).

tff(c_111,plain,(
    ! [C_40] : ~ r2_hidden(C_40,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_116,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_111])).

tff(c_295,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_116])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_295])).

tff(c_305,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_343,plain,(
    ! [A_12] : r1_tarski('#skF_4',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_12])).

tff(c_355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_26])).

tff(c_357,plain,(
    ! [A_63] : ~ r1_xboole_0(k1_xboole_0,A_63) ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_362,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_357])).

tff(c_363,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_448,plain,(
    ! [A_78,C_79,B_80,D_81] :
      ( r1_tarski(A_78,C_79)
      | k2_zfmisc_1(A_78,B_80) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_78,B_80),k2_zfmisc_1(C_79,D_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_451,plain,
    ( r1_tarski('#skF_4','#skF_6')
    | k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_363,c_448])).

tff(c_466,plain,(
    k2_zfmisc_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_451])).

tff(c_489,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_16])).

tff(c_491,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_489])).

tff(c_501,plain,(
    ! [A_12] : r1_tarski('#skF_4',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_12])).

tff(c_513,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_501,c_26])).

tff(c_514,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_489])).

tff(c_387,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,k3_xboole_0(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_390,plain,(
    ! [A_12,C_69] :
      ( ~ r1_xboole_0(k1_xboole_0,A_12)
      | ~ r2_hidden(C_69,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_387])).

tff(c_397,plain,(
    ! [C_70] : ~ r2_hidden(C_70,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_390])).

tff(c_402,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_397])).

tff(c_519,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_402])).

tff(c_528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_519])).

tff(c_530,plain,(
    ! [A_82] : ~ r1_xboole_0(k1_xboole_0,A_82) ),
    inference(splitRight,[status(thm)],[c_390])).

tff(c_535,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_530])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.30  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 2.23/1.30  
% 2.23/1.30  %Foreground sorts:
% 2.23/1.30  
% 2.23/1.30  
% 2.23/1.30  %Background operators:
% 2.23/1.30  
% 2.23/1.30  
% 2.23/1.30  %Foreground operators:
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.23/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.30  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.30  
% 2.23/1.32  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.23/1.32  tff(f_78, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.23/1.32  tff(f_67, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.23/1.32  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.23/1.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.23/1.32  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.23/1.32  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.23/1.32  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.23/1.32  tff(c_14, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.23/1.32  tff(c_30, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.23/1.32  tff(c_26, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.23/1.32  tff(c_28, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_5')) | r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.23/1.32  tff(c_66, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_28])).
% 2.23/1.32  tff(c_243, plain, (![B_55, D_56, A_57, C_58]: (r1_tarski(B_55, D_56) | k2_zfmisc_1(A_57, B_55)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_57, B_55), k2_zfmisc_1(C_58, D_56)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.23/1.32  tff(c_246, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_243])).
% 2.23/1.32  tff(c_261, plain, (k2_zfmisc_1('#skF_3', '#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_26, c_246])).
% 2.23/1.32  tff(c_16, plain, (![B_15, A_14]: (k1_xboole_0=B_15 | k1_xboole_0=A_14 | k2_zfmisc_1(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.32  tff(c_289, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_261, c_16])).
% 2.23/1.32  tff(c_291, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_289])).
% 2.23/1.32  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.32  tff(c_12, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.23/1.32  tff(c_61, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=A_30 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.32  tff(c_65, plain, (![A_12]: (k3_xboole_0(k1_xboole_0, A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_61])).
% 2.23/1.32  tff(c_89, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, k3_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.23/1.32  tff(c_92, plain, (![A_12, C_37]: (~r1_xboole_0(k1_xboole_0, A_12) | ~r2_hidden(C_37, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_65, c_89])).
% 2.23/1.32  tff(c_111, plain, (![C_40]: (~r2_hidden(C_40, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_92])).
% 2.23/1.32  tff(c_116, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_111])).
% 2.23/1.32  tff(c_295, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_116])).
% 2.23/1.32  tff(c_304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_295])).
% 2.23/1.32  tff(c_305, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_289])).
% 2.23/1.32  tff(c_343, plain, (![A_12]: (r1_tarski('#skF_4', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_305, c_12])).
% 2.23/1.32  tff(c_355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_343, c_26])).
% 2.23/1.32  tff(c_357, plain, (![A_63]: (~r1_xboole_0(k1_xboole_0, A_63))), inference(splitRight, [status(thm)], [c_92])).
% 2.23/1.32  tff(c_362, plain, $false, inference(resolution, [status(thm)], [c_14, c_357])).
% 2.23/1.32  tff(c_363, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_28])).
% 2.23/1.32  tff(c_448, plain, (![A_78, C_79, B_80, D_81]: (r1_tarski(A_78, C_79) | k2_zfmisc_1(A_78, B_80)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_78, B_80), k2_zfmisc_1(C_79, D_81)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.23/1.32  tff(c_451, plain, (r1_tarski('#skF_4', '#skF_6') | k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_363, c_448])).
% 2.23/1.32  tff(c_466, plain, (k2_zfmisc_1('#skF_4', '#skF_3')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_26, c_451])).
% 2.23/1.32  tff(c_489, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_466, c_16])).
% 2.23/1.32  tff(c_491, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_489])).
% 2.23/1.32  tff(c_501, plain, (![A_12]: (r1_tarski('#skF_4', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_491, c_12])).
% 2.23/1.32  tff(c_513, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_501, c_26])).
% 2.23/1.32  tff(c_514, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_489])).
% 2.23/1.32  tff(c_387, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, k3_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.23/1.32  tff(c_390, plain, (![A_12, C_69]: (~r1_xboole_0(k1_xboole_0, A_12) | ~r2_hidden(C_69, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_65, c_387])).
% 2.23/1.32  tff(c_397, plain, (![C_70]: (~r2_hidden(C_70, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_390])).
% 2.23/1.32  tff(c_402, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_397])).
% 2.23/1.32  tff(c_519, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_514, c_402])).
% 2.23/1.32  tff(c_528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_519])).
% 2.23/1.32  tff(c_530, plain, (![A_82]: (~r1_xboole_0(k1_xboole_0, A_82))), inference(splitRight, [status(thm)], [c_390])).
% 2.23/1.32  tff(c_535, plain, $false, inference(resolution, [status(thm)], [c_14, c_530])).
% 2.23/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.32  
% 2.23/1.32  Inference rules
% 2.23/1.32  ----------------------
% 2.23/1.32  #Ref     : 0
% 2.23/1.32  #Sup     : 103
% 2.23/1.32  #Fact    : 0
% 2.23/1.32  #Define  : 0
% 2.23/1.32  #Split   : 7
% 2.23/1.32  #Chain   : 0
% 2.23/1.32  #Close   : 0
% 2.23/1.32  
% 2.23/1.32  Ordering : KBO
% 2.23/1.32  
% 2.23/1.32  Simplification rules
% 2.23/1.32  ----------------------
% 2.23/1.32  #Subsume      : 4
% 2.23/1.32  #Demod        : 125
% 2.23/1.32  #Tautology    : 60
% 2.23/1.32  #SimpNegUnit  : 10
% 2.23/1.32  #BackRed      : 58
% 2.23/1.32  
% 2.23/1.32  #Partial instantiations: 0
% 2.23/1.32  #Strategies tried      : 1
% 2.23/1.32  
% 2.23/1.32  Timing (in seconds)
% 2.23/1.32  ----------------------
% 2.23/1.32  Preprocessing        : 0.27
% 2.23/1.32  Parsing              : 0.15
% 2.23/1.32  CNF conversion       : 0.02
% 2.23/1.32  Main loop            : 0.26
% 2.23/1.32  Inferencing          : 0.09
% 2.23/1.32  Reduction            : 0.09
% 2.23/1.32  Demodulation         : 0.06
% 2.23/1.32  BG Simplification    : 0.02
% 2.23/1.32  Subsumption          : 0.04
% 2.23/1.32  Abstraction          : 0.01
% 2.23/1.32  MUC search           : 0.00
% 2.23/1.32  Cooper               : 0.00
% 2.23/1.32  Total                : 0.56
% 2.23/1.32  Index Insertion      : 0.00
% 2.23/1.32  Index Deletion       : 0.00
% 2.23/1.32  Index Matching       : 0.00
% 2.23/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
