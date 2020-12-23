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
% DateTime   : Thu Dec  3 09:59:08 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 141 expanded)
%              Number of leaves         :   30 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  128 ( 250 expanded)
%              Number of equality atoms :   39 (  68 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_95,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(c_42,plain,
    ( k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_81,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,(
    ! [A_26] :
      ( v1_relat_1(A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_57,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k5_relat_1(A_17,B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_110,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_2'(A_42,B_43),B_43)
      | r1_xboole_0(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [B_44,A_45] :
      ( ~ v1_xboole_0(B_44)
      | r1_xboole_0(A_45,B_44) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_121,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = A_48
      | ~ v1_xboole_0(B_49) ) ),
    inference(resolution,[status(thm)],[c_115,c_18])).

tff(c_124,plain,(
    ! [A_48] : k4_xboole_0(A_48,k1_xboole_0) = A_48 ),
    inference(resolution,[status(thm)],[c_6,c_121])).

tff(c_26,plain,(
    ! [B_15] : k2_zfmisc_1(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_40,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_195,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_62,B_63)),k1_relat_1(A_62))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_201,plain,(
    ! [B_63] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_63)),k1_xboole_0)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_195])).

tff(c_206,plain,(
    ! [B_64] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_64)),k1_xboole_0)
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_201])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_209,plain,(
    ! [B_64] :
      ( k4_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,B_64)),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_64) ) ),
    inference(resolution,[status(thm)],[c_206,c_16])).

tff(c_211,plain,(
    ! [B_64] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_64)) = k1_xboole_0
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_209])).

tff(c_175,plain,(
    ! [A_61] :
      ( r1_tarski(A_61,k2_zfmisc_1(k1_relat_1(A_61),k2_relat_1(A_61)))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_237,plain,(
    ! [A_66] :
      ( k4_xboole_0(A_66,k2_zfmisc_1(k1_relat_1(A_66),k2_relat_1(A_66))) = k1_xboole_0
      | ~ v1_relat_1(A_66) ) ),
    inference(resolution,[status(thm)],[c_175,c_16])).

tff(c_250,plain,(
    ! [B_64] :
      ( k4_xboole_0(k5_relat_1(k1_xboole_0,B_64),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_64)))) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_64))
      | ~ v1_relat_1(B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_237])).

tff(c_345,plain,(
    ! [B_77] :
      ( k5_relat_1(k1_xboole_0,B_77) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_77))
      | ~ v1_relat_1(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_26,c_250])).

tff(c_349,plain,(
    ! [B_18] :
      ( k5_relat_1(k1_xboole_0,B_18) = k1_xboole_0
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_30,c_345])).

tff(c_353,plain,(
    ! [B_78] :
      ( k5_relat_1(k1_xboole_0,B_78) = k1_xboole_0
      | ~ v1_relat_1(B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_349])).

tff(c_362,plain,(
    k5_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_353])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_362])).

tff(c_369,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_392,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_2'(A_88,B_89),B_89)
      | r1_xboole_0(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_397,plain,(
    ! [B_90,A_91] :
      ( ~ v1_xboole_0(B_90)
      | r1_xboole_0(A_91,B_90) ) ),
    inference(resolution,[status(thm)],[c_392,c_2])).

tff(c_402,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = A_92
      | ~ v1_xboole_0(B_93) ) ),
    inference(resolution,[status(thm)],[c_397,c_18])).

tff(c_405,plain,(
    ! [A_92] : k4_xboole_0(A_92,k1_xboole_0) = A_92 ),
    inference(resolution,[status(thm)],[c_6,c_402])).

tff(c_24,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_602,plain,(
    ! [A_120,B_121] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_120,B_121)),k2_relat_1(B_121))
      | ~ v1_relat_1(B_121)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_611,plain,(
    ! [A_120] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_120,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_602])).

tff(c_633,plain,(
    ! [A_123] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_123,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_611])).

tff(c_636,plain,(
    ! [A_123] :
      ( k4_xboole_0(k2_relat_1(k5_relat_1(A_123,k1_xboole_0)),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_123) ) ),
    inference(resolution,[status(thm)],[c_633,c_16])).

tff(c_639,plain,(
    ! [A_124] :
      ( k2_relat_1(k5_relat_1(A_124,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_636])).

tff(c_473,plain,(
    ! [A_109] :
      ( r1_tarski(A_109,k2_zfmisc_1(k1_relat_1(A_109),k2_relat_1(A_109)))
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_483,plain,(
    ! [A_109] :
      ( k4_xboole_0(A_109,k2_zfmisc_1(k1_relat_1(A_109),k2_relat_1(A_109))) = k1_xboole_0
      | ~ v1_relat_1(A_109) ) ),
    inference(resolution,[status(thm)],[c_473,c_16])).

tff(c_654,plain,(
    ! [A_124] :
      ( k4_xboole_0(k5_relat_1(A_124,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_124,k1_xboole_0)),k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_124,k1_xboole_0))
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_639,c_483])).

tff(c_767,plain,(
    ! [A_129] :
      ( k5_relat_1(A_129,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_129,k1_xboole_0))
      | ~ v1_relat_1(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_24,c_654])).

tff(c_774,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_17) ) ),
    inference(resolution,[status(thm)],[c_30,c_767])).

tff(c_837,plain,(
    ! [A_132] :
      ( k5_relat_1(A_132,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_774])).

tff(c_846,plain,(
    k5_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_837])).

tff(c_853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_846])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.52  
% 2.87/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.52  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.87/1.52  
% 2.87/1.52  %Foreground sorts:
% 2.87/1.52  
% 2.87/1.52  
% 2.87/1.52  %Background operators:
% 2.87/1.52  
% 2.87/1.52  
% 2.87/1.52  %Foreground operators:
% 2.87/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.87/1.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.87/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.87/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.87/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.87/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.52  
% 2.99/1.54  tff(f_102, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.99/1.54  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.99/1.54  tff(f_68, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.99/1.54  tff(f_74, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.99/1.54  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.99/1.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.99/1.54  tff(f_58, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.99/1.54  tff(f_64, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.99/1.54  tff(f_95, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.99/1.54  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.99/1.54  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.99/1.54  tff(f_78, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.99/1.54  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.99/1.54  tff(c_42, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.99/1.54  tff(c_81, plain, (k5_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_42])).
% 2.99/1.54  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.99/1.54  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.99/1.54  tff(c_53, plain, (![A_26]: (v1_relat_1(A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.99/1.54  tff(c_57, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_53])).
% 2.99/1.54  tff(c_30, plain, (![A_17, B_18]: (v1_relat_1(k5_relat_1(A_17, B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.99/1.54  tff(c_110, plain, (![A_42, B_43]: (r2_hidden('#skF_2'(A_42, B_43), B_43) | r1_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.99/1.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.54  tff(c_115, plain, (![B_44, A_45]: (~v1_xboole_0(B_44) | r1_xboole_0(A_45, B_44))), inference(resolution, [status(thm)], [c_110, c_2])).
% 2.99/1.54  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.99/1.54  tff(c_121, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=A_48 | ~v1_xboole_0(B_49))), inference(resolution, [status(thm)], [c_115, c_18])).
% 2.99/1.54  tff(c_124, plain, (![A_48]: (k4_xboole_0(A_48, k1_xboole_0)=A_48)), inference(resolution, [status(thm)], [c_6, c_121])).
% 2.99/1.54  tff(c_26, plain, (![B_15]: (k2_zfmisc_1(k1_xboole_0, B_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.99/1.54  tff(c_40, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.99/1.54  tff(c_195, plain, (![A_62, B_63]: (r1_tarski(k1_relat_1(k5_relat_1(A_62, B_63)), k1_relat_1(A_62)) | ~v1_relat_1(B_63) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.99/1.54  tff(c_201, plain, (![B_63]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_63)), k1_xboole_0) | ~v1_relat_1(B_63) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_195])).
% 2.99/1.54  tff(c_206, plain, (![B_64]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_64)), k1_xboole_0) | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_201])).
% 2.99/1.54  tff(c_16, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.99/1.54  tff(c_209, plain, (![B_64]: (k4_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0, B_64)), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_64))), inference(resolution, [status(thm)], [c_206, c_16])).
% 2.99/1.54  tff(c_211, plain, (![B_64]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_64))=k1_xboole_0 | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_209])).
% 2.99/1.54  tff(c_175, plain, (![A_61]: (r1_tarski(A_61, k2_zfmisc_1(k1_relat_1(A_61), k2_relat_1(A_61))) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.99/1.54  tff(c_237, plain, (![A_66]: (k4_xboole_0(A_66, k2_zfmisc_1(k1_relat_1(A_66), k2_relat_1(A_66)))=k1_xboole_0 | ~v1_relat_1(A_66))), inference(resolution, [status(thm)], [c_175, c_16])).
% 2.99/1.54  tff(c_250, plain, (![B_64]: (k4_xboole_0(k5_relat_1(k1_xboole_0, B_64), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_64))))=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_64)) | ~v1_relat_1(B_64))), inference(superposition, [status(thm), theory('equality')], [c_211, c_237])).
% 2.99/1.54  tff(c_345, plain, (![B_77]: (k5_relat_1(k1_xboole_0, B_77)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_77)) | ~v1_relat_1(B_77))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_26, c_250])).
% 2.99/1.54  tff(c_349, plain, (![B_18]: (k5_relat_1(k1_xboole_0, B_18)=k1_xboole_0 | ~v1_relat_1(B_18) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_345])).
% 2.99/1.54  tff(c_353, plain, (![B_78]: (k5_relat_1(k1_xboole_0, B_78)=k1_xboole_0 | ~v1_relat_1(B_78))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_349])).
% 2.99/1.54  tff(c_362, plain, (k5_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_353])).
% 2.99/1.54  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_362])).
% 2.99/1.54  tff(c_369, plain, (k5_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_42])).
% 2.99/1.54  tff(c_392, plain, (![A_88, B_89]: (r2_hidden('#skF_2'(A_88, B_89), B_89) | r1_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.99/1.54  tff(c_397, plain, (![B_90, A_91]: (~v1_xboole_0(B_90) | r1_xboole_0(A_91, B_90))), inference(resolution, [status(thm)], [c_392, c_2])).
% 2.99/1.54  tff(c_402, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=A_92 | ~v1_xboole_0(B_93))), inference(resolution, [status(thm)], [c_397, c_18])).
% 2.99/1.54  tff(c_405, plain, (![A_92]: (k4_xboole_0(A_92, k1_xboole_0)=A_92)), inference(resolution, [status(thm)], [c_6, c_402])).
% 2.99/1.54  tff(c_24, plain, (![A_14]: (k2_zfmisc_1(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.99/1.54  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.99/1.54  tff(c_602, plain, (![A_120, B_121]: (r1_tarski(k2_relat_1(k5_relat_1(A_120, B_121)), k2_relat_1(B_121)) | ~v1_relat_1(B_121) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.99/1.54  tff(c_611, plain, (![A_120]: (r1_tarski(k2_relat_1(k5_relat_1(A_120, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_120))), inference(superposition, [status(thm), theory('equality')], [c_38, c_602])).
% 2.99/1.54  tff(c_633, plain, (![A_123]: (r1_tarski(k2_relat_1(k5_relat_1(A_123, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_611])).
% 2.99/1.54  tff(c_636, plain, (![A_123]: (k4_xboole_0(k2_relat_1(k5_relat_1(A_123, k1_xboole_0)), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_123))), inference(resolution, [status(thm)], [c_633, c_16])).
% 2.99/1.54  tff(c_639, plain, (![A_124]: (k2_relat_1(k5_relat_1(A_124, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_405, c_636])).
% 2.99/1.54  tff(c_473, plain, (![A_109]: (r1_tarski(A_109, k2_zfmisc_1(k1_relat_1(A_109), k2_relat_1(A_109))) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.99/1.54  tff(c_483, plain, (![A_109]: (k4_xboole_0(A_109, k2_zfmisc_1(k1_relat_1(A_109), k2_relat_1(A_109)))=k1_xboole_0 | ~v1_relat_1(A_109))), inference(resolution, [status(thm)], [c_473, c_16])).
% 2.99/1.54  tff(c_654, plain, (![A_124]: (k4_xboole_0(k5_relat_1(A_124, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_124, k1_xboole_0)), k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_124, k1_xboole_0)) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_639, c_483])).
% 2.99/1.54  tff(c_767, plain, (![A_129]: (k5_relat_1(A_129, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_129, k1_xboole_0)) | ~v1_relat_1(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_405, c_24, c_654])).
% 2.99/1.54  tff(c_774, plain, (![A_17]: (k5_relat_1(A_17, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_17))), inference(resolution, [status(thm)], [c_30, c_767])).
% 2.99/1.54  tff(c_837, plain, (![A_132]: (k5_relat_1(A_132, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_132))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_774])).
% 2.99/1.54  tff(c_846, plain, (k5_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_837])).
% 2.99/1.54  tff(c_853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_369, c_846])).
% 2.99/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.99/1.54  
% 2.99/1.54  Inference rules
% 2.99/1.54  ----------------------
% 2.99/1.54  #Ref     : 0
% 2.99/1.54  #Sup     : 173
% 2.99/1.54  #Fact    : 0
% 2.99/1.54  #Define  : 0
% 2.99/1.54  #Split   : 1
% 2.99/1.54  #Chain   : 0
% 2.99/1.54  #Close   : 0
% 2.99/1.54  
% 2.99/1.54  Ordering : KBO
% 2.99/1.54  
% 2.99/1.54  Simplification rules
% 2.99/1.54  ----------------------
% 2.99/1.54  #Subsume      : 8
% 2.99/1.54  #Demod        : 162
% 2.99/1.54  #Tautology    : 104
% 2.99/1.54  #SimpNegUnit  : 2
% 2.99/1.54  #BackRed      : 0
% 2.99/1.54  
% 2.99/1.54  #Partial instantiations: 0
% 2.99/1.54  #Strategies tried      : 1
% 2.99/1.54  
% 2.99/1.54  Timing (in seconds)
% 2.99/1.54  ----------------------
% 2.99/1.54  Preprocessing        : 0.35
% 2.99/1.54  Parsing              : 0.19
% 2.99/1.54  CNF conversion       : 0.03
% 2.99/1.54  Main loop            : 0.33
% 2.99/1.54  Inferencing          : 0.13
% 2.99/1.54  Reduction            : 0.09
% 2.99/1.54  Demodulation         : 0.06
% 2.99/1.54  BG Simplification    : 0.02
% 2.99/1.54  Subsumption          : 0.06
% 2.99/1.54  Abstraction          : 0.02
% 2.99/1.54  MUC search           : 0.00
% 2.99/1.54  Cooper               : 0.00
% 2.99/1.54  Total                : 0.72
% 2.99/1.54  Index Insertion      : 0.00
% 2.99/1.54  Index Deletion       : 0.00
% 2.99/1.54  Index Matching       : 0.00
% 2.99/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
