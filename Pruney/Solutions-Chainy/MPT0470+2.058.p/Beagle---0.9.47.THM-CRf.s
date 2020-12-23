%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:09 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 112 expanded)
%              Number of leaves         :   27 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :  117 ( 184 expanded)
%              Number of equality atoms :   38 (  64 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_45,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_47,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_82,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_37,axiom,(
    ! [A] : ~ r2_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_xboole_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_36,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_65,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18,plain,(
    ! [A_7] : k1_subset_1(A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [A_8] : v1_xboole_0(k1_subset_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_66,plain,(
    ! [A_24] :
      ( v1_relat_1(A_24)
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_70,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_39,c_66])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k5_relat_1(A_10,B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_133,plain,(
    ! [A_36,B_37] :
      ( k1_relat_1(k5_relat_1(A_36,B_37)) = k1_relat_1(A_36)
      | ~ r1_tarski(k2_relat_1(A_36),k1_relat_1(B_37))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_139,plain,(
    ! [B_37] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_37)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_37))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_133])).

tff(c_144,plain,(
    ! [B_38] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_38)) = k1_xboole_0
      | ~ v1_relat_1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_8,c_34,c_139])).

tff(c_26,plain,(
    ! [A_12] :
      ( r1_tarski(A_12,k2_zfmisc_1(k1_relat_1(A_12),k2_relat_1(A_12)))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_153,plain,(
    ! [B_38] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,B_38),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_38))))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_26])).

tff(c_160,plain,(
    ! [B_39] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,B_39),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_153])).

tff(c_87,plain,(
    ! [A_28,B_29] :
      ( r2_xboole_0(A_28,B_29)
      | B_29 = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_4] : ~ r2_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,(
    ! [A_28] :
      ( k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_87,c_10])).

tff(c_165,plain,(
    ! [B_40] :
      ( k5_relat_1(k1_xboole_0,B_40) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(resolution,[status(thm)],[c_160,c_100])).

tff(c_169,plain,(
    ! [B_11] :
      ( k5_relat_1(k1_xboole_0,B_11) = k1_xboole_0
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_165])).

tff(c_173,plain,(
    ! [B_41] :
      ( k5_relat_1(k1_xboole_0,B_41) = k1_xboole_0
      | ~ v1_relat_1(B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_169])).

tff(c_182,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_173])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_182])).

tff(c_189,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_191,plain,(
    ! [A_42] :
      ( v1_relat_1(A_42)
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_195,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_39,c_191])).

tff(c_14,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_267,plain,(
    ! [B_54,A_55] :
      ( k2_relat_1(k5_relat_1(B_54,A_55)) = k2_relat_1(A_55)
      | ~ r1_tarski(k1_relat_1(A_55),k2_relat_1(B_54))
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_270,plain,(
    ! [B_54] :
      ( k2_relat_1(k5_relat_1(B_54,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_54))
      | ~ v1_relat_1(B_54)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_267])).

tff(c_278,plain,(
    ! [B_56] :
      ( k2_relat_1(k5_relat_1(B_56,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_8,c_32,c_270])).

tff(c_287,plain,(
    ! [B_56] :
      ( r1_tarski(k5_relat_1(B_56,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_56,k1_xboole_0)),k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(B_56,k1_xboole_0))
      | ~ v1_relat_1(B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_26])).

tff(c_294,plain,(
    ! [B_57] :
      ( r1_tarski(k5_relat_1(B_57,k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_57,k1_xboole_0))
      | ~ v1_relat_1(B_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_287])).

tff(c_216,plain,(
    ! [A_46,B_47] :
      ( r2_xboole_0(A_46,B_47)
      | B_47 = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_229,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ r1_tarski(A_46,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_216,c_10])).

tff(c_341,plain,(
    ! [B_61] :
      ( k5_relat_1(B_61,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_61,k1_xboole_0))
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_294,c_229])).

tff(c_345,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_24,c_341])).

tff(c_349,plain,(
    ! [A_62] :
      ( k5_relat_1(A_62,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_345])).

tff(c_358,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_349])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_358])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:20:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.24  
% 2.17/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.24  %$ r2_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.17/1.24  
% 2.17/1.24  %Foreground sorts:
% 2.17/1.24  
% 2.17/1.24  
% 2.17/1.24  %Background operators:
% 2.17/1.24  
% 2.17/1.24  
% 2.17/1.24  %Foreground operators:
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.17/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.24  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.24  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.17/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.24  
% 2.17/1.26  tff(f_89, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.17/1.26  tff(f_45, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.17/1.26  tff(f_47, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc13_subset_1)).
% 2.17/1.26  tff(f_51, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.17/1.26  tff(f_57, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.17/1.26  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.17/1.26  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.17/1.26  tff(f_82, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.17/1.26  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.17/1.26  tff(f_61, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.17/1.26  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.17/1.26  tff(f_37, axiom, (![A]: ~r2_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_xboole_1)).
% 2.17/1.26  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.17/1.26  tff(c_36, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.17/1.26  tff(c_65, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.17/1.26  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.17/1.26  tff(c_18, plain, (![A_7]: (k1_subset_1(A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.26  tff(c_20, plain, (![A_8]: (v1_xboole_0(k1_subset_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.26  tff(c_39, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 2.17/1.26  tff(c_66, plain, (![A_24]: (v1_relat_1(A_24) | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.26  tff(c_70, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_39, c_66])).
% 2.17/1.26  tff(c_24, plain, (![A_10, B_11]: (v1_relat_1(k5_relat_1(A_10, B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.17/1.26  tff(c_16, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.26  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.17/1.26  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.17/1.26  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.17/1.26  tff(c_133, plain, (![A_36, B_37]: (k1_relat_1(k5_relat_1(A_36, B_37))=k1_relat_1(A_36) | ~r1_tarski(k2_relat_1(A_36), k1_relat_1(B_37)) | ~v1_relat_1(B_37) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.17/1.26  tff(c_139, plain, (![B_37]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_37))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_37)) | ~v1_relat_1(B_37) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_133])).
% 2.17/1.26  tff(c_144, plain, (![B_38]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_38))=k1_xboole_0 | ~v1_relat_1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_8, c_34, c_139])).
% 2.17/1.26  tff(c_26, plain, (![A_12]: (r1_tarski(A_12, k2_zfmisc_1(k1_relat_1(A_12), k2_relat_1(A_12))) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.17/1.26  tff(c_153, plain, (![B_38]: (r1_tarski(k5_relat_1(k1_xboole_0, B_38), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_38)))) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_38)) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_144, c_26])).
% 2.17/1.26  tff(c_160, plain, (![B_39]: (r1_tarski(k5_relat_1(k1_xboole_0, B_39), k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_39)) | ~v1_relat_1(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_153])).
% 2.17/1.26  tff(c_87, plain, (![A_28, B_29]: (r2_xboole_0(A_28, B_29) | B_29=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.26  tff(c_10, plain, (![A_4]: (~r2_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.26  tff(c_100, plain, (![A_28]: (k1_xboole_0=A_28 | ~r1_tarski(A_28, k1_xboole_0))), inference(resolution, [status(thm)], [c_87, c_10])).
% 2.17/1.26  tff(c_165, plain, (![B_40]: (k5_relat_1(k1_xboole_0, B_40)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_40)) | ~v1_relat_1(B_40))), inference(resolution, [status(thm)], [c_160, c_100])).
% 2.17/1.26  tff(c_169, plain, (![B_11]: (k5_relat_1(k1_xboole_0, B_11)=k1_xboole_0 | ~v1_relat_1(B_11) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_165])).
% 2.17/1.26  tff(c_173, plain, (![B_41]: (k5_relat_1(k1_xboole_0, B_41)=k1_xboole_0 | ~v1_relat_1(B_41))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_169])).
% 2.17/1.26  tff(c_182, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_173])).
% 2.17/1.26  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_182])).
% 2.17/1.26  tff(c_189, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.17/1.26  tff(c_191, plain, (![A_42]: (v1_relat_1(A_42) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.26  tff(c_195, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_39, c_191])).
% 2.17/1.26  tff(c_14, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.26  tff(c_267, plain, (![B_54, A_55]: (k2_relat_1(k5_relat_1(B_54, A_55))=k2_relat_1(A_55) | ~r1_tarski(k1_relat_1(A_55), k2_relat_1(B_54)) | ~v1_relat_1(B_54) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.17/1.26  tff(c_270, plain, (![B_54]: (k2_relat_1(k5_relat_1(B_54, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_54)) | ~v1_relat_1(B_54) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_267])).
% 2.17/1.26  tff(c_278, plain, (![B_56]: (k2_relat_1(k5_relat_1(B_56, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_56))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_8, c_32, c_270])).
% 2.17/1.26  tff(c_287, plain, (![B_56]: (r1_tarski(k5_relat_1(B_56, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_56, k1_xboole_0)), k1_xboole_0)) | ~v1_relat_1(k5_relat_1(B_56, k1_xboole_0)) | ~v1_relat_1(B_56))), inference(superposition, [status(thm), theory('equality')], [c_278, c_26])).
% 2.17/1.26  tff(c_294, plain, (![B_57]: (r1_tarski(k5_relat_1(B_57, k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_57, k1_xboole_0)) | ~v1_relat_1(B_57))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_287])).
% 2.17/1.26  tff(c_216, plain, (![A_46, B_47]: (r2_xboole_0(A_46, B_47) | B_47=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.17/1.26  tff(c_229, plain, (![A_46]: (k1_xboole_0=A_46 | ~r1_tarski(A_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_216, c_10])).
% 2.17/1.26  tff(c_341, plain, (![B_61]: (k5_relat_1(B_61, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_61, k1_xboole_0)) | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_294, c_229])).
% 2.17/1.26  tff(c_345, plain, (![A_10]: (k5_relat_1(A_10, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_24, c_341])).
% 2.17/1.26  tff(c_349, plain, (![A_62]: (k5_relat_1(A_62, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_345])).
% 2.17/1.26  tff(c_358, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_349])).
% 2.17/1.26  tff(c_364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_358])).
% 2.17/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.26  
% 2.17/1.26  Inference rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Ref     : 0
% 2.17/1.26  #Sup     : 68
% 2.17/1.26  #Fact    : 0
% 2.17/1.26  #Define  : 0
% 2.17/1.26  #Split   : 1
% 2.17/1.26  #Chain   : 0
% 2.17/1.26  #Close   : 0
% 2.17/1.26  
% 2.17/1.26  Ordering : KBO
% 2.17/1.26  
% 2.17/1.26  Simplification rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Subsume      : 2
% 2.17/1.26  #Demod        : 36
% 2.17/1.26  #Tautology    : 40
% 2.17/1.26  #SimpNegUnit  : 2
% 2.17/1.26  #BackRed      : 0
% 2.17/1.26  
% 2.17/1.26  #Partial instantiations: 0
% 2.17/1.26  #Strategies tried      : 1
% 2.17/1.26  
% 2.17/1.26  Timing (in seconds)
% 2.17/1.26  ----------------------
% 2.17/1.26  Preprocessing        : 0.29
% 2.17/1.26  Parsing              : 0.16
% 2.17/1.26  CNF conversion       : 0.02
% 2.17/1.26  Main loop            : 0.22
% 2.17/1.26  Inferencing          : 0.09
% 2.17/1.26  Reduction            : 0.06
% 2.17/1.26  Demodulation         : 0.04
% 2.17/1.26  BG Simplification    : 0.01
% 2.17/1.26  Subsumption          : 0.04
% 2.17/1.26  Abstraction          : 0.01
% 2.17/1.26  MUC search           : 0.00
% 2.17/1.26  Cooper               : 0.00
% 2.17/1.26  Total                : 0.55
% 2.17/1.26  Index Insertion      : 0.00
% 2.17/1.26  Index Deletion       : 0.00
% 2.17/1.26  Index Matching       : 0.00
% 2.17/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
