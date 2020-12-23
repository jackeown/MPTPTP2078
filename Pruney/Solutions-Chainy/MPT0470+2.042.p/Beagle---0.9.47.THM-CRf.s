%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:06 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   69 (  98 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 158 expanded)
%              Number of equality atoms :   36 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_34,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_36,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(c_38,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_81,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_82,plain,(
    ! [A_26] :
      ( v1_relat_1(A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_86,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_82])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k5_relat_1(A_12,B_13))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_20,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_150,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_37,B_38)),k1_relat_1(A_37))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_155,plain,(
    ! [B_38] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_38)),k1_xboole_0)
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_150])).

tff(c_159,plain,(
    ! [B_39] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_39)),k1_xboole_0)
      | ~ v1_relat_1(B_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_155])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_96,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ r1_tarski(B_29,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_96])).

tff(c_169,plain,(
    ! [B_40] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_40)) = k1_xboole_0
      | ~ v1_relat_1(B_40) ) ),
    inference(resolution,[status(thm)],[c_159,c_101])).

tff(c_28,plain,(
    ! [A_14] :
      ( k3_xboole_0(A_14,k2_zfmisc_1(k1_relat_1(A_14),k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_184,plain,(
    ! [B_40] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_40),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_40)))) = k5_relat_1(k1_xboole_0,B_40)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_28])).

tff(c_194,plain,(
    ! [B_41] :
      ( k5_relat_1(k1_xboole_0,B_41) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_41))
      | ~ v1_relat_1(B_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20,c_184])).

tff(c_198,plain,(
    ! [B_13] :
      ( k5_relat_1(k1_xboole_0,B_13) = k1_xboole_0
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_194])).

tff(c_202,plain,(
    ! [B_42] :
      ( k5_relat_1(k1_xboole_0,B_42) = k1_xboole_0
      | ~ v1_relat_1(B_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_198])).

tff(c_211,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_202])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_211])).

tff(c_218,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_220,plain,(
    ! [A_43] :
      ( v1_relat_1(A_43)
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_224,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_220])).

tff(c_18,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_297,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_54,B_55)),k2_relat_1(B_55))
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_305,plain,(
    ! [A_54] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_54,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_297])).

tff(c_311,plain,(
    ! [A_56] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_56,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_305])).

tff(c_255,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_260,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_255])).

tff(c_321,plain,(
    ! [A_57] :
      ( k2_relat_1(k5_relat_1(A_57,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_57) ) ),
    inference(resolution,[status(thm)],[c_311,c_260])).

tff(c_336,plain,(
    ! [A_57] :
      ( k3_xboole_0(k5_relat_1(A_57,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_57,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(A_57,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_57,k1_xboole_0))
      | ~ v1_relat_1(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_28])).

tff(c_480,plain,(
    ! [A_66] :
      ( k5_relat_1(A_66,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_66,k1_xboole_0))
      | ~ v1_relat_1(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18,c_336])).

tff(c_487,plain,(
    ! [A_12] :
      ( k5_relat_1(A_12,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_12) ) ),
    inference(resolution,[status(thm)],[c_26,c_480])).

tff(c_493,plain,(
    ! [A_67] :
      ( k5_relat_1(A_67,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_487])).

tff(c_502,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_493])).

tff(c_509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_502])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:35:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  
% 2.12/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.12/1.28  
% 2.12/1.28  %Foreground sorts:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Background operators:
% 2.12/1.28  
% 2.12/1.28  
% 2.12/1.28  %Foreground operators:
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.28  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.12/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.12/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.12/1.28  
% 2.12/1.30  tff(f_84, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.12/1.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.12/1.30  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.12/1.30  tff(f_56, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.12/1.30  tff(f_34, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.12/1.30  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.12/1.30  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.12/1.30  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.12/1.30  tff(f_36, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.12/1.30  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.12/1.30  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 2.12/1.30  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.12/1.30  tff(c_38, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.30  tff(c_81, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 2.12/1.30  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.12/1.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.12/1.30  tff(c_82, plain, (![A_26]: (v1_relat_1(A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.12/1.30  tff(c_86, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_82])).
% 2.12/1.30  tff(c_26, plain, (![A_12, B_13]: (v1_relat_1(k5_relat_1(A_12, B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.12/1.30  tff(c_10, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.12/1.30  tff(c_20, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.30  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.12/1.30  tff(c_150, plain, (![A_37, B_38]: (r1_tarski(k1_relat_1(k5_relat_1(A_37, B_38)), k1_relat_1(A_37)) | ~v1_relat_1(B_38) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.12/1.30  tff(c_155, plain, (![B_38]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_38)), k1_xboole_0) | ~v1_relat_1(B_38) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_150])).
% 2.12/1.30  tff(c_159, plain, (![B_39]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_39)), k1_xboole_0) | ~v1_relat_1(B_39))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_155])).
% 2.12/1.30  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.12/1.30  tff(c_96, plain, (![B_29, A_30]: (B_29=A_30 | ~r1_tarski(B_29, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.30  tff(c_101, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_96])).
% 2.12/1.30  tff(c_169, plain, (![B_40]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_40))=k1_xboole_0 | ~v1_relat_1(B_40))), inference(resolution, [status(thm)], [c_159, c_101])).
% 2.12/1.30  tff(c_28, plain, (![A_14]: (k3_xboole_0(A_14, k2_zfmisc_1(k1_relat_1(A_14), k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.12/1.30  tff(c_184, plain, (![B_40]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_40), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_40))))=k5_relat_1(k1_xboole_0, B_40) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_40)) | ~v1_relat_1(B_40))), inference(superposition, [status(thm), theory('equality')], [c_169, c_28])).
% 2.12/1.30  tff(c_194, plain, (![B_41]: (k5_relat_1(k1_xboole_0, B_41)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_41)) | ~v1_relat_1(B_41))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20, c_184])).
% 2.12/1.30  tff(c_198, plain, (![B_13]: (k5_relat_1(k1_xboole_0, B_13)=k1_xboole_0 | ~v1_relat_1(B_13) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_194])).
% 2.12/1.30  tff(c_202, plain, (![B_42]: (k5_relat_1(k1_xboole_0, B_42)=k1_xboole_0 | ~v1_relat_1(B_42))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_198])).
% 2.12/1.30  tff(c_211, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_202])).
% 2.12/1.30  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_211])).
% 2.12/1.30  tff(c_218, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.12/1.30  tff(c_220, plain, (![A_43]: (v1_relat_1(A_43) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.12/1.30  tff(c_224, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_220])).
% 2.12/1.30  tff(c_18, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.12/1.30  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.12/1.30  tff(c_297, plain, (![A_54, B_55]: (r1_tarski(k2_relat_1(k5_relat_1(A_54, B_55)), k2_relat_1(B_55)) | ~v1_relat_1(B_55) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.12/1.30  tff(c_305, plain, (![A_54]: (r1_tarski(k2_relat_1(k5_relat_1(A_54, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_34, c_297])).
% 2.12/1.30  tff(c_311, plain, (![A_56]: (r1_tarski(k2_relat_1(k5_relat_1(A_56, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_305])).
% 2.12/1.30  tff(c_255, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.30  tff(c_260, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_255])).
% 2.12/1.30  tff(c_321, plain, (![A_57]: (k2_relat_1(k5_relat_1(A_57, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_57))), inference(resolution, [status(thm)], [c_311, c_260])).
% 2.12/1.30  tff(c_336, plain, (![A_57]: (k3_xboole_0(k5_relat_1(A_57, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_57, k1_xboole_0)), k1_xboole_0))=k5_relat_1(A_57, k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_57, k1_xboole_0)) | ~v1_relat_1(A_57))), inference(superposition, [status(thm), theory('equality')], [c_321, c_28])).
% 2.12/1.30  tff(c_480, plain, (![A_66]: (k5_relat_1(A_66, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_66, k1_xboole_0)) | ~v1_relat_1(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_18, c_336])).
% 2.12/1.30  tff(c_487, plain, (![A_12]: (k5_relat_1(A_12, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_12))), inference(resolution, [status(thm)], [c_26, c_480])).
% 2.12/1.30  tff(c_493, plain, (![A_67]: (k5_relat_1(A_67, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_487])).
% 2.12/1.30  tff(c_502, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_493])).
% 2.12/1.30  tff(c_509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_502])).
% 2.12/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  Inference rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Ref     : 0
% 2.12/1.30  #Sup     : 100
% 2.12/1.30  #Fact    : 0
% 2.12/1.30  #Define  : 0
% 2.12/1.30  #Split   : 1
% 2.12/1.30  #Chain   : 0
% 2.12/1.30  #Close   : 0
% 2.12/1.30  
% 2.12/1.30  Ordering : KBO
% 2.12/1.30  
% 2.12/1.30  Simplification rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Subsume      : 6
% 2.12/1.30  #Demod        : 86
% 2.12/1.30  #Tautology    : 69
% 2.12/1.30  #SimpNegUnit  : 2
% 2.12/1.30  #BackRed      : 0
% 2.12/1.30  
% 2.12/1.30  #Partial instantiations: 0
% 2.12/1.30  #Strategies tried      : 1
% 2.12/1.30  
% 2.12/1.30  Timing (in seconds)
% 2.12/1.30  ----------------------
% 2.12/1.30  Preprocessing        : 0.30
% 2.12/1.30  Parsing              : 0.17
% 2.12/1.30  CNF conversion       : 0.02
% 2.12/1.30  Main loop            : 0.22
% 2.12/1.30  Inferencing          : 0.08
% 2.12/1.30  Reduction            : 0.07
% 2.12/1.30  Demodulation         : 0.05
% 2.12/1.30  BG Simplification    : 0.01
% 2.12/1.30  Subsumption          : 0.04
% 2.12/1.30  Abstraction          : 0.01
% 2.12/1.30  MUC search           : 0.00
% 2.12/1.30  Cooper               : 0.00
% 2.12/1.30  Total                : 0.56
% 2.12/1.30  Index Insertion      : 0.00
% 2.12/1.30  Index Deletion       : 0.00
% 2.12/1.30  Index Matching       : 0.00
% 2.12/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
