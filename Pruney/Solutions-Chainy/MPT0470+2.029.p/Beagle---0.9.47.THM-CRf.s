%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:04 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 103 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  122 ( 181 expanded)
%              Number of equality atoms :   32 (  48 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_83,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(c_32,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_57,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_52,plain,(
    ! [A_21] :
      ( v1_relat_1(A_21)
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k5_relat_1(A_8,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_210,plain,(
    ! [A_43,B_44] :
      ( k1_relat_1(k5_relat_1(A_43,B_44)) = k1_relat_1(A_43)
      | ~ r1_tarski(k2_relat_1(A_43),k1_relat_1(B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_219,plain,(
    ! [B_44] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_44)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_44))
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_210])).

tff(c_226,plain,(
    ! [B_45] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_45)) = k1_xboole_0
      | ~ v1_relat_1(B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12,c_30,c_219])).

tff(c_20,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k1_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_238,plain,(
    ! [B_45] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_45))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_45))
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_20])).

tff(c_246,plain,(
    ! [B_46] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_46))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_46))
      | ~ v1_relat_1(B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_238])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_258,plain,(
    ! [B_47] :
      ( k5_relat_1(k1_xboole_0,B_47) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_47))
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_246,c_4])).

tff(c_262,plain,(
    ! [B_9] :
      ( k5_relat_1(k1_xboole_0,B_9) = k1_xboole_0
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_258])).

tff(c_285,plain,(
    ! [B_49] :
      ( k5_relat_1(k1_xboole_0,B_49) = k1_xboole_0
      | ~ v1_relat_1(B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_262])).

tff(c_297,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_285])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_297])).

tff(c_305,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_311,plain,(
    ! [A_50,B_51] :
      ( v1_xboole_0(k2_zfmisc_1(A_50,B_51))
      | ~ v1_xboole_0(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_327,plain,(
    ! [A_55,B_56] :
      ( k2_zfmisc_1(A_55,B_56) = k1_xboole_0
      | ~ v1_xboole_0(B_56) ) ),
    inference(resolution,[status(thm)],[c_311,c_4])).

tff(c_333,plain,(
    ! [A_55] : k2_zfmisc_1(A_55,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_327])).

tff(c_424,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_67,B_68)),k2_relat_1(B_68))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_432,plain,(
    ! [A_67] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_67,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_424])).

tff(c_438,plain,(
    ! [A_69] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_69,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_432])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_443,plain,(
    ! [A_69] :
      ( k2_relat_1(k5_relat_1(A_69,k1_xboole_0)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(k5_relat_1(A_69,k1_xboole_0)))
      | ~ v1_relat_1(A_69) ) ),
    inference(resolution,[status(thm)],[c_438,c_6])).

tff(c_484,plain,(
    ! [A_73] :
      ( k2_relat_1(k5_relat_1(A_73,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_443])).

tff(c_22,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,k2_zfmisc_1(k1_relat_1(A_11),k2_relat_1(A_11)))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_502,plain,(
    ! [A_73] :
      ( r1_tarski(k5_relat_1(A_73,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_73,k1_xboole_0)),k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_73,k1_xboole_0))
      | ~ v1_relat_1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_22])).

tff(c_718,plain,(
    ! [A_83] :
      ( r1_tarski(k5_relat_1(A_83,k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_83,k1_xboole_0))
      | ~ v1_relat_1(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_502])).

tff(c_351,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_360,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_351])).

tff(c_733,plain,(
    ! [A_84] :
      ( k5_relat_1(A_84,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_84,k1_xboole_0))
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_718,c_360])).

tff(c_740,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_18,c_733])).

tff(c_792,plain,(
    ! [A_86] :
      ( k5_relat_1(A_86,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_740])).

tff(c_804,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_792])).

tff(c_812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_804])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n025.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:55:20 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.34  
% 2.70/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.34  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.70/1.34  
% 2.70/1.34  %Foreground sorts:
% 2.70/1.34  
% 2.70/1.34  
% 2.70/1.34  %Background operators:
% 2.70/1.34  
% 2.70/1.34  
% 2.70/1.34  %Foreground operators:
% 2.70/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.34  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.70/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.70/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.70/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.34  
% 2.70/1.36  tff(f_90, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.70/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.70/1.36  tff(f_46, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.70/1.36  tff(f_52, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.70/1.36  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.70/1.36  tff(f_83, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.70/1.36  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.70/1.36  tff(f_60, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.70/1.36  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.70/1.36  tff(f_42, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.70/1.36  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.70/1.36  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.70/1.36  tff(f_64, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.70/1.36  tff(c_32, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.70/1.36  tff(c_57, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 2.70/1.36  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.70/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.70/1.36  tff(c_52, plain, (![A_21]: (v1_relat_1(A_21) | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.70/1.36  tff(c_56, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_52])).
% 2.70/1.36  tff(c_18, plain, (![A_8, B_9]: (v1_relat_1(k5_relat_1(A_8, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.70/1.36  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.70/1.36  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.36  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.36  tff(c_210, plain, (![A_43, B_44]: (k1_relat_1(k5_relat_1(A_43, B_44))=k1_relat_1(A_43) | ~r1_tarski(k2_relat_1(A_43), k1_relat_1(B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.70/1.36  tff(c_219, plain, (![B_44]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_44))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_44)) | ~v1_relat_1(B_44) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_210])).
% 2.70/1.36  tff(c_226, plain, (![B_45]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_45))=k1_xboole_0 | ~v1_relat_1(B_45))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12, c_30, c_219])).
% 2.70/1.36  tff(c_20, plain, (![A_10]: (~v1_xboole_0(k1_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.36  tff(c_238, plain, (![B_45]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_45)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_45)) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_226, c_20])).
% 2.70/1.36  tff(c_246, plain, (![B_46]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_46)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_46)) | ~v1_relat_1(B_46))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_238])).
% 2.70/1.36  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.70/1.36  tff(c_258, plain, (![B_47]: (k5_relat_1(k1_xboole_0, B_47)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_47)) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_246, c_4])).
% 2.70/1.36  tff(c_262, plain, (![B_9]: (k5_relat_1(k1_xboole_0, B_9)=k1_xboole_0 | ~v1_relat_1(B_9) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_258])).
% 2.70/1.36  tff(c_285, plain, (![B_49]: (k5_relat_1(k1_xboole_0, B_49)=k1_xboole_0 | ~v1_relat_1(B_49))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_262])).
% 2.70/1.36  tff(c_297, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_285])).
% 2.70/1.36  tff(c_304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_297])).
% 2.70/1.36  tff(c_305, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 2.70/1.36  tff(c_311, plain, (![A_50, B_51]: (v1_xboole_0(k2_zfmisc_1(A_50, B_51)) | ~v1_xboole_0(B_51))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.70/1.36  tff(c_327, plain, (![A_55, B_56]: (k2_zfmisc_1(A_55, B_56)=k1_xboole_0 | ~v1_xboole_0(B_56))), inference(resolution, [status(thm)], [c_311, c_4])).
% 2.70/1.36  tff(c_333, plain, (![A_55]: (k2_zfmisc_1(A_55, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_327])).
% 2.70/1.36  tff(c_424, plain, (![A_67, B_68]: (r1_tarski(k2_relat_1(k5_relat_1(A_67, B_68)), k2_relat_1(B_68)) | ~v1_relat_1(B_68) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.70/1.36  tff(c_432, plain, (![A_67]: (r1_tarski(k2_relat_1(k5_relat_1(A_67, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_67))), inference(superposition, [status(thm), theory('equality')], [c_28, c_424])).
% 2.70/1.36  tff(c_438, plain, (![A_69]: (r1_tarski(k2_relat_1(k5_relat_1(A_69, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_432])).
% 2.70/1.36  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.70/1.36  tff(c_443, plain, (![A_69]: (k2_relat_1(k5_relat_1(A_69, k1_xboole_0))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_relat_1(k5_relat_1(A_69, k1_xboole_0))) | ~v1_relat_1(A_69))), inference(resolution, [status(thm)], [c_438, c_6])).
% 2.70/1.36  tff(c_484, plain, (![A_73]: (k2_relat_1(k5_relat_1(A_73, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_443])).
% 2.70/1.36  tff(c_22, plain, (![A_11]: (r1_tarski(A_11, k2_zfmisc_1(k1_relat_1(A_11), k2_relat_1(A_11))) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.70/1.36  tff(c_502, plain, (![A_73]: (r1_tarski(k5_relat_1(A_73, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_73, k1_xboole_0)), k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_73, k1_xboole_0)) | ~v1_relat_1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_484, c_22])).
% 2.70/1.36  tff(c_718, plain, (![A_83]: (r1_tarski(k5_relat_1(A_83, k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_83, k1_xboole_0)) | ~v1_relat_1(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_502])).
% 2.70/1.36  tff(c_351, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.70/1.36  tff(c_360, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_351])).
% 2.70/1.36  tff(c_733, plain, (![A_84]: (k5_relat_1(A_84, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_84, k1_xboole_0)) | ~v1_relat_1(A_84))), inference(resolution, [status(thm)], [c_718, c_360])).
% 2.70/1.36  tff(c_740, plain, (![A_8]: (k5_relat_1(A_8, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_18, c_733])).
% 2.70/1.36  tff(c_792, plain, (![A_86]: (k5_relat_1(A_86, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_740])).
% 2.70/1.36  tff(c_804, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_792])).
% 2.70/1.36  tff(c_812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_305, c_804])).
% 2.70/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.36  
% 2.70/1.36  Inference rules
% 2.70/1.36  ----------------------
% 2.70/1.36  #Ref     : 0
% 2.70/1.36  #Sup     : 168
% 2.70/1.36  #Fact    : 0
% 2.70/1.36  #Define  : 0
% 2.70/1.36  #Split   : 1
% 2.70/1.36  #Chain   : 0
% 2.70/1.36  #Close   : 0
% 2.70/1.36  
% 2.70/1.36  Ordering : KBO
% 2.70/1.36  
% 2.70/1.36  Simplification rules
% 2.70/1.36  ----------------------
% 2.70/1.36  #Subsume      : 5
% 2.70/1.36  #Demod        : 211
% 2.70/1.36  #Tautology    : 104
% 2.70/1.36  #SimpNegUnit  : 2
% 2.70/1.36  #BackRed      : 0
% 2.70/1.36  
% 2.70/1.36  #Partial instantiations: 0
% 2.70/1.36  #Strategies tried      : 1
% 2.70/1.36  
% 2.70/1.36  Timing (in seconds)
% 2.70/1.36  ----------------------
% 2.70/1.36  Preprocessing        : 0.28
% 2.70/1.36  Parsing              : 0.16
% 2.70/1.36  CNF conversion       : 0.02
% 2.70/1.36  Main loop            : 0.33
% 2.70/1.36  Inferencing          : 0.13
% 2.70/1.36  Reduction            : 0.10
% 2.70/1.36  Demodulation         : 0.07
% 2.70/1.36  BG Simplification    : 0.02
% 2.70/1.36  Subsumption          : 0.06
% 2.70/1.36  Abstraction          : 0.02
% 2.70/1.36  MUC search           : 0.00
% 2.70/1.36  Cooper               : 0.00
% 2.70/1.36  Total                : 0.65
% 2.70/1.36  Index Insertion      : 0.00
% 2.70/1.36  Index Deletion       : 0.00
% 2.70/1.36  Index Matching       : 0.00
% 2.70/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
