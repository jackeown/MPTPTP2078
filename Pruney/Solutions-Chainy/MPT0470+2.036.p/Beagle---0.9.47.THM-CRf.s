%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:05 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   63 (  97 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  113 ( 171 expanded)
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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_85,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(c_36,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_77,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_72,plain,(
    ! [A_22] :
      ( v1_relat_1(A_22)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_76,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_72])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k5_relat_1(A_8,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_201,plain,(
    ! [A_39,B_40] :
      ( k1_relat_1(k5_relat_1(A_39,B_40)) = k1_relat_1(A_39)
      | ~ r1_tarski(k2_relat_1(A_39),k1_relat_1(B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_210,plain,(
    ! [B_40] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_40)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_201])).

tff(c_339,plain,(
    ! [B_44] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_44)) = k1_xboole_0
      | ~ v1_relat_1(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_12,c_34,c_210])).

tff(c_24,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k1_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_351,plain,(
    ! [B_44] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_44))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_44))
      | ~ v1_relat_1(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_24])).

tff(c_365,plain,(
    ! [B_45] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_45))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_45))
      | ~ v1_relat_1(B_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_351])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_379,plain,(
    ! [B_46] :
      ( k5_relat_1(k1_xboole_0,B_46) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_46))
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_365,c_4])).

tff(c_386,plain,(
    ! [B_9] :
      ( k5_relat_1(k1_xboole_0,B_9) = k1_xboole_0
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_379])).

tff(c_392,plain,(
    ! [B_47] :
      ( k5_relat_1(k1_xboole_0,B_47) = k1_xboole_0
      | ~ v1_relat_1(B_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_386])).

tff(c_401,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_392])).

tff(c_408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_401])).

tff(c_409,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_16,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_481,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_58,B_59)),k2_relat_1(B_59))
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_489,plain,(
    ! [A_58] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_58,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_481])).

tff(c_532,plain,(
    ! [A_63] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_63,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_489])).

tff(c_433,plain,(
    ! [B_52,A_53] :
      ( B_52 = A_53
      | ~ r1_tarski(B_52,A_53)
      | ~ r1_tarski(A_53,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_442,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_433])).

tff(c_542,plain,(
    ! [A_64] :
      ( k2_relat_1(k5_relat_1(A_64,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_64) ) ),
    inference(resolution,[status(thm)],[c_532,c_442])).

tff(c_26,plain,(
    ! [A_11] :
      ( r1_tarski(A_11,k2_zfmisc_1(k1_relat_1(A_11),k2_relat_1(A_11)))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_560,plain,(
    ! [A_64] :
      ( r1_tarski(k5_relat_1(A_64,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(A_64,k1_xboole_0)),k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_64,k1_xboole_0))
      | ~ v1_relat_1(A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_542,c_26])).

tff(c_754,plain,(
    ! [A_73] :
      ( r1_tarski(k5_relat_1(A_73,k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_73,k1_xboole_0))
      | ~ v1_relat_1(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_560])).

tff(c_794,plain,(
    ! [A_76] :
      ( k5_relat_1(A_76,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_76,k1_xboole_0))
      | ~ v1_relat_1(A_76) ) ),
    inference(resolution,[status(thm)],[c_754,c_442])).

tff(c_801,plain,(
    ! [A_8] :
      ( k5_relat_1(A_8,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_22,c_794])).

tff(c_807,plain,(
    ! [A_77] :
      ( k5_relat_1(A_77,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_801])).

tff(c_816,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_807])).

tff(c_823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_816])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.35  
% 2.51/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.36  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.51/1.36  
% 2.51/1.36  %Foreground sorts:
% 2.51/1.36  
% 2.51/1.36  
% 2.51/1.36  %Background operators:
% 2.51/1.36  
% 2.51/1.36  
% 2.51/1.36  %Foreground operators:
% 2.51/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.51/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.51/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.51/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.36  
% 2.71/1.37  tff(f_92, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.71/1.37  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.71/1.37  tff(f_48, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.71/1.37  tff(f_54, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.71/1.37  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.71/1.37  tff(f_85, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.71/1.37  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 2.71/1.37  tff(f_62, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.71/1.37  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.71/1.37  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.71/1.37  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 2.71/1.37  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.71/1.37  tff(f_66, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.71/1.37  tff(c_36, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.71/1.37  tff(c_77, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.71/1.37  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.71/1.37  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.71/1.37  tff(c_72, plain, (![A_22]: (v1_relat_1(A_22) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.71/1.37  tff(c_76, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_72])).
% 2.71/1.37  tff(c_22, plain, (![A_8, B_9]: (v1_relat_1(k5_relat_1(A_8, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.71/1.37  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.71/1.37  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.71/1.37  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.71/1.37  tff(c_201, plain, (![A_39, B_40]: (k1_relat_1(k5_relat_1(A_39, B_40))=k1_relat_1(A_39) | ~r1_tarski(k2_relat_1(A_39), k1_relat_1(B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.71/1.37  tff(c_210, plain, (![B_40]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_40))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_32, c_201])).
% 2.71/1.37  tff(c_339, plain, (![B_44]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_44))=k1_xboole_0 | ~v1_relat_1(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_12, c_34, c_210])).
% 2.71/1.37  tff(c_24, plain, (![A_10]: (~v1_xboole_0(k1_relat_1(A_10)) | ~v1_relat_1(A_10) | v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.71/1.37  tff(c_351, plain, (![B_44]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_44)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_44)) | ~v1_relat_1(B_44))), inference(superposition, [status(thm), theory('equality')], [c_339, c_24])).
% 2.71/1.37  tff(c_365, plain, (![B_45]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_45)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_45)) | ~v1_relat_1(B_45))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_351])).
% 2.71/1.37  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.71/1.37  tff(c_379, plain, (![B_46]: (k5_relat_1(k1_xboole_0, B_46)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_46)) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_365, c_4])).
% 2.71/1.37  tff(c_386, plain, (![B_9]: (k5_relat_1(k1_xboole_0, B_9)=k1_xboole_0 | ~v1_relat_1(B_9) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_379])).
% 2.71/1.37  tff(c_392, plain, (![B_47]: (k5_relat_1(k1_xboole_0, B_47)=k1_xboole_0 | ~v1_relat_1(B_47))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_386])).
% 2.71/1.37  tff(c_401, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_392])).
% 2.71/1.37  tff(c_408, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_401])).
% 2.71/1.37  tff(c_409, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.71/1.37  tff(c_16, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.71/1.37  tff(c_481, plain, (![A_58, B_59]: (r1_tarski(k2_relat_1(k5_relat_1(A_58, B_59)), k2_relat_1(B_59)) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.71/1.37  tff(c_489, plain, (![A_58]: (r1_tarski(k2_relat_1(k5_relat_1(A_58, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_58))), inference(superposition, [status(thm), theory('equality')], [c_32, c_481])).
% 2.71/1.37  tff(c_532, plain, (![A_63]: (r1_tarski(k2_relat_1(k5_relat_1(A_63, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_489])).
% 2.71/1.37  tff(c_433, plain, (![B_52, A_53]: (B_52=A_53 | ~r1_tarski(B_52, A_53) | ~r1_tarski(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.71/1.37  tff(c_442, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_433])).
% 2.71/1.37  tff(c_542, plain, (![A_64]: (k2_relat_1(k5_relat_1(A_64, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_64))), inference(resolution, [status(thm)], [c_532, c_442])).
% 2.71/1.37  tff(c_26, plain, (![A_11]: (r1_tarski(A_11, k2_zfmisc_1(k1_relat_1(A_11), k2_relat_1(A_11))) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.71/1.37  tff(c_560, plain, (![A_64]: (r1_tarski(k5_relat_1(A_64, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(A_64, k1_xboole_0)), k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_64, k1_xboole_0)) | ~v1_relat_1(A_64))), inference(superposition, [status(thm), theory('equality')], [c_542, c_26])).
% 2.71/1.37  tff(c_754, plain, (![A_73]: (r1_tarski(k5_relat_1(A_73, k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_73, k1_xboole_0)) | ~v1_relat_1(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_560])).
% 2.71/1.37  tff(c_794, plain, (![A_76]: (k5_relat_1(A_76, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_76, k1_xboole_0)) | ~v1_relat_1(A_76))), inference(resolution, [status(thm)], [c_754, c_442])).
% 2.71/1.37  tff(c_801, plain, (![A_8]: (k5_relat_1(A_8, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_22, c_794])).
% 2.71/1.37  tff(c_807, plain, (![A_77]: (k5_relat_1(A_77, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_801])).
% 2.71/1.37  tff(c_816, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_807])).
% 2.71/1.37  tff(c_823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_409, c_816])).
% 2.71/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.37  
% 2.71/1.37  Inference rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Ref     : 0
% 2.71/1.37  #Sup     : 165
% 2.71/1.37  #Fact    : 0
% 2.71/1.37  #Define  : 0
% 2.71/1.37  #Split   : 1
% 2.71/1.37  #Chain   : 0
% 2.71/1.37  #Close   : 0
% 2.71/1.37  
% 2.71/1.37  Ordering : KBO
% 2.71/1.37  
% 2.71/1.37  Simplification rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Subsume      : 9
% 2.71/1.37  #Demod        : 215
% 2.71/1.37  #Tautology    : 108
% 2.71/1.37  #SimpNegUnit  : 2
% 2.71/1.37  #BackRed      : 0
% 2.71/1.37  
% 2.71/1.37  #Partial instantiations: 0
% 2.71/1.37  #Strategies tried      : 1
% 2.71/1.37  
% 2.71/1.37  Timing (in seconds)
% 2.71/1.37  ----------------------
% 2.71/1.38  Preprocessing        : 0.29
% 2.71/1.38  Parsing              : 0.16
% 2.71/1.38  CNF conversion       : 0.02
% 2.71/1.38  Main loop            : 0.32
% 2.71/1.38  Inferencing          : 0.12
% 2.71/1.38  Reduction            : 0.10
% 2.71/1.38  Demodulation         : 0.07
% 2.71/1.38  BG Simplification    : 0.02
% 2.71/1.38  Subsumption          : 0.06
% 2.71/1.38  Abstraction          : 0.02
% 2.71/1.38  MUC search           : 0.00
% 2.71/1.38  Cooper               : 0.00
% 2.71/1.38  Total                : 0.64
% 2.71/1.38  Index Insertion      : 0.00
% 2.71/1.38  Index Deletion       : 0.00
% 2.71/1.38  Index Matching       : 0.00
% 2.71/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
