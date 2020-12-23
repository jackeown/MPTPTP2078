%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:04 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 110 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  122 ( 190 expanded)
%              Number of equality atoms :   37 (  56 expanded)
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

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_81,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_32,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_57,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_52,plain,(
    ! [A_22] :
      ( v1_relat_1(A_22)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_56,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k5_relat_1(A_10,B_11))
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_67,plain,(
    ! [A_25,B_26] :
      ( v1_xboole_0(k2_zfmisc_1(A_25,B_26))
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_130,plain,(
    ! [A_35,B_36] :
      ( k2_zfmisc_1(A_35,B_36) = k1_xboole_0
      | ~ v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_67,c_4])).

tff(c_139,plain,(
    ! [B_36] : k2_zfmisc_1(k1_xboole_0,B_36) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_130])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_517,plain,(
    ! [A_58,B_59] :
      ( k1_relat_1(k5_relat_1(A_58,B_59)) = k1_relat_1(A_58)
      | ~ r1_tarski(k2_relat_1(A_58),k1_relat_1(B_59))
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_526,plain,(
    ! [B_59] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_59)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_59))
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_517])).

tff(c_533,plain,(
    ! [B_60] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_60)) = k1_xboole_0
      | ~ v1_relat_1(B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12,c_30,c_526])).

tff(c_22,plain,(
    ! [A_12] :
      ( r1_tarski(A_12,k2_zfmisc_1(k1_relat_1(A_12),k2_relat_1(A_12)))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_545,plain,(
    ! [B_60] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,B_60),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_60))))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_60))
      | ~ v1_relat_1(B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_22])).

tff(c_801,plain,(
    ! [B_71] :
      ( r1_tarski(k5_relat_1(k1_xboole_0,B_71),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_71))
      | ~ v1_relat_1(B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_545])).

tff(c_102,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_111,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_102])).

tff(c_816,plain,(
    ! [B_72] :
      ( k5_relat_1(k1_xboole_0,B_72) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_72))
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_801,c_111])).

tff(c_823,plain,(
    ! [B_11] :
      ( k5_relat_1(k1_xboole_0,B_11) = k1_xboole_0
      | ~ v1_relat_1(B_11)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_816])).

tff(c_829,plain,(
    ! [B_73] :
      ( k5_relat_1(k1_xboole_0,B_73) = k1_xboole_0
      | ~ v1_relat_1(B_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_823])).

tff(c_844,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_829])).

tff(c_853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_844])).

tff(c_854,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_869,plain,(
    ! [A_76,B_77] :
      ( v1_xboole_0(k2_zfmisc_1(A_76,B_77))
      | ~ v1_xboole_0(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_932,plain,(
    ! [A_86,B_87] :
      ( k2_zfmisc_1(A_86,B_87) = k1_xboole_0
      | ~ v1_xboole_0(B_87) ) ),
    inference(resolution,[status(thm)],[c_869,c_4])).

tff(c_941,plain,(
    ! [A_86] : k2_zfmisc_1(A_86,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_932])).

tff(c_1344,plain,(
    ! [B_110,A_111] :
      ( k2_relat_1(k5_relat_1(B_110,A_111)) = k2_relat_1(A_111)
      | ~ r1_tarski(k1_relat_1(A_111),k2_relat_1(B_110))
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1350,plain,(
    ! [B_110] :
      ( k2_relat_1(k5_relat_1(B_110,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_110))
      | ~ v1_relat_1(B_110)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1344])).

tff(c_1360,plain,(
    ! [B_112] :
      ( k2_relat_1(k5_relat_1(B_112,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12,c_28,c_1350])).

tff(c_1372,plain,(
    ! [B_112] :
      ( r1_tarski(k5_relat_1(B_112,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_112,k1_xboole_0)),k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(B_112,k1_xboole_0))
      | ~ v1_relat_1(B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1360,c_22])).

tff(c_1606,plain,(
    ! [B_122] :
      ( r1_tarski(k5_relat_1(B_122,k1_xboole_0),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_122,k1_xboole_0))
      | ~ v1_relat_1(B_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_941,c_1372])).

tff(c_888,plain,(
    ! [B_80,A_81] :
      ( B_80 = A_81
      | ~ r1_tarski(B_80,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_897,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_888])).

tff(c_1621,plain,(
    ! [B_123] :
      ( k5_relat_1(B_123,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_123,k1_xboole_0))
      | ~ v1_relat_1(B_123) ) ),
    inference(resolution,[status(thm)],[c_1606,c_897])).

tff(c_1628,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_20,c_1621])).

tff(c_1634,plain,(
    ! [A_124] :
      ( k5_relat_1(A_124,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1628])).

tff(c_1649,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_1634])).

tff(c_1658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_854,c_1649])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.51  
% 3.22/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.51  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.22/1.51  
% 3.22/1.51  %Foreground sorts:
% 3.22/1.51  
% 3.22/1.51  
% 3.22/1.51  %Background operators:
% 3.22/1.51  
% 3.22/1.51  
% 3.22/1.51  %Foreground operators:
% 3.22/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.22/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.22/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.22/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.22/1.51  
% 3.38/1.53  tff(f_88, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.38/1.53  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.38/1.53  tff(f_50, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.38/1.53  tff(f_56, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.38/1.53  tff(f_46, axiom, (![A, B]: (v1_xboole_0(A) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_zfmisc_1)).
% 3.38/1.53  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.38/1.53  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.38/1.53  tff(f_81, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.38/1.53  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.38/1.53  tff(f_60, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.38/1.53  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.38/1.53  tff(f_42, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 3.38/1.53  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.38/1.53  tff(c_32, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.38/1.53  tff(c_57, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 3.38/1.53  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.38/1.53  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.38/1.53  tff(c_52, plain, (![A_22]: (v1_relat_1(A_22) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.38/1.53  tff(c_56, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_52])).
% 3.38/1.53  tff(c_20, plain, (![A_10, B_11]: (v1_relat_1(k5_relat_1(A_10, B_11)) | ~v1_relat_1(B_11) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.53  tff(c_67, plain, (![A_25, B_26]: (v1_xboole_0(k2_zfmisc_1(A_25, B_26)) | ~v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.38/1.53  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.38/1.53  tff(c_130, plain, (![A_35, B_36]: (k2_zfmisc_1(A_35, B_36)=k1_xboole_0 | ~v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_67, c_4])).
% 3.38/1.53  tff(c_139, plain, (![B_36]: (k2_zfmisc_1(k1_xboole_0, B_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_130])).
% 3.38/1.53  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.38/1.53  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.38/1.53  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.38/1.53  tff(c_517, plain, (![A_58, B_59]: (k1_relat_1(k5_relat_1(A_58, B_59))=k1_relat_1(A_58) | ~r1_tarski(k2_relat_1(A_58), k1_relat_1(B_59)) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.38/1.53  tff(c_526, plain, (![B_59]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_59))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_59)) | ~v1_relat_1(B_59) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_517])).
% 3.38/1.53  tff(c_533, plain, (![B_60]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_60))=k1_xboole_0 | ~v1_relat_1(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12, c_30, c_526])).
% 3.38/1.53  tff(c_22, plain, (![A_12]: (r1_tarski(A_12, k2_zfmisc_1(k1_relat_1(A_12), k2_relat_1(A_12))) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.38/1.53  tff(c_545, plain, (![B_60]: (r1_tarski(k5_relat_1(k1_xboole_0, B_60), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_60)))) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_60)) | ~v1_relat_1(B_60))), inference(superposition, [status(thm), theory('equality')], [c_533, c_22])).
% 3.38/1.53  tff(c_801, plain, (![B_71]: (r1_tarski(k5_relat_1(k1_xboole_0, B_71), k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_71)) | ~v1_relat_1(B_71))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_545])).
% 3.38/1.53  tff(c_102, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.38/1.53  tff(c_111, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_102])).
% 3.38/1.53  tff(c_816, plain, (![B_72]: (k5_relat_1(k1_xboole_0, B_72)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_72)) | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_801, c_111])).
% 3.38/1.53  tff(c_823, plain, (![B_11]: (k5_relat_1(k1_xboole_0, B_11)=k1_xboole_0 | ~v1_relat_1(B_11) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_816])).
% 3.38/1.53  tff(c_829, plain, (![B_73]: (k5_relat_1(k1_xboole_0, B_73)=k1_xboole_0 | ~v1_relat_1(B_73))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_823])).
% 3.38/1.53  tff(c_844, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_829])).
% 3.38/1.53  tff(c_853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_844])).
% 3.38/1.53  tff(c_854, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 3.38/1.53  tff(c_869, plain, (![A_76, B_77]: (v1_xboole_0(k2_zfmisc_1(A_76, B_77)) | ~v1_xboole_0(B_77))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.38/1.53  tff(c_932, plain, (![A_86, B_87]: (k2_zfmisc_1(A_86, B_87)=k1_xboole_0 | ~v1_xboole_0(B_87))), inference(resolution, [status(thm)], [c_869, c_4])).
% 3.38/1.53  tff(c_941, plain, (![A_86]: (k2_zfmisc_1(A_86, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_932])).
% 3.38/1.53  tff(c_1344, plain, (![B_110, A_111]: (k2_relat_1(k5_relat_1(B_110, A_111))=k2_relat_1(A_111) | ~r1_tarski(k1_relat_1(A_111), k2_relat_1(B_110)) | ~v1_relat_1(B_110) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.38/1.53  tff(c_1350, plain, (![B_110]: (k2_relat_1(k5_relat_1(B_110, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_110)) | ~v1_relat_1(B_110) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1344])).
% 3.38/1.53  tff(c_1360, plain, (![B_112]: (k2_relat_1(k5_relat_1(B_112, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_12, c_28, c_1350])).
% 3.38/1.53  tff(c_1372, plain, (![B_112]: (r1_tarski(k5_relat_1(B_112, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_112, k1_xboole_0)), k1_xboole_0)) | ~v1_relat_1(k5_relat_1(B_112, k1_xboole_0)) | ~v1_relat_1(B_112))), inference(superposition, [status(thm), theory('equality')], [c_1360, c_22])).
% 3.38/1.53  tff(c_1606, plain, (![B_122]: (r1_tarski(k5_relat_1(B_122, k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_122, k1_xboole_0)) | ~v1_relat_1(B_122))), inference(demodulation, [status(thm), theory('equality')], [c_941, c_1372])).
% 3.38/1.53  tff(c_888, plain, (![B_80, A_81]: (B_80=A_81 | ~r1_tarski(B_80, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.38/1.53  tff(c_897, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_888])).
% 3.38/1.53  tff(c_1621, plain, (![B_123]: (k5_relat_1(B_123, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_123, k1_xboole_0)) | ~v1_relat_1(B_123))), inference(resolution, [status(thm)], [c_1606, c_897])).
% 3.38/1.53  tff(c_1628, plain, (![A_10]: (k5_relat_1(A_10, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_20, c_1621])).
% 3.38/1.53  tff(c_1634, plain, (![A_124]: (k5_relat_1(A_124, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1628])).
% 3.38/1.53  tff(c_1649, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_1634])).
% 3.38/1.53  tff(c_1658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_854, c_1649])).
% 3.38/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.53  
% 3.38/1.53  Inference rules
% 3.38/1.53  ----------------------
% 3.38/1.53  #Ref     : 0
% 3.38/1.53  #Sup     : 373
% 3.38/1.53  #Fact    : 0
% 3.38/1.53  #Define  : 0
% 3.38/1.53  #Split   : 1
% 3.38/1.53  #Chain   : 0
% 3.38/1.53  #Close   : 0
% 3.38/1.53  
% 3.38/1.53  Ordering : KBO
% 3.38/1.53  
% 3.38/1.53  Simplification rules
% 3.38/1.53  ----------------------
% 3.38/1.53  #Subsume      : 6
% 3.38/1.53  #Demod        : 315
% 3.38/1.53  #Tautology    : 296
% 3.38/1.53  #SimpNegUnit  : 2
% 3.38/1.53  #BackRed      : 0
% 3.38/1.53  
% 3.38/1.53  #Partial instantiations: 0
% 3.38/1.53  #Strategies tried      : 1
% 3.38/1.53  
% 3.38/1.53  Timing (in seconds)
% 3.38/1.53  ----------------------
% 3.38/1.53  Preprocessing        : 0.30
% 3.38/1.53  Parsing              : 0.17
% 3.38/1.53  CNF conversion       : 0.02
% 3.38/1.53  Main loop            : 0.44
% 3.38/1.53  Inferencing          : 0.17
% 3.38/1.53  Reduction            : 0.13
% 3.38/1.53  Demodulation         : 0.09
% 3.38/1.53  BG Simplification    : 0.02
% 3.38/1.53  Subsumption          : 0.09
% 3.38/1.53  Abstraction          : 0.02
% 3.42/1.53  MUC search           : 0.00
% 3.42/1.53  Cooper               : 0.00
% 3.42/1.53  Total                : 0.78
% 3.42/1.53  Index Insertion      : 0.00
% 3.42/1.53  Index Deletion       : 0.00
% 3.42/1.53  Index Matching       : 0.00
% 3.42/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
