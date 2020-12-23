%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:18 EST 2020

% Result     : Theorem 10.22s
% Output     : CNFRefutation 10.37s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 132 expanded)
%              Number of leaves         :   37 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 289 expanded)
%              Number of equality atoms :   42 ( 198 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_92,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_68,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_97,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_66,plain,
    ( k1_xboole_0 != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_81,plain,(
    k1_tarski('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_99,plain,(
    ! [A_67,B_68] : r1_tarski(A_67,k2_xboole_0(A_67,B_68)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_102,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_99])).

tff(c_1392,plain,(
    ! [B_184,A_185] :
      ( k1_tarski(B_184) = A_185
      | k1_xboole_0 = A_185
      | ~ r1_tarski(A_185,k1_tarski(B_184)) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1411,plain,
    ( k1_tarski('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_102,c_1392])).

tff(c_1426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_81,c_1411])).

tff(c_1427,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_18,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1428,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_22,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1431,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1428,c_1428,c_22])).

tff(c_1578,plain,(
    ! [B_217,A_218] :
      ( ~ r1_xboole_0(B_217,A_218)
      | ~ r1_tarski(B_217,A_218)
      | v1_xboole_0(B_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1587,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1431,c_1578])).

tff(c_1594,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1587])).

tff(c_1977,plain,(
    ! [A_270,B_271] :
      ( r2_hidden('#skF_2'(A_270,B_271),A_270)
      | r1_tarski(A_270,B_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1988,plain,(
    ! [A_272,B_273] :
      ( ~ v1_xboole_0(A_272)
      | r1_tarski(A_272,B_273) ) ),
    inference(resolution,[status(thm)],[c_1977,c_2])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2020,plain,(
    ! [A_274,B_275] :
      ( k2_xboole_0(A_274,B_275) = B_275
      | ~ v1_xboole_0(A_274) ) ),
    inference(resolution,[status(thm)],[c_1988,c_20])).

tff(c_2023,plain,(
    ! [B_275] : k2_xboole_0('#skF_4',B_275) = B_275 ),
    inference(resolution,[status(thm)],[c_1594,c_2020])).

tff(c_2025,plain,(
    k1_tarski('#skF_3') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2023,c_72])).

tff(c_2027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1427,c_2025])).

tff(c_2029,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_70,plain,
    ( k1_tarski('#skF_3') != '#skF_5'
    | k1_tarski('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2064,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2029,c_2029,c_70])).

tff(c_2031,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2029,c_72])).

tff(c_2222,plain,(
    ! [A_296,B_297] :
      ( r1_xboole_0(k1_tarski(A_296),B_297)
      | r2_hidden(A_296,B_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2231,plain,(
    ! [B_297] :
      ( r1_xboole_0('#skF_4',B_297)
      | r2_hidden('#skF_3',B_297) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2029,c_2222])).

tff(c_36,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4672,plain,(
    ! [A_458,B_459,C_460] :
      ( r1_tarski(k2_tarski(A_458,B_459),C_460)
      | ~ r2_hidden(B_459,C_460)
      | ~ r2_hidden(A_458,C_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_46176,plain,(
    ! [A_39847,C_39848] :
      ( r1_tarski(k1_tarski(A_39847),C_39848)
      | ~ r2_hidden(A_39847,C_39848)
      | ~ r2_hidden(A_39847,C_39848) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4672])).

tff(c_47014,plain,(
    ! [C_40860] :
      ( r1_tarski('#skF_4',C_40860)
      | ~ r2_hidden('#skF_3',C_40860)
      | ~ r2_hidden('#skF_3',C_40860) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2029,c_46176])).

tff(c_52985,plain,(
    ! [B_43141] :
      ( r1_tarski('#skF_4',B_43141)
      | ~ r2_hidden('#skF_3',B_43141)
      | r1_xboole_0('#skF_4',B_43141) ) ),
    inference(resolution,[status(thm)],[c_2231,c_47014])).

tff(c_53306,plain,(
    ! [B_43394] :
      ( r1_tarski('#skF_4',B_43394)
      | r1_xboole_0('#skF_4',B_43394) ) ),
    inference(resolution,[status(thm)],[c_2231,c_52985])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_xboole_0(B_11,A_10)
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53547,plain,(
    ! [B_43647] :
      ( r1_xboole_0(B_43647,'#skF_4')
      | r1_tarski('#skF_4',B_43647) ) ),
    inference(resolution,[status(thm)],[c_53306,c_12])).

tff(c_2028,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2297,plain,(
    ! [A_306,C_307,B_308] :
      ( r1_xboole_0(A_306,C_307)
      | ~ r1_xboole_0(A_306,k2_xboole_0(B_308,C_307)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2320,plain,(
    ! [A_309] :
      ( r1_xboole_0(A_309,'#skF_5')
      | ~ r1_xboole_0(A_309,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2031,c_2297])).

tff(c_24,plain,(
    ! [A_16] :
      ( ~ r1_xboole_0(A_16,A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2326,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2320,c_24])).

tff(c_2330,plain,(
    ~ r1_xboole_0('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_2028,c_2326])).

tff(c_53766,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_53547,c_2330])).

tff(c_53798,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_53766,c_20])).

tff(c_54029,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2031,c_53798])).

tff(c_54031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2064,c_54029])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.22/4.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.22/4.12  
% 10.22/4.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.22/4.12  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 10.22/4.12  
% 10.22/4.12  %Foreground sorts:
% 10.22/4.12  
% 10.22/4.12  
% 10.22/4.12  %Background operators:
% 10.22/4.12  
% 10.22/4.12  
% 10.22/4.12  %Foreground operators:
% 10.22/4.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.22/4.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.22/4.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.22/4.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.22/4.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.22/4.12  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.22/4.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.22/4.12  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.22/4.12  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.22/4.12  tff('#skF_5', type, '#skF_5': $i).
% 10.22/4.12  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.22/4.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.22/4.12  tff('#skF_3', type, '#skF_3': $i).
% 10.22/4.12  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.22/4.12  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.22/4.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.22/4.12  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.22/4.12  tff('#skF_4', type, '#skF_4': $i).
% 10.22/4.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.22/4.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.22/4.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.22/4.12  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.22/4.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.22/4.12  
% 10.37/4.13  tff(f_142, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 10.37/4.13  tff(f_90, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.37/4.13  tff(f_115, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 10.37/4.13  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.37/4.13  tff(f_64, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 10.37/4.13  tff(f_72, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 10.37/4.13  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 10.37/4.13  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.37/4.13  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.37/4.13  tff(f_109, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 10.37/4.13  tff(f_92, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 10.37/4.13  tff(f_123, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 10.37/4.13  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 10.37/4.13  tff(f_88, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 10.37/4.13  tff(c_68, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.37/4.13  tff(c_97, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_68])).
% 10.37/4.13  tff(c_66, plain, (k1_xboole_0!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.37/4.13  tff(c_81, plain, (k1_tarski('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_66])).
% 10.37/4.13  tff(c_72, plain, (k2_xboole_0('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.37/4.13  tff(c_99, plain, (![A_67, B_68]: (r1_tarski(A_67, k2_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.37/4.13  tff(c_102, plain, (r1_tarski('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_99])).
% 10.37/4.13  tff(c_1392, plain, (![B_184, A_185]: (k1_tarski(B_184)=A_185 | k1_xboole_0=A_185 | ~r1_tarski(A_185, k1_tarski(B_184)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 10.37/4.13  tff(c_1411, plain, (k1_tarski('#skF_3')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_102, c_1392])).
% 10.37/4.13  tff(c_1426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_81, c_1411])).
% 10.37/4.13  tff(c_1427, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_68])).
% 10.37/4.13  tff(c_18, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.37/4.13  tff(c_1428, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_68])).
% 10.37/4.13  tff(c_22, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.37/4.13  tff(c_1431, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1428, c_1428, c_22])).
% 10.37/4.13  tff(c_1578, plain, (![B_217, A_218]: (~r1_xboole_0(B_217, A_218) | ~r1_tarski(B_217, A_218) | v1_xboole_0(B_217))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.37/4.13  tff(c_1587, plain, (~r1_tarski('#skF_4', '#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1431, c_1578])).
% 10.37/4.13  tff(c_1594, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1587])).
% 10.37/4.13  tff(c_1977, plain, (![A_270, B_271]: (r2_hidden('#skF_2'(A_270, B_271), A_270) | r1_tarski(A_270, B_271))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.37/4.13  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.37/4.13  tff(c_1988, plain, (![A_272, B_273]: (~v1_xboole_0(A_272) | r1_tarski(A_272, B_273))), inference(resolution, [status(thm)], [c_1977, c_2])).
% 10.37/4.13  tff(c_20, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.37/4.13  tff(c_2020, plain, (![A_274, B_275]: (k2_xboole_0(A_274, B_275)=B_275 | ~v1_xboole_0(A_274))), inference(resolution, [status(thm)], [c_1988, c_20])).
% 10.37/4.13  tff(c_2023, plain, (![B_275]: (k2_xboole_0('#skF_4', B_275)=B_275)), inference(resolution, [status(thm)], [c_1594, c_2020])).
% 10.37/4.13  tff(c_2025, plain, (k1_tarski('#skF_3')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2023, c_72])).
% 10.37/4.13  tff(c_2027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1427, c_2025])).
% 10.37/4.13  tff(c_2029, plain, (k1_tarski('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_66])).
% 10.37/4.13  tff(c_70, plain, (k1_tarski('#skF_3')!='#skF_5' | k1_tarski('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.37/4.13  tff(c_2064, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2029, c_2029, c_70])).
% 10.37/4.13  tff(c_2031, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2029, c_72])).
% 10.37/4.13  tff(c_2222, plain, (![A_296, B_297]: (r1_xboole_0(k1_tarski(A_296), B_297) | r2_hidden(A_296, B_297))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.37/4.13  tff(c_2231, plain, (![B_297]: (r1_xboole_0('#skF_4', B_297) | r2_hidden('#skF_3', B_297))), inference(superposition, [status(thm), theory('equality')], [c_2029, c_2222])).
% 10.37/4.13  tff(c_36, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.37/4.13  tff(c_4672, plain, (![A_458, B_459, C_460]: (r1_tarski(k2_tarski(A_458, B_459), C_460) | ~r2_hidden(B_459, C_460) | ~r2_hidden(A_458, C_460))), inference(cnfTransformation, [status(thm)], [f_123])).
% 10.37/4.13  tff(c_46176, plain, (![A_39847, C_39848]: (r1_tarski(k1_tarski(A_39847), C_39848) | ~r2_hidden(A_39847, C_39848) | ~r2_hidden(A_39847, C_39848))), inference(superposition, [status(thm), theory('equality')], [c_36, c_4672])).
% 10.37/4.13  tff(c_47014, plain, (![C_40860]: (r1_tarski('#skF_4', C_40860) | ~r2_hidden('#skF_3', C_40860) | ~r2_hidden('#skF_3', C_40860))), inference(superposition, [status(thm), theory('equality')], [c_2029, c_46176])).
% 10.37/4.13  tff(c_52985, plain, (![B_43141]: (r1_tarski('#skF_4', B_43141) | ~r2_hidden('#skF_3', B_43141) | r1_xboole_0('#skF_4', B_43141))), inference(resolution, [status(thm)], [c_2231, c_47014])).
% 10.37/4.13  tff(c_53306, plain, (![B_43394]: (r1_tarski('#skF_4', B_43394) | r1_xboole_0('#skF_4', B_43394))), inference(resolution, [status(thm)], [c_2231, c_52985])).
% 10.37/4.13  tff(c_12, plain, (![B_11, A_10]: (r1_xboole_0(B_11, A_10) | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.37/4.13  tff(c_53547, plain, (![B_43647]: (r1_xboole_0(B_43647, '#skF_4') | r1_tarski('#skF_4', B_43647))), inference(resolution, [status(thm)], [c_53306, c_12])).
% 10.37/4.13  tff(c_2028, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_66])).
% 10.37/4.13  tff(c_2297, plain, (![A_306, C_307, B_308]: (r1_xboole_0(A_306, C_307) | ~r1_xboole_0(A_306, k2_xboole_0(B_308, C_307)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.37/4.14  tff(c_2320, plain, (![A_309]: (r1_xboole_0(A_309, '#skF_5') | ~r1_xboole_0(A_309, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2031, c_2297])).
% 10.37/4.14  tff(c_24, plain, (![A_16]: (~r1_xboole_0(A_16, A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.37/4.14  tff(c_2326, plain, (k1_xboole_0='#skF_5' | ~r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2320, c_24])).
% 10.37/4.14  tff(c_2330, plain, (~r1_xboole_0('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_2028, c_2326])).
% 10.37/4.14  tff(c_53766, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_53547, c_2330])).
% 10.37/4.14  tff(c_53798, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_53766, c_20])).
% 10.37/4.14  tff(c_54029, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2031, c_53798])).
% 10.37/4.14  tff(c_54031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2064, c_54029])).
% 10.37/4.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.37/4.14  
% 10.37/4.14  Inference rules
% 10.37/4.14  ----------------------
% 10.37/4.14  #Ref     : 0
% 10.37/4.14  #Sup     : 6919
% 10.37/4.14  #Fact    : 6
% 10.37/4.14  #Define  : 0
% 10.37/4.14  #Split   : 10
% 10.37/4.14  #Chain   : 0
% 10.37/4.14  #Close   : 0
% 10.37/4.14  
% 10.37/4.14  Ordering : KBO
% 10.37/4.14  
% 10.37/4.14  Simplification rules
% 10.37/4.14  ----------------------
% 10.37/4.14  #Subsume      : 3904
% 10.37/4.14  #Demod        : 2933
% 10.37/4.14  #Tautology    : 1895
% 10.37/4.14  #SimpNegUnit  : 98
% 10.37/4.14  #BackRed      : 23
% 10.37/4.14  
% 10.37/4.14  #Partial instantiations: 16576
% 10.37/4.14  #Strategies tried      : 1
% 10.37/4.14  
% 10.37/4.14  Timing (in seconds)
% 10.37/4.14  ----------------------
% 10.37/4.14  Preprocessing        : 0.30
% 10.37/4.14  Parsing              : 0.15
% 10.37/4.14  CNF conversion       : 0.02
% 10.37/4.14  Main loop            : 2.91
% 10.37/4.14  Inferencing          : 1.00
% 10.37/4.14  Reduction            : 0.99
% 10.37/4.14  Demodulation         : 0.73
% 10.37/4.14  BG Simplification    : 0.07
% 10.37/4.14  Subsumption          : 0.74
% 10.37/4.14  Abstraction          : 0.11
% 10.37/4.14  MUC search           : 0.00
% 10.37/4.14  Cooper               : 0.00
% 10.37/4.14  Total                : 3.25
% 10.37/4.14  Index Insertion      : 0.00
% 10.37/4.14  Index Deletion       : 0.00
% 10.37/4.14  Index Matching       : 0.00
% 10.37/4.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
