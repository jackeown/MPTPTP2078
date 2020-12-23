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
% DateTime   : Thu Dec  3 10:10:38 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 128 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 233 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_86,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ( r2_hidden(C,A)
           => r2_hidden(k4_tarski(C,C),B) )
       => r1_tarski(k6_relat_1(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_48,plain,(
    ! [A_25] : v1_relat_1(k1_wellord2(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_1'(A_14,B_15),A_14)
      | r1_tarski(k6_relat_1(A_14),B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_44,plain,(
    ! [C_23,D_24,A_17] :
      ( r2_hidden(k4_tarski(C_23,D_24),k1_wellord2(A_17))
      | ~ r1_tarski(C_23,D_24)
      | ~ r2_hidden(D_24,A_17)
      | ~ r2_hidden(C_23,A_17)
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_600,plain,(
    ! [C_90,D_91,A_92] :
      ( r2_hidden(k4_tarski(C_90,D_91),k1_wellord2(A_92))
      | ~ r1_tarski(C_90,D_91)
      | ~ r2_hidden(D_91,A_92)
      | ~ r2_hidden(C_90,A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_14,B_15),'#skF_1'(A_14,B_15)),B_15)
      | r1_tarski(k6_relat_1(A_14),B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_604,plain,(
    ! [A_14,A_92] :
      ( r1_tarski(k6_relat_1(A_14),k1_wellord2(A_92))
      | ~ v1_relat_1(k1_wellord2(A_92))
      | ~ r1_tarski('#skF_1'(A_14,k1_wellord2(A_92)),'#skF_1'(A_14,k1_wellord2(A_92)))
      | ~ r2_hidden('#skF_1'(A_14,k1_wellord2(A_92)),A_92) ) ),
    inference(resolution,[status(thm)],[c_600,c_26])).

tff(c_612,plain,(
    ! [A_93,A_94] :
      ( r1_tarski(k6_relat_1(A_93),k1_wellord2(A_94))
      | ~ r2_hidden('#skF_1'(A_93,k1_wellord2(A_94)),A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_48,c_604])).

tff(c_616,plain,(
    ! [A_14] :
      ( r1_tarski(k6_relat_1(A_14),k1_wellord2(A_14))
      | ~ v1_relat_1(k1_wellord2(A_14)) ) ),
    inference(resolution,[status(thm)],[c_28,c_612])).

tff(c_620,plain,(
    ! [A_95] : r1_tarski(k6_relat_1(A_95),k1_wellord2(A_95)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_616])).

tff(c_14,plain,(
    ! [A_8] : v1_relat_1(k6_relat_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_316,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(k1_relat_1(A_58),k1_relat_1(B_59))
      | ~ r1_tarski(A_58,B_59)
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_321,plain,(
    ! [A_13,B_59] :
      ( r1_tarski(A_13,k1_relat_1(B_59))
      | ~ r1_tarski(k6_relat_1(A_13),B_59)
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_316])).

tff(c_327,plain,(
    ! [A_13,B_59] :
      ( r1_tarski(A_13,k1_relat_1(B_59))
      | ~ r1_tarski(k6_relat_1(A_13),B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_321])).

tff(c_623,plain,(
    ! [A_95] :
      ( r1_tarski(A_95,k1_relat_1(k1_wellord2(A_95)))
      | ~ v1_relat_1(k1_wellord2(A_95)) ) ),
    inference(resolution,[status(thm)],[c_620,c_327])).

tff(c_631,plain,(
    ! [A_95] : r1_tarski(A_95,k1_relat_1(k1_wellord2(A_95))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_623])).

tff(c_42,plain,(
    ! [A_17] :
      ( k3_relat_1(k1_wellord2(A_17)) = A_17
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_56,plain,(
    ! [A_17] : k3_relat_1(k1_wellord2(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42])).

tff(c_170,plain,(
    ! [A_42] :
      ( k2_xboole_0(k1_relat_1(A_42),k2_relat_1(A_42)) = k3_relat_1(A_42)
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_226,plain,(
    ! [A_47] :
      ( r1_tarski(k1_relat_1(A_47),k3_relat_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_10])).

tff(c_237,plain,(
    ! [A_17] :
      ( r1_tarski(k1_relat_1(k1_wellord2(A_17)),A_17)
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_226])).

tff(c_245,plain,(
    ! [A_48] : r1_tarski(k1_relat_1(k1_wellord2(A_48)),A_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_237])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_248,plain,(
    ! [A_48] :
      ( k1_relat_1(k1_wellord2(A_48)) = A_48
      | ~ r1_tarski(A_48,k1_relat_1(k1_wellord2(A_48))) ) ),
    inference(resolution,[status(thm)],[c_245,c_4])).

tff(c_637,plain,(
    ! [A_48] : k1_relat_1(k1_wellord2(A_48)) = A_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_248])).

tff(c_24,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_272,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k2_relat_1(A_51),k2_relat_1(B_52))
      | ~ r1_tarski(A_51,B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_277,plain,(
    ! [A_13,B_52] :
      ( r1_tarski(A_13,k2_relat_1(B_52))
      | ~ r1_tarski(k6_relat_1(A_13),B_52)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_272])).

tff(c_283,plain,(
    ! [A_13,B_52] :
      ( r1_tarski(A_13,k2_relat_1(B_52))
      | ~ r1_tarski(k6_relat_1(A_13),B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_277])).

tff(c_626,plain,(
    ! [A_95] :
      ( r1_tarski(A_95,k2_relat_1(k1_wellord2(A_95)))
      | ~ v1_relat_1(k1_wellord2(A_95)) ) ),
    inference(resolution,[status(thm)],[c_620,c_283])).

tff(c_634,plain,(
    ! [A_95] : r1_tarski(A_95,k2_relat_1(k1_wellord2(A_95))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_626])).

tff(c_89,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_104,plain,(
    ! [A_35,B_34] : r1_tarski(A_35,k2_xboole_0(B_34,A_35)) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_10])).

tff(c_249,plain,(
    ! [A_49] :
      ( r1_tarski(k2_relat_1(A_49),k3_relat_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_104])).

tff(c_260,plain,(
    ! [A_17] :
      ( r1_tarski(k2_relat_1(k1_wellord2(A_17)),A_17)
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_249])).

tff(c_268,plain,(
    ! [A_50] : r1_tarski(k2_relat_1(k1_wellord2(A_50)),A_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_260])).

tff(c_271,plain,(
    ! [A_50] :
      ( k2_relat_1(k1_wellord2(A_50)) = A_50
      | ~ r1_tarski(A_50,k2_relat_1(k1_wellord2(A_50))) ) ),
    inference(resolution,[status(thm)],[c_268,c_4])).

tff(c_753,plain,(
    ! [A_100] : k2_relat_1(k1_wellord2(A_100)) = A_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_271])).

tff(c_16,plain,(
    ! [A_9] :
      ( r1_tarski(A_9,k2_zfmisc_1(k1_relat_1(A_9),k2_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_777,plain,(
    ! [A_100] :
      ( r1_tarski(k1_wellord2(A_100),k2_zfmisc_1(k1_relat_1(k1_wellord2(A_100)),A_100))
      | ~ v1_relat_1(k1_wellord2(A_100)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_16])).

tff(c_795,plain,(
    ! [A_100] : r1_tarski(k1_wellord2(A_100),k2_zfmisc_1(A_100,A_100)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_637,c_777])).

tff(c_50,plain,(
    ~ r1_tarski(k1_wellord2('#skF_4'),k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_795,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.54  
% 2.69/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.54  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k6_relat_1 > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.69/1.54  
% 2.69/1.54  %Foreground sorts:
% 2.69/1.54  
% 2.69/1.54  
% 2.69/1.54  %Background operators:
% 2.69/1.54  
% 2.69/1.54  
% 2.69/1.54  %Foreground operators:
% 2.69/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.69/1.54  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.69/1.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.69/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.54  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.69/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.54  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.69/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.69/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.69/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.69/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.54  
% 2.92/1.56  tff(f_86, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.92/1.56  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: (r2_hidden(C, A) => r2_hidden(k4_tarski(C, C), B))) => r1_tarski(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_relat_1)).
% 2.92/1.56  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.92/1.56  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 2.92/1.56  tff(f_41, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.92/1.56  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.92/1.56  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.92/1.56  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 2.92/1.56  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.92/1.56  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.92/1.56  tff(f_45, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.92/1.56  tff(f_89, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 2.92/1.56  tff(c_48, plain, (![A_25]: (v1_relat_1(k1_wellord2(A_25)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.92/1.56  tff(c_28, plain, (![A_14, B_15]: (r2_hidden('#skF_1'(A_14, B_15), A_14) | r1_tarski(k6_relat_1(A_14), B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.92/1.56  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.92/1.56  tff(c_44, plain, (![C_23, D_24, A_17]: (r2_hidden(k4_tarski(C_23, D_24), k1_wellord2(A_17)) | ~r1_tarski(C_23, D_24) | ~r2_hidden(D_24, A_17) | ~r2_hidden(C_23, A_17) | ~v1_relat_1(k1_wellord2(A_17)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.92/1.56  tff(c_600, plain, (![C_90, D_91, A_92]: (r2_hidden(k4_tarski(C_90, D_91), k1_wellord2(A_92)) | ~r1_tarski(C_90, D_91) | ~r2_hidden(D_91, A_92) | ~r2_hidden(C_90, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44])).
% 2.92/1.56  tff(c_26, plain, (![A_14, B_15]: (~r2_hidden(k4_tarski('#skF_1'(A_14, B_15), '#skF_1'(A_14, B_15)), B_15) | r1_tarski(k6_relat_1(A_14), B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.92/1.56  tff(c_604, plain, (![A_14, A_92]: (r1_tarski(k6_relat_1(A_14), k1_wellord2(A_92)) | ~v1_relat_1(k1_wellord2(A_92)) | ~r1_tarski('#skF_1'(A_14, k1_wellord2(A_92)), '#skF_1'(A_14, k1_wellord2(A_92))) | ~r2_hidden('#skF_1'(A_14, k1_wellord2(A_92)), A_92))), inference(resolution, [status(thm)], [c_600, c_26])).
% 2.92/1.56  tff(c_612, plain, (![A_93, A_94]: (r1_tarski(k6_relat_1(A_93), k1_wellord2(A_94)) | ~r2_hidden('#skF_1'(A_93, k1_wellord2(A_94)), A_94))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_48, c_604])).
% 2.92/1.56  tff(c_616, plain, (![A_14]: (r1_tarski(k6_relat_1(A_14), k1_wellord2(A_14)) | ~v1_relat_1(k1_wellord2(A_14)))), inference(resolution, [status(thm)], [c_28, c_612])).
% 2.92/1.56  tff(c_620, plain, (![A_95]: (r1_tarski(k6_relat_1(A_95), k1_wellord2(A_95)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_616])).
% 2.92/1.56  tff(c_14, plain, (![A_8]: (v1_relat_1(k6_relat_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.92/1.56  tff(c_22, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.92/1.56  tff(c_316, plain, (![A_58, B_59]: (r1_tarski(k1_relat_1(A_58), k1_relat_1(B_59)) | ~r1_tarski(A_58, B_59) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.92/1.56  tff(c_321, plain, (![A_13, B_59]: (r1_tarski(A_13, k1_relat_1(B_59)) | ~r1_tarski(k6_relat_1(A_13), B_59) | ~v1_relat_1(B_59) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_316])).
% 2.92/1.56  tff(c_327, plain, (![A_13, B_59]: (r1_tarski(A_13, k1_relat_1(B_59)) | ~r1_tarski(k6_relat_1(A_13), B_59) | ~v1_relat_1(B_59))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_321])).
% 2.92/1.56  tff(c_623, plain, (![A_95]: (r1_tarski(A_95, k1_relat_1(k1_wellord2(A_95))) | ~v1_relat_1(k1_wellord2(A_95)))), inference(resolution, [status(thm)], [c_620, c_327])).
% 2.92/1.56  tff(c_631, plain, (![A_95]: (r1_tarski(A_95, k1_relat_1(k1_wellord2(A_95))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_623])).
% 2.92/1.56  tff(c_42, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17 | ~v1_relat_1(k1_wellord2(A_17)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.92/1.56  tff(c_56, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42])).
% 2.92/1.56  tff(c_170, plain, (![A_42]: (k2_xboole_0(k1_relat_1(A_42), k2_relat_1(A_42))=k3_relat_1(A_42) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.92/1.56  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.92/1.56  tff(c_226, plain, (![A_47]: (r1_tarski(k1_relat_1(A_47), k3_relat_1(A_47)) | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_170, c_10])).
% 2.92/1.56  tff(c_237, plain, (![A_17]: (r1_tarski(k1_relat_1(k1_wellord2(A_17)), A_17) | ~v1_relat_1(k1_wellord2(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_226])).
% 2.92/1.56  tff(c_245, plain, (![A_48]: (r1_tarski(k1_relat_1(k1_wellord2(A_48)), A_48))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_237])).
% 2.92/1.56  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.92/1.56  tff(c_248, plain, (![A_48]: (k1_relat_1(k1_wellord2(A_48))=A_48 | ~r1_tarski(A_48, k1_relat_1(k1_wellord2(A_48))))), inference(resolution, [status(thm)], [c_245, c_4])).
% 2.92/1.56  tff(c_637, plain, (![A_48]: (k1_relat_1(k1_wellord2(A_48))=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_631, c_248])).
% 2.92/1.56  tff(c_24, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.92/1.56  tff(c_272, plain, (![A_51, B_52]: (r1_tarski(k2_relat_1(A_51), k2_relat_1(B_52)) | ~r1_tarski(A_51, B_52) | ~v1_relat_1(B_52) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.92/1.56  tff(c_277, plain, (![A_13, B_52]: (r1_tarski(A_13, k2_relat_1(B_52)) | ~r1_tarski(k6_relat_1(A_13), B_52) | ~v1_relat_1(B_52) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_272])).
% 2.92/1.56  tff(c_283, plain, (![A_13, B_52]: (r1_tarski(A_13, k2_relat_1(B_52)) | ~r1_tarski(k6_relat_1(A_13), B_52) | ~v1_relat_1(B_52))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_277])).
% 2.92/1.56  tff(c_626, plain, (![A_95]: (r1_tarski(A_95, k2_relat_1(k1_wellord2(A_95))) | ~v1_relat_1(k1_wellord2(A_95)))), inference(resolution, [status(thm)], [c_620, c_283])).
% 2.92/1.56  tff(c_634, plain, (![A_95]: (r1_tarski(A_95, k2_relat_1(k1_wellord2(A_95))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_626])).
% 2.92/1.56  tff(c_89, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.92/1.56  tff(c_104, plain, (![A_35, B_34]: (r1_tarski(A_35, k2_xboole_0(B_34, A_35)))), inference(superposition, [status(thm), theory('equality')], [c_89, c_10])).
% 2.92/1.56  tff(c_249, plain, (![A_49]: (r1_tarski(k2_relat_1(A_49), k3_relat_1(A_49)) | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_170, c_104])).
% 2.92/1.56  tff(c_260, plain, (![A_17]: (r1_tarski(k2_relat_1(k1_wellord2(A_17)), A_17) | ~v1_relat_1(k1_wellord2(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_249])).
% 2.92/1.56  tff(c_268, plain, (![A_50]: (r1_tarski(k2_relat_1(k1_wellord2(A_50)), A_50))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_260])).
% 2.92/1.56  tff(c_271, plain, (![A_50]: (k2_relat_1(k1_wellord2(A_50))=A_50 | ~r1_tarski(A_50, k2_relat_1(k1_wellord2(A_50))))), inference(resolution, [status(thm)], [c_268, c_4])).
% 2.92/1.56  tff(c_753, plain, (![A_100]: (k2_relat_1(k1_wellord2(A_100))=A_100)), inference(demodulation, [status(thm), theory('equality')], [c_634, c_271])).
% 2.92/1.56  tff(c_16, plain, (![A_9]: (r1_tarski(A_9, k2_zfmisc_1(k1_relat_1(A_9), k2_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.92/1.56  tff(c_777, plain, (![A_100]: (r1_tarski(k1_wellord2(A_100), k2_zfmisc_1(k1_relat_1(k1_wellord2(A_100)), A_100)) | ~v1_relat_1(k1_wellord2(A_100)))), inference(superposition, [status(thm), theory('equality')], [c_753, c_16])).
% 2.92/1.56  tff(c_795, plain, (![A_100]: (r1_tarski(k1_wellord2(A_100), k2_zfmisc_1(A_100, A_100)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_637, c_777])).
% 2.92/1.56  tff(c_50, plain, (~r1_tarski(k1_wellord2('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.92/1.56  tff(c_949, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_795, c_50])).
% 2.92/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.56  
% 2.92/1.56  Inference rules
% 2.92/1.56  ----------------------
% 2.92/1.56  #Ref     : 0
% 2.92/1.56  #Sup     : 180
% 2.92/1.56  #Fact    : 0
% 2.92/1.56  #Define  : 0
% 2.92/1.56  #Split   : 0
% 2.92/1.56  #Chain   : 0
% 2.92/1.56  #Close   : 0
% 2.92/1.56  
% 2.92/1.56  Ordering : KBO
% 2.92/1.56  
% 2.92/1.56  Simplification rules
% 2.92/1.56  ----------------------
% 2.92/1.56  #Subsume      : 23
% 2.92/1.56  #Demod        : 244
% 2.92/1.56  #Tautology    : 80
% 2.92/1.56  #SimpNegUnit  : 0
% 2.92/1.56  #BackRed      : 10
% 2.92/1.56  
% 2.92/1.56  #Partial instantiations: 0
% 2.92/1.56  #Strategies tried      : 1
% 2.92/1.56  
% 2.92/1.56  Timing (in seconds)
% 2.92/1.56  ----------------------
% 2.96/1.56  Preprocessing        : 0.30
% 2.96/1.56  Parsing              : 0.15
% 2.96/1.56  CNF conversion       : 0.02
% 2.96/1.56  Main loop            : 0.37
% 2.96/1.56  Inferencing          : 0.12
% 2.96/1.56  Reduction            : 0.14
% 2.96/1.56  Demodulation         : 0.11
% 2.96/1.56  BG Simplification    : 0.02
% 2.96/1.56  Subsumption          : 0.06
% 2.96/1.56  Abstraction          : 0.02
% 2.96/1.56  MUC search           : 0.00
% 2.96/1.56  Cooper               : 0.00
% 2.96/1.56  Total                : 0.70
% 2.96/1.56  Index Insertion      : 0.00
% 2.96/1.56  Index Deletion       : 0.00
% 2.96/1.56  Index Matching       : 0.00
% 2.96/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
