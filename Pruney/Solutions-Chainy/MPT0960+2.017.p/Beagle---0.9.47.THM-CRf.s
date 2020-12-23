%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:39 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 175 expanded)
%              Number of leaves         :   34 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  123 ( 335 expanded)
%              Number of equality atoms :   22 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_94,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ( r2_hidden(C,A)
           => r2_hidden(k4_tarski(C,C),B) )
       => r1_tarski(k6_relat_1(A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_54,plain,(
    ! [A_29] : v1_relat_1(k1_wellord2(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( r2_hidden('#skF_1'(A_17,B_18),A_17)
      | r1_tarski(k6_relat_1(A_17),B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [C_27,D_28,A_21] :
      ( r2_hidden(k4_tarski(C_27,D_28),k1_wellord2(A_21))
      | ~ r1_tarski(C_27,D_28)
      | ~ r2_hidden(D_28,A_21)
      | ~ r2_hidden(C_27,A_21)
      | ~ v1_relat_1(k1_wellord2(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_667,plain,(
    ! [C_97,D_98,A_99] :
      ( r2_hidden(k4_tarski(C_97,D_98),k1_wellord2(A_99))
      | ~ r1_tarski(C_97,D_98)
      | ~ r2_hidden(D_98,A_99)
      | ~ r2_hidden(C_97,A_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_17,B_18),'#skF_1'(A_17,B_18)),B_18)
      | r1_tarski(k6_relat_1(A_17),B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_671,plain,(
    ! [A_17,A_99] :
      ( r1_tarski(k6_relat_1(A_17),k1_wellord2(A_99))
      | ~ v1_relat_1(k1_wellord2(A_99))
      | ~ r1_tarski('#skF_1'(A_17,k1_wellord2(A_99)),'#skF_1'(A_17,k1_wellord2(A_99)))
      | ~ r2_hidden('#skF_1'(A_17,k1_wellord2(A_99)),A_99) ) ),
    inference(resolution,[status(thm)],[c_667,c_28])).

tff(c_679,plain,(
    ! [A_100,A_101] :
      ( r1_tarski(k6_relat_1(A_100),k1_wellord2(A_101))
      | ~ r2_hidden('#skF_1'(A_100,k1_wellord2(A_101)),A_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_54,c_671])).

tff(c_683,plain,(
    ! [A_17] :
      ( r1_tarski(k6_relat_1(A_17),k1_wellord2(A_17))
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(resolution,[status(thm)],[c_30,c_679])).

tff(c_687,plain,(
    ! [A_102] : r1_tarski(k6_relat_1(A_102),k1_wellord2(A_102)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_683])).

tff(c_32,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_282,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k1_relat_1(A_59),k1_relat_1(B_60))
      | ~ r1_tarski(A_59,B_60)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_290,plain,(
    ! [A_16,B_60] :
      ( r1_tarski(A_16,k1_relat_1(B_60))
      | ~ r1_tarski(k6_relat_1(A_16),B_60)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_282])).

tff(c_297,plain,(
    ! [A_16,B_60] :
      ( r1_tarski(A_16,k1_relat_1(B_60))
      | ~ r1_tarski(k6_relat_1(A_16),B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_290])).

tff(c_693,plain,(
    ! [A_102] :
      ( r1_tarski(A_102,k1_relat_1(k1_wellord2(A_102)))
      | ~ v1_relat_1(k1_wellord2(A_102)) ) ),
    inference(resolution,[status(thm)],[c_687,c_297])).

tff(c_704,plain,(
    ! [A_102] : r1_tarski(A_102,k1_relat_1(k1_wellord2(A_102))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_693])).

tff(c_48,plain,(
    ! [A_21] :
      ( k3_relat_1(k1_wellord2(A_21)) = A_21
      | ~ v1_relat_1(k1_wellord2(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    ! [A_21] : k3_relat_1(k1_wellord2(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48])).

tff(c_198,plain,(
    ! [A_52] :
      ( k2_xboole_0(k1_relat_1(A_52),k2_relat_1(A_52)) = k3_relat_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_234,plain,(
    ! [A_56] :
      ( r1_tarski(k1_relat_1(A_56),k3_relat_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_10])).

tff(c_248,plain,(
    ! [A_21] :
      ( r1_tarski(k1_relat_1(k1_wellord2(A_21)),A_21)
      | ~ v1_relat_1(k1_wellord2(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_234])).

tff(c_257,plain,(
    ! [A_57] : r1_tarski(k1_relat_1(k1_wellord2(A_57)),A_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_248])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_263,plain,(
    ! [A_57] :
      ( k1_relat_1(k1_wellord2(A_57)) = A_57
      | ~ r1_tarski(A_57,k1_relat_1(k1_wellord2(A_57))) ) ),
    inference(resolution,[status(thm)],[c_257,c_2])).

tff(c_754,plain,(
    ! [A_57] : k1_relat_1(k1_wellord2(A_57)) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_263])).

tff(c_781,plain,(
    ! [A_106] : k1_relat_1(k1_wellord2(A_106)) = A_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_263])).

tff(c_16,plain,(
    ! [A_11] :
      ( k2_xboole_0(k1_relat_1(A_11),k2_relat_1(A_11)) = k3_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_805,plain,(
    ! [A_106] :
      ( k2_xboole_0(A_106,k2_relat_1(k1_wellord2(A_106))) = k3_relat_1(k1_wellord2(A_106))
      | ~ v1_relat_1(k1_wellord2(A_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_16])).

tff(c_826,plain,(
    ! [A_106] : k2_xboole_0(A_106,k2_relat_1(k1_wellord2(A_106))) = A_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_62,c_805])).

tff(c_26,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_372,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k2_relat_1(A_65),k2_relat_1(B_66))
      | ~ r1_tarski(A_65,B_66)
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_380,plain,(
    ! [A_16,B_66] :
      ( r1_tarski(A_16,k2_relat_1(B_66))
      | ~ r1_tarski(k6_relat_1(A_16),B_66)
      | ~ v1_relat_1(B_66)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_372])).

tff(c_387,plain,(
    ! [A_16,B_66] :
      ( r1_tarski(A_16,k2_relat_1(B_66))
      | ~ r1_tarski(k6_relat_1(A_16),B_66)
      | ~ v1_relat_1(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_380])).

tff(c_690,plain,(
    ! [A_102] :
      ( r1_tarski(A_102,k2_relat_1(k1_wellord2(A_102)))
      | ~ v1_relat_1(k1_wellord2(A_102)) ) ),
    inference(resolution,[status(thm)],[c_687,c_387])).

tff(c_707,plain,(
    ! [A_103] : r1_tarski(A_103,k2_relat_1(k1_wellord2(A_103))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_690])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_724,plain,(
    ! [A_103] : k2_xboole_0(A_103,k2_relat_1(k1_wellord2(A_103))) = k2_relat_1(k1_wellord2(A_103)) ),
    inference(resolution,[status(thm)],[c_707,c_8])).

tff(c_922,plain,(
    ! [A_110] : k2_relat_1(k1_wellord2(A_110)) = A_110 ),
    inference(demodulation,[status(thm),theory(equality)],[c_826,c_724])).

tff(c_18,plain,(
    ! [A_12] :
      ( r1_tarski(A_12,k2_zfmisc_1(k1_relat_1(A_12),k2_relat_1(A_12)))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_940,plain,(
    ! [A_110] :
      ( r1_tarski(k1_wellord2(A_110),k2_zfmisc_1(k1_relat_1(k1_wellord2(A_110)),A_110))
      | ~ v1_relat_1(k1_wellord2(A_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_922,c_18])).

tff(c_954,plain,(
    ! [A_110] : r1_tarski(k1_wellord2(A_110),k2_zfmisc_1(A_110,A_110)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_754,c_940])).

tff(c_56,plain,(
    ~ r1_tarski(k1_wellord2('#skF_4'),k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_954,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:36:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.44  
% 2.77/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.45  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.77/1.45  
% 2.77/1.45  %Foreground sorts:
% 2.77/1.45  
% 2.77/1.45  
% 2.77/1.45  %Background operators:
% 2.77/1.45  
% 2.77/1.45  
% 2.77/1.45  %Foreground operators:
% 2.77/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.77/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.77/1.45  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.77/1.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.77/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.77/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.45  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.77/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.77/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.77/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.77/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.45  
% 3.03/1.46  tff(f_94, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.03/1.46  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: (r2_hidden(C, A) => r2_hidden(k4_tarski(C, C), B))) => r1_tarski(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_relat_1)).
% 3.03/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.03/1.46  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 3.03/1.46  tff(f_77, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.03/1.46  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.03/1.46  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 3.03/1.46  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 3.03/1.46  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.03/1.46  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.03/1.46  tff(f_49, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.03/1.46  tff(f_97, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 3.03/1.46  tff(c_54, plain, (![A_29]: (v1_relat_1(k1_wellord2(A_29)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.03/1.46  tff(c_30, plain, (![A_17, B_18]: (r2_hidden('#skF_1'(A_17, B_18), A_17) | r1_tarski(k6_relat_1(A_17), B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.03/1.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.03/1.46  tff(c_50, plain, (![C_27, D_28, A_21]: (r2_hidden(k4_tarski(C_27, D_28), k1_wellord2(A_21)) | ~r1_tarski(C_27, D_28) | ~r2_hidden(D_28, A_21) | ~r2_hidden(C_27, A_21) | ~v1_relat_1(k1_wellord2(A_21)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.03/1.46  tff(c_667, plain, (![C_97, D_98, A_99]: (r2_hidden(k4_tarski(C_97, D_98), k1_wellord2(A_99)) | ~r1_tarski(C_97, D_98) | ~r2_hidden(D_98, A_99) | ~r2_hidden(C_97, A_99))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50])).
% 3.03/1.46  tff(c_28, plain, (![A_17, B_18]: (~r2_hidden(k4_tarski('#skF_1'(A_17, B_18), '#skF_1'(A_17, B_18)), B_18) | r1_tarski(k6_relat_1(A_17), B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.03/1.46  tff(c_671, plain, (![A_17, A_99]: (r1_tarski(k6_relat_1(A_17), k1_wellord2(A_99)) | ~v1_relat_1(k1_wellord2(A_99)) | ~r1_tarski('#skF_1'(A_17, k1_wellord2(A_99)), '#skF_1'(A_17, k1_wellord2(A_99))) | ~r2_hidden('#skF_1'(A_17, k1_wellord2(A_99)), A_99))), inference(resolution, [status(thm)], [c_667, c_28])).
% 3.03/1.46  tff(c_679, plain, (![A_100, A_101]: (r1_tarski(k6_relat_1(A_100), k1_wellord2(A_101)) | ~r2_hidden('#skF_1'(A_100, k1_wellord2(A_101)), A_101))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_54, c_671])).
% 3.03/1.46  tff(c_683, plain, (![A_17]: (r1_tarski(k6_relat_1(A_17), k1_wellord2(A_17)) | ~v1_relat_1(k1_wellord2(A_17)))), inference(resolution, [status(thm)], [c_30, c_679])).
% 3.03/1.46  tff(c_687, plain, (![A_102]: (r1_tarski(k6_relat_1(A_102), k1_wellord2(A_102)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_683])).
% 3.03/1.46  tff(c_32, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.03/1.46  tff(c_24, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.03/1.46  tff(c_282, plain, (![A_59, B_60]: (r1_tarski(k1_relat_1(A_59), k1_relat_1(B_60)) | ~r1_tarski(A_59, B_60) | ~v1_relat_1(B_60) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.03/1.46  tff(c_290, plain, (![A_16, B_60]: (r1_tarski(A_16, k1_relat_1(B_60)) | ~r1_tarski(k6_relat_1(A_16), B_60) | ~v1_relat_1(B_60) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_282])).
% 3.03/1.46  tff(c_297, plain, (![A_16, B_60]: (r1_tarski(A_16, k1_relat_1(B_60)) | ~r1_tarski(k6_relat_1(A_16), B_60) | ~v1_relat_1(B_60))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_290])).
% 3.03/1.46  tff(c_693, plain, (![A_102]: (r1_tarski(A_102, k1_relat_1(k1_wellord2(A_102))) | ~v1_relat_1(k1_wellord2(A_102)))), inference(resolution, [status(thm)], [c_687, c_297])).
% 3.03/1.46  tff(c_704, plain, (![A_102]: (r1_tarski(A_102, k1_relat_1(k1_wellord2(A_102))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_693])).
% 3.03/1.46  tff(c_48, plain, (![A_21]: (k3_relat_1(k1_wellord2(A_21))=A_21 | ~v1_relat_1(k1_wellord2(A_21)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.03/1.46  tff(c_62, plain, (![A_21]: (k3_relat_1(k1_wellord2(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48])).
% 3.03/1.46  tff(c_198, plain, (![A_52]: (k2_xboole_0(k1_relat_1(A_52), k2_relat_1(A_52))=k3_relat_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.03/1.46  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.03/1.46  tff(c_234, plain, (![A_56]: (r1_tarski(k1_relat_1(A_56), k3_relat_1(A_56)) | ~v1_relat_1(A_56))), inference(superposition, [status(thm), theory('equality')], [c_198, c_10])).
% 3.03/1.46  tff(c_248, plain, (![A_21]: (r1_tarski(k1_relat_1(k1_wellord2(A_21)), A_21) | ~v1_relat_1(k1_wellord2(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_234])).
% 3.03/1.46  tff(c_257, plain, (![A_57]: (r1_tarski(k1_relat_1(k1_wellord2(A_57)), A_57))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_248])).
% 3.03/1.46  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.03/1.46  tff(c_263, plain, (![A_57]: (k1_relat_1(k1_wellord2(A_57))=A_57 | ~r1_tarski(A_57, k1_relat_1(k1_wellord2(A_57))))), inference(resolution, [status(thm)], [c_257, c_2])).
% 3.03/1.46  tff(c_754, plain, (![A_57]: (k1_relat_1(k1_wellord2(A_57))=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_704, c_263])).
% 3.03/1.46  tff(c_781, plain, (![A_106]: (k1_relat_1(k1_wellord2(A_106))=A_106)), inference(demodulation, [status(thm), theory('equality')], [c_704, c_263])).
% 3.03/1.46  tff(c_16, plain, (![A_11]: (k2_xboole_0(k1_relat_1(A_11), k2_relat_1(A_11))=k3_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.03/1.46  tff(c_805, plain, (![A_106]: (k2_xboole_0(A_106, k2_relat_1(k1_wellord2(A_106)))=k3_relat_1(k1_wellord2(A_106)) | ~v1_relat_1(k1_wellord2(A_106)))), inference(superposition, [status(thm), theory('equality')], [c_781, c_16])).
% 3.03/1.46  tff(c_826, plain, (![A_106]: (k2_xboole_0(A_106, k2_relat_1(k1_wellord2(A_106)))=A_106)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_62, c_805])).
% 3.03/1.46  tff(c_26, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.03/1.46  tff(c_372, plain, (![A_65, B_66]: (r1_tarski(k2_relat_1(A_65), k2_relat_1(B_66)) | ~r1_tarski(A_65, B_66) | ~v1_relat_1(B_66) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.03/1.46  tff(c_380, plain, (![A_16, B_66]: (r1_tarski(A_16, k2_relat_1(B_66)) | ~r1_tarski(k6_relat_1(A_16), B_66) | ~v1_relat_1(B_66) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_372])).
% 3.03/1.46  tff(c_387, plain, (![A_16, B_66]: (r1_tarski(A_16, k2_relat_1(B_66)) | ~r1_tarski(k6_relat_1(A_16), B_66) | ~v1_relat_1(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_380])).
% 3.03/1.46  tff(c_690, plain, (![A_102]: (r1_tarski(A_102, k2_relat_1(k1_wellord2(A_102))) | ~v1_relat_1(k1_wellord2(A_102)))), inference(resolution, [status(thm)], [c_687, c_387])).
% 3.03/1.46  tff(c_707, plain, (![A_103]: (r1_tarski(A_103, k2_relat_1(k1_wellord2(A_103))))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_690])).
% 3.03/1.46  tff(c_8, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.03/1.46  tff(c_724, plain, (![A_103]: (k2_xboole_0(A_103, k2_relat_1(k1_wellord2(A_103)))=k2_relat_1(k1_wellord2(A_103)))), inference(resolution, [status(thm)], [c_707, c_8])).
% 3.03/1.46  tff(c_922, plain, (![A_110]: (k2_relat_1(k1_wellord2(A_110))=A_110)), inference(demodulation, [status(thm), theory('equality')], [c_826, c_724])).
% 3.03/1.46  tff(c_18, plain, (![A_12]: (r1_tarski(A_12, k2_zfmisc_1(k1_relat_1(A_12), k2_relat_1(A_12))) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.03/1.46  tff(c_940, plain, (![A_110]: (r1_tarski(k1_wellord2(A_110), k2_zfmisc_1(k1_relat_1(k1_wellord2(A_110)), A_110)) | ~v1_relat_1(k1_wellord2(A_110)))), inference(superposition, [status(thm), theory('equality')], [c_922, c_18])).
% 3.03/1.46  tff(c_954, plain, (![A_110]: (r1_tarski(k1_wellord2(A_110), k2_zfmisc_1(A_110, A_110)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_754, c_940])).
% 3.03/1.46  tff(c_56, plain, (~r1_tarski(k1_wellord2('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.03/1.46  tff(c_958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_954, c_56])).
% 3.03/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.46  
% 3.03/1.46  Inference rules
% 3.03/1.46  ----------------------
% 3.03/1.46  #Ref     : 0
% 3.03/1.46  #Sup     : 180
% 3.03/1.46  #Fact    : 0
% 3.03/1.46  #Define  : 0
% 3.03/1.46  #Split   : 0
% 3.03/1.46  #Chain   : 0
% 3.03/1.46  #Close   : 0
% 3.03/1.46  
% 3.03/1.46  Ordering : KBO
% 3.03/1.46  
% 3.03/1.46  Simplification rules
% 3.03/1.46  ----------------------
% 3.03/1.46  #Subsume      : 12
% 3.03/1.46  #Demod        : 241
% 3.03/1.46  #Tautology    : 91
% 3.03/1.46  #SimpNegUnit  : 0
% 3.03/1.46  #BackRed      : 7
% 3.03/1.46  
% 3.03/1.46  #Partial instantiations: 0
% 3.03/1.46  #Strategies tried      : 1
% 3.03/1.46  
% 3.03/1.46  Timing (in seconds)
% 3.03/1.46  ----------------------
% 3.08/1.47  Preprocessing        : 0.33
% 3.08/1.47  Parsing              : 0.17
% 3.08/1.47  CNF conversion       : 0.02
% 3.08/1.47  Main loop            : 0.36
% 3.08/1.47  Inferencing          : 0.13
% 3.08/1.47  Reduction            : 0.12
% 3.08/1.47  Demodulation         : 0.09
% 3.08/1.47  BG Simplification    : 0.02
% 3.08/1.47  Subsumption          : 0.06
% 3.08/1.47  Abstraction          : 0.02
% 3.08/1.47  MUC search           : 0.00
% 3.08/1.47  Cooper               : 0.00
% 3.08/1.47  Total                : 0.73
% 3.08/1.47  Index Insertion      : 0.00
% 3.08/1.47  Index Deletion       : 0.00
% 3.08/1.47  Index Matching       : 0.00
% 3.08/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
