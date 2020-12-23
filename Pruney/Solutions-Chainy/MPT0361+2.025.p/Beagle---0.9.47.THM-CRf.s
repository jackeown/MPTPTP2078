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
% DateTime   : Thu Dec  3 09:56:30 EST 2020

% Result     : Theorem 39.55s
% Output     : CNFRefutation 39.55s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 171 expanded)
%              Number of leaves         :   32 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 329 expanded)
%              Number of equality atoms :   18 (  49 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_42,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_56,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_67,plain,(
    ! [A_58,B_59] : k1_enumset1(A_58,A_58,B_59) = k2_tarski(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [E_7,A_1,C_3] : r2_hidden(E_7,k1_enumset1(A_1,E_7,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_76,plain,(
    ! [A_58,B_59] : r2_hidden(A_58,k2_tarski(A_58,B_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_6])).

tff(c_38,plain,(
    ! [A_30,B_31] : k3_tarski(k2_tarski(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_88,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,k3_tarski(B_65))
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_137,plain,(
    ! [A_77,A_78,B_79] :
      ( r1_tarski(A_77,k2_xboole_0(A_78,B_79))
      | ~ r2_hidden(A_77,k2_tarski(A_78,B_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_88])).

tff(c_144,plain,(
    ! [A_58,B_59] : r1_tarski(A_58,k2_xboole_0(A_58,B_59)) ),
    inference(resolution,[status(thm)],[c_76,c_137])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_235,plain,(
    ! [A_98,B_99,C_100] :
      ( k4_subset_1(A_98,B_99,C_100) = k2_xboole_0(B_99,C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(A_98))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_245,plain,(
    ! [B_101] :
      ( k4_subset_1('#skF_3',B_101,'#skF_5') = k2_xboole_0(B_101,'#skF_5')
      | ~ m1_subset_1(B_101,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_52,c_235])).

tff(c_258,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_245])).

tff(c_290,plain,(
    ! [A_103,B_104,C_105] :
      ( m1_subset_1(k4_subset_1(A_103,B_104,C_105),k1_zfmisc_1(A_103))
      | ~ m1_subset_1(C_105,k1_zfmisc_1(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_311,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_290])).

tff(c_324,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_311])).

tff(c_40,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k3_subset_1(A_32,B_33),k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2310,plain,(
    ! [A_153,B_154,B_155] :
      ( k4_subset_1(A_153,B_154,k3_subset_1(A_153,B_155)) = k2_xboole_0(B_154,k3_subset_1(A_153,B_155))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(A_153))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_153)) ) ),
    inference(resolution,[status(thm)],[c_40,c_235])).

tff(c_2498,plain,(
    ! [B_156] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_156)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_156))
      | ~ m1_subset_1(B_156,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_2310])).

tff(c_2631,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5'))) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_324,c_2498])).

tff(c_42,plain,(
    ! [A_34,B_35,C_36] :
      ( m1_subset_1(k4_subset_1(A_34,B_35,C_36),k1_zfmisc_1(A_34))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(A_34))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3648,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4',k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5'))),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2631,c_42])).

tff(c_3654,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4',k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5'))),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3648])).

tff(c_32525,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3654])).

tff(c_32528,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_32525])).

tff(c_32532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_32528])).

tff(c_32534,plain,(
    m1_subset_1(k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3654])).

tff(c_44,plain,(
    ! [A_37,B_38] :
      ( k3_subset_1(A_37,k3_subset_1(A_37,B_38)) = B_38
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2767,plain,(
    ! [A_157,B_158,C_159] :
      ( k3_subset_1(A_157,k3_subset_1(A_157,k4_subset_1(A_157,B_158,C_159))) = k4_subset_1(A_157,B_158,C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(A_157))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_157)) ) ),
    inference(resolution,[status(thm)],[c_290,c_44])).

tff(c_48,plain,(
    ! [C_45,A_42,B_43] :
      ( r1_tarski(C_45,k3_subset_1(A_42,B_43))
      | ~ r1_tarski(B_43,k3_subset_1(A_42,C_45))
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14092,plain,(
    ! [A_226,B_227,C_228,B_229] :
      ( r1_tarski(k3_subset_1(A_226,k4_subset_1(A_226,B_227,C_228)),k3_subset_1(A_226,B_229))
      | ~ r1_tarski(B_229,k4_subset_1(A_226,B_227,C_228))
      | ~ m1_subset_1(k3_subset_1(A_226,k4_subset_1(A_226,B_227,C_228)),k1_zfmisc_1(A_226))
      | ~ m1_subset_1(B_229,k1_zfmisc_1(A_226))
      | ~ m1_subset_1(C_228,k1_zfmisc_1(A_226))
      | ~ m1_subset_1(B_227,k1_zfmisc_1(A_226)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2767,c_48])).

tff(c_14487,plain,(
    ! [B_229] :
      ( r1_tarski(k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k3_subset_1('#skF_3',B_229))
      | ~ r1_tarski(B_229,k4_subset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(k3_subset_1('#skF_3',k4_subset_1('#skF_3','#skF_4','#skF_5')),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(B_229,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_14092])).

tff(c_14698,plain,(
    ! [B_229] :
      ( r1_tarski(k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k3_subset_1('#skF_3',B_229))
      | ~ r1_tarski(B_229,k2_xboole_0('#skF_4','#skF_5'))
      | ~ m1_subset_1(k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1(B_229,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_258,c_258,c_14487])).

tff(c_71358,plain,(
    ! [B_347] :
      ( r1_tarski(k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k3_subset_1('#skF_3',B_347))
      | ~ r1_tarski(B_347,k2_xboole_0('#skF_4','#skF_5'))
      | ~ m1_subset_1(B_347,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32534,c_14698])).

tff(c_50,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3',k4_subset_1('#skF_3','#skF_4','#skF_5')),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_263,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_50])).

tff(c_71381,plain,
    ( ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_71358,c_263])).

tff(c_71834,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_144,c_71381])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:04:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 39.55/29.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.55/29.49  
% 39.55/29.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.55/29.49  %$ r2_hidden > r1_tarski > m1_subset_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 39.55/29.49  
% 39.55/29.49  %Foreground sorts:
% 39.55/29.49  
% 39.55/29.49  
% 39.55/29.49  %Background operators:
% 39.55/29.49  
% 39.55/29.49  
% 39.55/29.49  %Foreground operators:
% 39.55/29.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 39.55/29.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 39.55/29.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 39.55/29.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 39.55/29.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 39.55/29.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 39.55/29.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 39.55/29.49  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 39.55/29.49  tff('#skF_5', type, '#skF_5': $i).
% 39.55/29.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 39.55/29.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 39.55/29.49  tff('#skF_3', type, '#skF_3': $i).
% 39.55/29.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 39.55/29.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 39.55/29.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 39.55/29.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 39.55/29.49  tff('#skF_4', type, '#skF_4': $i).
% 39.55/29.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 39.55/29.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 39.55/29.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 39.55/29.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 39.55/29.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 39.55/29.49  
% 39.55/29.51  tff(f_93, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_subset_1)).
% 39.55/29.51  tff(f_42, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 39.55/29.51  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 39.55/29.51  tff(f_56, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 39.55/29.51  tff(f_54, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 39.55/29.51  tff(f_76, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 39.55/29.51  tff(f_66, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 39.55/29.51  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 39.55/29.51  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 39.55/29.51  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 39.55/29.51  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 39.55/29.51  tff(c_67, plain, (![A_58, B_59]: (k1_enumset1(A_58, A_58, B_59)=k2_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_42])).
% 39.55/29.51  tff(c_6, plain, (![E_7, A_1, C_3]: (r2_hidden(E_7, k1_enumset1(A_1, E_7, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 39.55/29.51  tff(c_76, plain, (![A_58, B_59]: (r2_hidden(A_58, k2_tarski(A_58, B_59)))), inference(superposition, [status(thm), theory('equality')], [c_67, c_6])).
% 39.55/29.51  tff(c_38, plain, (![A_30, B_31]: (k3_tarski(k2_tarski(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_56])).
% 39.55/29.51  tff(c_88, plain, (![A_64, B_65]: (r1_tarski(A_64, k3_tarski(B_65)) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_54])).
% 39.55/29.51  tff(c_137, plain, (![A_77, A_78, B_79]: (r1_tarski(A_77, k2_xboole_0(A_78, B_79)) | ~r2_hidden(A_77, k2_tarski(A_78, B_79)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_88])).
% 39.55/29.51  tff(c_144, plain, (![A_58, B_59]: (r1_tarski(A_58, k2_xboole_0(A_58, B_59)))), inference(resolution, [status(thm)], [c_76, c_137])).
% 39.55/29.51  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 39.55/29.51  tff(c_235, plain, (![A_98, B_99, C_100]: (k4_subset_1(A_98, B_99, C_100)=k2_xboole_0(B_99, C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(A_98)) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 39.55/29.51  tff(c_245, plain, (![B_101]: (k4_subset_1('#skF_3', B_101, '#skF_5')=k2_xboole_0(B_101, '#skF_5') | ~m1_subset_1(B_101, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_52, c_235])).
% 39.55/29.51  tff(c_258, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_245])).
% 39.55/29.51  tff(c_290, plain, (![A_103, B_104, C_105]: (m1_subset_1(k4_subset_1(A_103, B_104, C_105), k1_zfmisc_1(A_103)) | ~m1_subset_1(C_105, k1_zfmisc_1(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 39.55/29.51  tff(c_311, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_258, c_290])).
% 39.55/29.51  tff(c_324, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_311])).
% 39.55/29.51  tff(c_40, plain, (![A_32, B_33]: (m1_subset_1(k3_subset_1(A_32, B_33), k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 39.55/29.51  tff(c_2310, plain, (![A_153, B_154, B_155]: (k4_subset_1(A_153, B_154, k3_subset_1(A_153, B_155))=k2_xboole_0(B_154, k3_subset_1(A_153, B_155)) | ~m1_subset_1(B_154, k1_zfmisc_1(A_153)) | ~m1_subset_1(B_155, k1_zfmisc_1(A_153)))), inference(resolution, [status(thm)], [c_40, c_235])).
% 39.55/29.51  tff(c_2498, plain, (![B_156]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_156))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_156)) | ~m1_subset_1(B_156, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_54, c_2310])).
% 39.55/29.51  tff(c_2631, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_324, c_2498])).
% 39.55/29.51  tff(c_42, plain, (![A_34, B_35, C_36]: (m1_subset_1(k4_subset_1(A_34, B_35, C_36), k1_zfmisc_1(A_34)) | ~m1_subset_1(C_36, k1_zfmisc_1(A_34)) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 39.55/29.51  tff(c_3648, plain, (m1_subset_1(k2_xboole_0('#skF_4', k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2631, c_42])).
% 39.55/29.51  tff(c_3654, plain, (m1_subset_1(k2_xboole_0('#skF_4', k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3648])).
% 39.55/29.51  tff(c_32525, plain, (~m1_subset_1(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3654])).
% 39.55/29.51  tff(c_32528, plain, (~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_32525])).
% 39.55/29.51  tff(c_32532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_324, c_32528])).
% 39.55/29.51  tff(c_32534, plain, (m1_subset_1(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_3654])).
% 39.55/29.51  tff(c_44, plain, (![A_37, B_38]: (k3_subset_1(A_37, k3_subset_1(A_37, B_38))=B_38 | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 39.55/29.51  tff(c_2767, plain, (![A_157, B_158, C_159]: (k3_subset_1(A_157, k3_subset_1(A_157, k4_subset_1(A_157, B_158, C_159)))=k4_subset_1(A_157, B_158, C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(A_157)) | ~m1_subset_1(B_158, k1_zfmisc_1(A_157)))), inference(resolution, [status(thm)], [c_290, c_44])).
% 39.55/29.51  tff(c_48, plain, (![C_45, A_42, B_43]: (r1_tarski(C_45, k3_subset_1(A_42, B_43)) | ~r1_tarski(B_43, k3_subset_1(A_42, C_45)) | ~m1_subset_1(C_45, k1_zfmisc_1(A_42)) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 39.55/29.51  tff(c_14092, plain, (![A_226, B_227, C_228, B_229]: (r1_tarski(k3_subset_1(A_226, k4_subset_1(A_226, B_227, C_228)), k3_subset_1(A_226, B_229)) | ~r1_tarski(B_229, k4_subset_1(A_226, B_227, C_228)) | ~m1_subset_1(k3_subset_1(A_226, k4_subset_1(A_226, B_227, C_228)), k1_zfmisc_1(A_226)) | ~m1_subset_1(B_229, k1_zfmisc_1(A_226)) | ~m1_subset_1(C_228, k1_zfmisc_1(A_226)) | ~m1_subset_1(B_227, k1_zfmisc_1(A_226)))), inference(superposition, [status(thm), theory('equality')], [c_2767, c_48])).
% 39.55/29.51  tff(c_14487, plain, (![B_229]: (r1_tarski(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k3_subset_1('#skF_3', B_229)) | ~r1_tarski(B_229, k4_subset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(k3_subset_1('#skF_3', k4_subset_1('#skF_3', '#skF_4', '#skF_5')), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(B_229, k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_258, c_14092])).
% 39.55/29.51  tff(c_14698, plain, (![B_229]: (r1_tarski(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k3_subset_1('#skF_3', B_229)) | ~r1_tarski(B_229, k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k1_zfmisc_1('#skF_3')) | ~m1_subset_1(B_229, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_258, c_258, c_14487])).
% 39.55/29.51  tff(c_71358, plain, (![B_347]: (r1_tarski(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k3_subset_1('#skF_3', B_347)) | ~r1_tarski(B_347, k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(B_347, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32534, c_14698])).
% 39.55/29.51  tff(c_50, plain, (~r1_tarski(k3_subset_1('#skF_3', k4_subset_1('#skF_3', '#skF_4', '#skF_5')), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 39.55/29.51  tff(c_263, plain, (~r1_tarski(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_50])).
% 39.55/29.51  tff(c_71381, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_71358, c_263])).
% 39.55/29.51  tff(c_71834, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_144, c_71381])).
% 39.55/29.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.55/29.51  
% 39.55/29.51  Inference rules
% 39.55/29.51  ----------------------
% 39.55/29.51  #Ref     : 0
% 39.55/29.51  #Sup     : 17240
% 39.55/29.51  #Fact    : 30
% 39.55/29.51  #Define  : 0
% 39.55/29.51  #Split   : 11
% 39.55/29.51  #Chain   : 0
% 39.55/29.51  #Close   : 0
% 39.55/29.51  
% 39.55/29.51  Ordering : KBO
% 39.55/29.51  
% 39.55/29.51  Simplification rules
% 39.55/29.51  ----------------------
% 39.55/29.51  #Subsume      : 665
% 39.55/29.51  #Demod        : 19400
% 39.55/29.51  #Tautology    : 2077
% 39.55/29.51  #SimpNegUnit  : 1
% 39.55/29.51  #BackRed      : 1
% 39.55/29.51  
% 39.55/29.51  #Partial instantiations: 0
% 39.55/29.51  #Strategies tried      : 1
% 39.55/29.51  
% 39.55/29.51  Timing (in seconds)
% 39.55/29.51  ----------------------
% 39.55/29.51  Preprocessing        : 0.42
% 39.55/29.51  Parsing              : 0.25
% 39.55/29.51  CNF conversion       : 0.02
% 39.55/29.51  Main loop            : 28.26
% 39.55/29.51  Inferencing          : 2.35
% 39.55/29.51  Reduction            : 15.72
% 39.55/29.51  Demodulation         : 14.50
% 39.55/29.51  BG Simplification    : 0.36
% 39.55/29.51  Subsumption          : 8.87
% 39.55/29.51  Abstraction          : 0.69
% 39.55/29.51  MUC search           : 0.00
% 39.55/29.51  Cooper               : 0.00
% 39.55/29.51  Total                : 28.71
% 39.55/29.51  Index Insertion      : 0.00
% 39.55/29.51  Index Deletion       : 0.00
% 39.55/29.51  Index Matching       : 0.00
% 39.55/29.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
