%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0923+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:05 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   52 (  64 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 119 expanded)
%              Number of equality atoms :   19 (  33 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_1 > #skF_11 > #skF_9 > #skF_4 > #skF_10 > #skF_8 > #skF_14 > #skF_13 > #skF_2 > #skF_7 > #skF_6 > #skF_5 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_40,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ~ ( r2_hidden(A,k3_zfmisc_1(B,C,D))
        & ! [E,F,G] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & r2_hidden(G,D)
              & A = k3_mcart_1(E,F,G) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_mcart_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] : k4_mcart_1(A,B,C,D) = k4_tarski(k3_mcart_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ~ ( r2_hidden(A,k4_zfmisc_1(B,C,D,E))
          & ! [F,G,H,I] :
              ~ ( r2_hidden(F,B)
                & r2_hidden(G,C)
                & r2_hidden(H,D)
                & r2_hidden(I,E)
                & A = k4_mcart_1(F,G,H,I) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_mcart_1)).

tff(c_28,plain,(
    ! [A_39,B_40,C_41,D_42] : k2_zfmisc_1(k3_zfmisc_1(A_39,B_40,C_41),D_42) = k4_zfmisc_1(A_39,B_40,C_41,D_42) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_69,plain,(
    ! [A_82,B_83,D_84] :
      ( r2_hidden('#skF_6'(A_82,B_83,k2_zfmisc_1(A_82,B_83),D_84),B_83)
      | ~ r2_hidden(D_84,k2_zfmisc_1(A_82,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_72,plain,(
    ! [D_84,D_42,A_39,C_41,B_40] :
      ( r2_hidden('#skF_6'(k3_zfmisc_1(A_39,B_40,C_41),D_42,k4_zfmisc_1(A_39,B_40,C_41,D_42),D_84),D_42)
      | ~ r2_hidden(D_84,k2_zfmisc_1(k3_zfmisc_1(A_39,B_40,C_41),D_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_69])).

tff(c_73,plain,(
    ! [D_84,D_42,A_39,C_41,B_40] :
      ( r2_hidden('#skF_6'(k3_zfmisc_1(A_39,B_40,C_41),D_42,k4_zfmisc_1(A_39,B_40,C_41,D_42),D_84),D_42)
      | ~ r2_hidden(D_84,k4_zfmisc_1(A_39,B_40,C_41,D_42)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_72])).

tff(c_8,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),A_1)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_36,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( r2_hidden('#skF_7'(A_43,B_44,C_45,D_46),B_44)
      | ~ r2_hidden(A_43,k3_zfmisc_1(B_44,C_45,D_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( r2_hidden('#skF_8'(A_43,B_44,C_45,D_46),C_45)
      | ~ r2_hidden(A_43,k3_zfmisc_1(B_44,C_45,D_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( r2_hidden('#skF_9'(A_43,B_44,C_45,D_46),D_46)
      | ~ r2_hidden(A_43,k3_zfmisc_1(B_44,C_45,D_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_1,B_2,D_28] :
      ( k4_tarski('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),'#skF_6'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28)) = D_28
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_121,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( k3_mcart_1('#skF_7'(A_131,B_132,C_133,D_134),'#skF_8'(A_131,B_132,C_133,D_134),'#skF_9'(A_131,B_132,C_133,D_134)) = A_131
      | ~ r2_hidden(A_131,k3_zfmisc_1(B_132,C_133,D_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_35,B_36,C_37,D_38] : k4_tarski(k3_mcart_1(A_35,B_36,C_37),D_38) = k4_mcart_1(A_35,B_36,C_37,D_38) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_166,plain,(
    ! [D_161,B_163,D_165,A_162,C_164] :
      ( k4_mcart_1('#skF_7'(A_162,B_163,C_164,D_161),'#skF_8'(A_162,B_163,C_164,D_161),'#skF_9'(A_162,B_163,C_164,D_161),D_165) = k4_tarski(A_162,D_165)
      | ~ r2_hidden(A_162,k3_zfmisc_1(B_163,C_164,D_161)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_26])).

tff(c_38,plain,(
    ! [F_54,G_55,H_56,I_57] :
      ( k4_mcart_1(F_54,G_55,H_56,I_57) != '#skF_10'
      | ~ r2_hidden(I_57,'#skF_14')
      | ~ r2_hidden(H_56,'#skF_13')
      | ~ r2_hidden(G_55,'#skF_12')
      | ~ r2_hidden(F_54,'#skF_11') ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_189,plain,(
    ! [B_180,D_184,D_181,A_182,C_183] :
      ( k4_tarski(A_182,D_181) != '#skF_10'
      | ~ r2_hidden(D_181,'#skF_14')
      | ~ r2_hidden('#skF_9'(A_182,B_180,C_183,D_184),'#skF_13')
      | ~ r2_hidden('#skF_8'(A_182,B_180,C_183,D_184),'#skF_12')
      | ~ r2_hidden('#skF_7'(A_182,B_180,C_183,D_184),'#skF_11')
      | ~ r2_hidden(A_182,k3_zfmisc_1(B_180,C_183,D_184)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_38])).

tff(c_424,plain,(
    ! [B_341,A_343,B_339,D_338,C_340,D_342] :
      ( D_338 != '#skF_10'
      | ~ r2_hidden('#skF_6'(A_343,B_341,k2_zfmisc_1(A_343,B_341),D_338),'#skF_14')
      | ~ r2_hidden('#skF_9'('#skF_5'(A_343,B_341,k2_zfmisc_1(A_343,B_341),D_338),B_339,C_340,D_342),'#skF_13')
      | ~ r2_hidden('#skF_8'('#skF_5'(A_343,B_341,k2_zfmisc_1(A_343,B_341),D_338),B_339,C_340,D_342),'#skF_12')
      | ~ r2_hidden('#skF_7'('#skF_5'(A_343,B_341,k2_zfmisc_1(A_343,B_341),D_338),B_339,C_340,D_342),'#skF_11')
      | ~ r2_hidden('#skF_5'(A_343,B_341,k2_zfmisc_1(A_343,B_341),D_338),k3_zfmisc_1(B_339,C_340,D_342))
      | ~ r2_hidden(D_338,k2_zfmisc_1(A_343,B_341)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_189])).

tff(c_766,plain,(
    ! [B_492,D_489,C_491,B_488,A_490] :
      ( D_489 != '#skF_10'
      | ~ r2_hidden('#skF_6'(A_490,B_488,k2_zfmisc_1(A_490,B_488),D_489),'#skF_14')
      | ~ r2_hidden('#skF_8'('#skF_5'(A_490,B_488,k2_zfmisc_1(A_490,B_488),D_489),B_492,C_491,'#skF_13'),'#skF_12')
      | ~ r2_hidden('#skF_7'('#skF_5'(A_490,B_488,k2_zfmisc_1(A_490,B_488),D_489),B_492,C_491,'#skF_13'),'#skF_11')
      | ~ r2_hidden(D_489,k2_zfmisc_1(A_490,B_488))
      | ~ r2_hidden('#skF_5'(A_490,B_488,k2_zfmisc_1(A_490,B_488),D_489),k3_zfmisc_1(B_492,C_491,'#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_32,c_424])).

tff(c_777,plain,(
    ! [D_493,A_494,B_495,B_496] :
      ( D_493 != '#skF_10'
      | ~ r2_hidden('#skF_6'(A_494,B_495,k2_zfmisc_1(A_494,B_495),D_493),'#skF_14')
      | ~ r2_hidden('#skF_7'('#skF_5'(A_494,B_495,k2_zfmisc_1(A_494,B_495),D_493),B_496,'#skF_12','#skF_13'),'#skF_11')
      | ~ r2_hidden(D_493,k2_zfmisc_1(A_494,B_495))
      | ~ r2_hidden('#skF_5'(A_494,B_495,k2_zfmisc_1(A_494,B_495),D_493),k3_zfmisc_1(B_496,'#skF_12','#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_34,c_766])).

tff(c_788,plain,(
    ! [D_497,A_498,B_499] :
      ( D_497 != '#skF_10'
      | ~ r2_hidden('#skF_6'(A_498,B_499,k2_zfmisc_1(A_498,B_499),D_497),'#skF_14')
      | ~ r2_hidden(D_497,k2_zfmisc_1(A_498,B_499))
      | ~ r2_hidden('#skF_5'(A_498,B_499,k2_zfmisc_1(A_498,B_499),D_497),k3_zfmisc_1('#skF_11','#skF_12','#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_36,c_777])).

tff(c_792,plain,(
    ! [D_28,B_2] :
      ( D_28 != '#skF_10'
      | ~ r2_hidden('#skF_6'(k3_zfmisc_1('#skF_11','#skF_12','#skF_13'),B_2,k2_zfmisc_1(k3_zfmisc_1('#skF_11','#skF_12','#skF_13'),B_2),D_28),'#skF_14')
      | ~ r2_hidden(D_28,k2_zfmisc_1(k3_zfmisc_1('#skF_11','#skF_12','#skF_13'),B_2)) ) ),
    inference(resolution,[status(thm)],[c_8,c_788])).

tff(c_800,plain,(
    ! [D_500,B_501] :
      ( D_500 != '#skF_10'
      | ~ r2_hidden('#skF_6'(k3_zfmisc_1('#skF_11','#skF_12','#skF_13'),B_501,k4_zfmisc_1('#skF_11','#skF_12','#skF_13',B_501),D_500),'#skF_14')
      | ~ r2_hidden(D_500,k4_zfmisc_1('#skF_11','#skF_12','#skF_13',B_501)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_792])).

tff(c_806,plain,(
    ~ r2_hidden('#skF_10',k4_zfmisc_1('#skF_11','#skF_12','#skF_13','#skF_14')) ),
    inference(resolution,[status(thm)],[c_73,c_800])).

tff(c_40,plain,(
    r2_hidden('#skF_10',k4_zfmisc_1('#skF_11','#skF_12','#skF_13','#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_806,c_40])).

%------------------------------------------------------------------------------
