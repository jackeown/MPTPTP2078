%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:38 EST 2020

% Result     : Theorem 6.50s
% Output     : CNFRefutation 6.50s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 392 expanded)
%              Number of leaves         :   33 ( 145 expanded)
%              Depth                    :   13
%              Number of atoms          :  210 (1113 expanded)
%              Number of equality atoms :   23 (  81 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( r1_tarski(C,k1_relat_1(k5_relat_1(A,B)))
              <=> ( r1_tarski(C,k1_relat_1(A))
                  & r1_tarski(k9_relat_1(A,C),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_121,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_16,plain,(
    ! [A_19,B_21] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_19,B_21)),k1_relat_1(A_19))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_71,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    k2_xboole_0('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) = k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_71,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_139,plain,(
    ! [C_61] :
      ( r1_tarski('#skF_4',C_61)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),C_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_2])).

tff(c_143,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_139])).

tff(c_146,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_143])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_28,plain,(
    ! [A_29] : v1_relat_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    ! [A_29] : v1_funct_1(k6_relat_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_20,plain,(
    ! [A_24,B_25] :
      ( k5_relat_1(k6_relat_1(A_24),B_25) = k7_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_266,plain,(
    ! [A_68,B_69] :
      ( v1_funct_1(k5_relat_1(A_68,B_69))
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_269,plain,(
    ! [B_25,A_24] :
      ( v1_funct_1(k7_relat_1(B_25,A_24))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_funct_1(k6_relat_1(A_24))
      | ~ v1_relat_1(k6_relat_1(A_24))
      | ~ v1_relat_1(B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_266])).

tff(c_271,plain,(
    ! [B_25,A_24] :
      ( v1_funct_1(k7_relat_1(B_25,A_24))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_269])).

tff(c_36,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_159,plain,(
    ! [B_63,A_64] :
      ( k1_relat_1(k7_relat_1(B_63,A_64)) = A_64
      | ~ r1_tarski(A_64,k1_relat_1(B_63))
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_162,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_146,c_159])).

tff(c_174,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_162])).

tff(c_421,plain,(
    ! [B_73,C_74,A_75] :
      ( k7_relat_1(k5_relat_1(B_73,C_74),A_75) = k5_relat_1(k7_relat_1(B_73,A_75),C_74)
      | ~ v1_relat_1(C_74)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_179,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_71,c_159])).

tff(c_256,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_259,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_256])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_259])).

tff(c_264,plain,(
    k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_430,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_264])).

tff(c_456,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_430])).

tff(c_478,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k7_relat_1('#skF_1','#skF_4')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_16])).

tff(c_490,plain,
    ( r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_174,c_478])).

tff(c_492,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_490])).

tff(c_495,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_492])).

tff(c_499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_495])).

tff(c_501,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_490])).

tff(c_12,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1201,plain,(
    ! [B_91,A_92] :
      ( r1_tarski(k2_relat_1(B_91),k1_relat_1(A_92))
      | k1_relat_1(k5_relat_1(B_91,A_92)) != k1_relat_1(B_91)
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91)
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_4972,plain,(
    ! [B_168,A_169,A_170] :
      ( r1_tarski(k9_relat_1(B_168,A_169),k1_relat_1(A_170))
      | k1_relat_1(k5_relat_1(k7_relat_1(B_168,A_169),A_170)) != k1_relat_1(k7_relat_1(B_168,A_169))
      | ~ v1_funct_1(k7_relat_1(B_168,A_169))
      | ~ v1_relat_1(k7_relat_1(B_168,A_169))
      | ~ v1_funct_1(A_170)
      | ~ v1_relat_1(A_170)
      | ~ v1_relat_1(B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1201])).

tff(c_48,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_357,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_48])).

tff(c_358,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_357])).

tff(c_4978,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) != k1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4972,c_358])).

tff(c_5066,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_36,c_501,c_174,c_456,c_4978])).

tff(c_5079,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_271,c_5066])).

tff(c_5083,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_5079])).

tff(c_5085,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_5233,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_5085,c_44])).

tff(c_14,plain,(
    ! [A_16,B_18] :
      ( k10_relat_1(A_16,k1_relat_1(B_18)) = k1_relat_1(k5_relat_1(A_16,B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5084,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_357])).

tff(c_46,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_5129,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_46])).

tff(c_5130,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5129])).

tff(c_5152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5085,c_5130])).

tff(c_5153,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_5129])).

tff(c_5318,plain,(
    ! [A_174,C_175,B_176] :
      ( r1_tarski(A_174,k10_relat_1(C_175,B_176))
      | ~ r1_tarski(k9_relat_1(C_175,A_174),B_176)
      | ~ r1_tarski(A_174,k1_relat_1(C_175))
      | ~ v1_funct_1(C_175)
      | ~ v1_relat_1(C_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5321,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_5153,c_5318])).

tff(c_5330,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_5084,c_5321])).

tff(c_5357,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_5330])).

tff(c_5360,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_5357])).

tff(c_5362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5233,c_5360])).

tff(c_5364,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_50,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_5405,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_5364,c_50])).

tff(c_5363,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_5471,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_5364,c_52])).

tff(c_6142,plain,(
    ! [A_213,C_214,B_215] :
      ( r1_tarski(A_213,k10_relat_1(C_214,B_215))
      | ~ r1_tarski(k9_relat_1(C_214,A_213),B_215)
      | ~ r1_tarski(A_213,k1_relat_1(C_214))
      | ~ v1_funct_1(C_214)
      | ~ v1_relat_1(C_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6157,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_5471,c_6142])).

tff(c_6174,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_5363,c_6157])).

tff(c_6180,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_6174])).

tff(c_6183,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_6180])).

tff(c_6185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5405,c_6183])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.50/2.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.50/2.35  
% 6.50/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.50/2.35  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.50/2.35  
% 6.50/2.35  %Foreground sorts:
% 6.50/2.35  
% 6.50/2.35  
% 6.50/2.35  %Background operators:
% 6.50/2.35  
% 6.50/2.35  
% 6.50/2.35  %Foreground operators:
% 6.50/2.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.50/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.50/2.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.50/2.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.50/2.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.50/2.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.50/2.35  tff('#skF_2', type, '#skF_2': $i).
% 6.50/2.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.50/2.35  tff('#skF_3', type, '#skF_3': $i).
% 6.50/2.35  tff('#skF_1', type, '#skF_1': $i).
% 6.50/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.50/2.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.50/2.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.50/2.35  tff('#skF_4', type, '#skF_4': $i).
% 6.50/2.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.50/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.50/2.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.50/2.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.50/2.35  
% 6.50/2.37  tff(f_138, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 6.50/2.37  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 6.50/2.37  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.50/2.37  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.50/2.37  tff(f_98, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 6.50/2.37  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 6.50/2.37  tff(f_94, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 6.50/2.37  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 6.50/2.37  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 6.50/2.37  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 6.50/2.37  tff(f_39, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 6.50/2.37  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 6.50/2.37  tff(f_121, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 6.50/2.37  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 6.50/2.37  tff(f_108, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 6.50/2.37  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.50/2.37  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.50/2.37  tff(c_16, plain, (![A_19, B_21]: (r1_tarski(k1_relat_1(k5_relat_1(A_19, B_21)), k1_relat_1(A_19)) | ~v1_relat_1(B_21) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.50/2.37  tff(c_54, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.50/2.37  tff(c_71, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_54])).
% 6.50/2.37  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.50/2.37  tff(c_75, plain, (k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_71, c_4])).
% 6.50/2.37  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.50/2.37  tff(c_139, plain, (![C_61]: (r1_tarski('#skF_4', C_61) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), C_61))), inference(superposition, [status(thm), theory('equality')], [c_75, c_2])).
% 6.50/2.37  tff(c_143, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_139])).
% 6.50/2.37  tff(c_146, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_143])).
% 6.50/2.37  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.50/2.37  tff(c_28, plain, (![A_29]: (v1_relat_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.50/2.37  tff(c_30, plain, (![A_29]: (v1_funct_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.50/2.37  tff(c_20, plain, (![A_24, B_25]: (k5_relat_1(k6_relat_1(A_24), B_25)=k7_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.50/2.37  tff(c_266, plain, (![A_68, B_69]: (v1_funct_1(k5_relat_1(A_68, B_69)) | ~v1_funct_1(B_69) | ~v1_relat_1(B_69) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.50/2.37  tff(c_269, plain, (![B_25, A_24]: (v1_funct_1(k7_relat_1(B_25, A_24)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25) | ~v1_funct_1(k6_relat_1(A_24)) | ~v1_relat_1(k6_relat_1(A_24)) | ~v1_relat_1(B_25))), inference(superposition, [status(thm), theory('equality')], [c_20, c_266])).
% 6.50/2.37  tff(c_271, plain, (![B_25, A_24]: (v1_funct_1(k7_relat_1(B_25, A_24)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_269])).
% 6.50/2.37  tff(c_36, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.50/2.37  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.50/2.37  tff(c_159, plain, (![B_63, A_64]: (k1_relat_1(k7_relat_1(B_63, A_64))=A_64 | ~r1_tarski(A_64, k1_relat_1(B_63)) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.50/2.37  tff(c_162, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_146, c_159])).
% 6.50/2.37  tff(c_174, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_162])).
% 6.50/2.37  tff(c_421, plain, (![B_73, C_74, A_75]: (k7_relat_1(k5_relat_1(B_73, C_74), A_75)=k5_relat_1(k7_relat_1(B_73, A_75), C_74) | ~v1_relat_1(C_74) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.50/2.37  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.50/2.37  tff(c_179, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4' | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_71, c_159])).
% 6.50/2.37  tff(c_256, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_179])).
% 6.50/2.37  tff(c_259, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_256])).
% 6.50/2.37  tff(c_263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_259])).
% 6.50/2.37  tff(c_264, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_179])).
% 6.50/2.37  tff(c_430, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_421, c_264])).
% 6.50/2.37  tff(c_456, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_430])).
% 6.50/2.37  tff(c_478, plain, (r1_tarski('#skF_4', k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_456, c_16])).
% 6.50/2.37  tff(c_490, plain, (r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_174, c_478])).
% 6.50/2.37  tff(c_492, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_490])).
% 6.50/2.37  tff(c_495, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_492])).
% 6.50/2.37  tff(c_499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_495])).
% 6.50/2.37  tff(c_501, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitRight, [status(thm)], [c_490])).
% 6.50/2.37  tff(c_12, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.50/2.37  tff(c_1201, plain, (![B_91, A_92]: (r1_tarski(k2_relat_1(B_91), k1_relat_1(A_92)) | k1_relat_1(k5_relat_1(B_91, A_92))!=k1_relat_1(B_91) | ~v1_funct_1(B_91) | ~v1_relat_1(B_91) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.50/2.37  tff(c_4972, plain, (![B_168, A_169, A_170]: (r1_tarski(k9_relat_1(B_168, A_169), k1_relat_1(A_170)) | k1_relat_1(k5_relat_1(k7_relat_1(B_168, A_169), A_170))!=k1_relat_1(k7_relat_1(B_168, A_169)) | ~v1_funct_1(k7_relat_1(B_168, A_169)) | ~v1_relat_1(k7_relat_1(B_168, A_169)) | ~v1_funct_1(A_170) | ~v1_relat_1(A_170) | ~v1_relat_1(B_168))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1201])).
% 6.50/2.37  tff(c_48, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.50/2.37  tff(c_357, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_48])).
% 6.50/2.37  tff(c_358, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_357])).
% 6.50/2.37  tff(c_4978, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))!=k1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_funct_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4972, c_358])).
% 6.50/2.37  tff(c_5066, plain, (~v1_funct_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_36, c_501, c_174, c_456, c_4978])).
% 6.50/2.37  tff(c_5079, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_271, c_5066])).
% 6.50/2.37  tff(c_5083, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_5079])).
% 6.50/2.37  tff(c_5085, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_357])).
% 6.50/2.37  tff(c_44, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.50/2.37  tff(c_5233, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_5085, c_44])).
% 6.50/2.37  tff(c_14, plain, (![A_16, B_18]: (k10_relat_1(A_16, k1_relat_1(B_18))=k1_relat_1(k5_relat_1(A_16, B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.50/2.37  tff(c_5084, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_357])).
% 6.50/2.37  tff(c_46, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.50/2.37  tff(c_5129, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_46])).
% 6.50/2.37  tff(c_5130, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_5129])).
% 6.50/2.37  tff(c_5152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5085, c_5130])).
% 6.50/2.37  tff(c_5153, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_5129])).
% 6.50/2.37  tff(c_5318, plain, (![A_174, C_175, B_176]: (r1_tarski(A_174, k10_relat_1(C_175, B_176)) | ~r1_tarski(k9_relat_1(C_175, A_174), B_176) | ~r1_tarski(A_174, k1_relat_1(C_175)) | ~v1_funct_1(C_175) | ~v1_relat_1(C_175))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.50/2.37  tff(c_5321, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_5153, c_5318])).
% 6.50/2.37  tff(c_5330, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_5084, c_5321])).
% 6.50/2.37  tff(c_5357, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_5330])).
% 6.50/2.37  tff(c_5360, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_5357])).
% 6.50/2.37  tff(c_5362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5233, c_5360])).
% 6.50/2.37  tff(c_5364, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_54])).
% 6.50/2.37  tff(c_50, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.50/2.37  tff(c_5405, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_5364, c_50])).
% 6.50/2.37  tff(c_5363, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_54])).
% 6.50/2.37  tff(c_52, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.50/2.37  tff(c_5471, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_5364, c_52])).
% 6.50/2.37  tff(c_6142, plain, (![A_213, C_214, B_215]: (r1_tarski(A_213, k10_relat_1(C_214, B_215)) | ~r1_tarski(k9_relat_1(C_214, A_213), B_215) | ~r1_tarski(A_213, k1_relat_1(C_214)) | ~v1_funct_1(C_214) | ~v1_relat_1(C_214))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.50/2.37  tff(c_6157, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_5471, c_6142])).
% 6.50/2.37  tff(c_6174, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_5363, c_6157])).
% 6.50/2.37  tff(c_6180, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_6174])).
% 6.50/2.37  tff(c_6183, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_6180])).
% 6.50/2.37  tff(c_6185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5405, c_6183])).
% 6.50/2.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.50/2.37  
% 6.50/2.37  Inference rules
% 6.50/2.37  ----------------------
% 6.50/2.37  #Ref     : 0
% 6.50/2.37  #Sup     : 1505
% 6.50/2.37  #Fact    : 0
% 6.50/2.37  #Define  : 0
% 6.50/2.37  #Split   : 10
% 6.50/2.37  #Chain   : 0
% 6.50/2.37  #Close   : 0
% 6.50/2.37  
% 6.50/2.37  Ordering : KBO
% 6.50/2.37  
% 6.50/2.37  Simplification rules
% 6.50/2.37  ----------------------
% 6.50/2.37  #Subsume      : 91
% 6.50/2.37  #Demod        : 1155
% 6.50/2.37  #Tautology    : 513
% 6.50/2.37  #SimpNegUnit  : 4
% 6.50/2.37  #BackRed      : 8
% 6.50/2.37  
% 6.50/2.37  #Partial instantiations: 0
% 6.50/2.37  #Strategies tried      : 1
% 6.50/2.37  
% 6.50/2.37  Timing (in seconds)
% 6.50/2.37  ----------------------
% 6.50/2.37  Preprocessing        : 0.34
% 6.50/2.37  Parsing              : 0.19
% 6.50/2.37  CNF conversion       : 0.02
% 6.50/2.37  Main loop            : 1.21
% 6.50/2.37  Inferencing          : 0.37
% 6.50/2.37  Reduction            : 0.46
% 6.50/2.37  Demodulation         : 0.35
% 6.50/2.37  BG Simplification    : 0.05
% 6.50/2.37  Subsumption          : 0.25
% 6.50/2.37  Abstraction          : 0.06
% 6.50/2.37  MUC search           : 0.00
% 6.50/2.37  Cooper               : 0.00
% 6.50/2.37  Total                : 1.59
% 6.50/2.37  Index Insertion      : 0.00
% 6.50/2.37  Index Deletion       : 0.00
% 6.50/2.37  Index Matching       : 0.00
% 6.50/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
