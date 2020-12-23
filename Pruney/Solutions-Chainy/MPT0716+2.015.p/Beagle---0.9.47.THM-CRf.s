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
% DateTime   : Thu Dec  3 10:05:38 EST 2020

% Result     : Theorem 5.44s
% Output     : CNFRefutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 752 expanded)
%              Number of leaves         :   34 ( 263 expanded)
%              Depth                    :   18
%              Number of atoms          :  219 (2118 expanded)
%              Number of equality atoms :   26 ( 214 expanded)
%              Maximal formula depth    :    9 (   3 average)
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

tff(f_131,negated_conjecture,(
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

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

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

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_127,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_59,B_60)),k1_relat_1(A_59))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_54,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

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

tff(c_121,plain,(
    ! [C_3] :
      ( r1_tarski('#skF_4',C_3)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_1','#skF_2')),C_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_2])).

tff(c_131,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_127,c_121])).

tff(c_140,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_131])).

tff(c_48,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_349,plain,
    ( r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_48])).

tff(c_350,plain,(
    ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_12,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

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

tff(c_261,plain,(
    ! [A_67,B_68] :
      ( v1_funct_1(k5_relat_1(A_67,B_68))
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_264,plain,(
    ! [B_25,A_24] :
      ( v1_funct_1(k7_relat_1(B_25,A_24))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_funct_1(k6_relat_1(A_24))
      | ~ v1_relat_1(k6_relat_1(A_24))
      | ~ v1_relat_1(B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_261])).

tff(c_266,plain,(
    ! [B_25,A_24] :
      ( v1_funct_1(k7_relat_1(B_25,A_24))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_264])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_164,plain,(
    ! [B_64,A_65] :
      ( k1_relat_1(k7_relat_1(B_64,A_65)) = A_65
      | ~ r1_tarski(A_65,k1_relat_1(B_64))
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_170,plain,
    ( k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_140,c_164])).

tff(c_186,plain,(
    k1_relat_1(k7_relat_1('#skF_1','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_170])).

tff(c_761,plain,(
    ! [B_77,C_78,A_79] :
      ( k7_relat_1(k5_relat_1(B_77,C_78),A_79) = k5_relat_1(k7_relat_1(B_77,A_79),C_78)
      | ~ v1_relat_1(C_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k5_relat_1(A_6,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_189,plain,
    ( k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4'
    | ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_71,c_164])).

tff(c_251,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_189])).

tff(c_254,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_251])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_254])).

tff(c_259,plain,(
    k1_relat_1(k7_relat_1(k5_relat_1('#skF_1','#skF_2'),'#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_189])).

tff(c_770,plain,
    ( k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_259])).

tff(c_796,plain,(
    k1_relat_1(k5_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_770])).

tff(c_16,plain,(
    ! [A_19,B_21] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_19,B_21)),k1_relat_1(A_19))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_821,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k7_relat_1('#skF_1','#skF_4')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_16])).

tff(c_838,plain,
    ( r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_186,c_821])).

tff(c_840,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_838])).

tff(c_843,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_840])).

tff(c_847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_843])).

tff(c_849,plain,(
    v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_838])).

tff(c_22,plain,(
    ! [A_26] :
      ( k7_relat_1(A_26,k1_relat_1(A_26)) = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_205,plain,
    ( k7_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_4') = k7_relat_1('#skF_1','#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_22])).

tff(c_879,plain,(
    k7_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_4') = k7_relat_1('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_205])).

tff(c_889,plain,
    ( k9_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_4') = k2_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_879,c_12])).

tff(c_900,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_4') = k2_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_889])).

tff(c_410,plain,(
    ! [A_72,B_73] :
      ( k10_relat_1(A_72,k1_relat_1(B_73)) = k1_relat_1(k5_relat_1(A_72,B_73))
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_32,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k9_relat_1(B_31,k10_relat_1(B_31,A_30)),A_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2420,plain,(
    ! [A_125,B_126] :
      ( r1_tarski(k9_relat_1(A_125,k1_relat_1(k5_relat_1(A_125,B_126))),k1_relat_1(B_126))
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125)
      | ~ v1_relat_1(B_126)
      | ~ v1_relat_1(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_410,c_32])).

tff(c_2456,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1('#skF_1','#skF_4'),'#skF_4'),k1_relat_1('#skF_2'))
    | ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_2420])).

tff(c_2490,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1('#skF_1','#skF_4')),k1_relat_1('#skF_2'))
    | ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_38,c_849,c_900,c_2456])).

tff(c_2507,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_1','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2490])).

tff(c_2510,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_266,c_2507])).

tff(c_2514,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2510])).

tff(c_2515,plain,(
    r1_tarski(k2_relat_1(k7_relat_1('#skF_1','#skF_4')),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2490])).

tff(c_2622,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2515])).

tff(c_2628,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2622])).

tff(c_2630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_350,c_2628])).

tff(c_2632,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2941,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_2632,c_44])).

tff(c_14,plain,(
    ! [A_16,B_18] :
      ( k10_relat_1(A_16,k1_relat_1(B_18)) = k1_relat_1(k5_relat_1(A_16,B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2631,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_46,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_1','#skF_4'),k1_relat_1('#skF_2'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2734,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_2632,c_46])).

tff(c_2973,plain,(
    ! [A_134,C_135,B_136] :
      ( r1_tarski(A_134,k10_relat_1(C_135,B_136))
      | ~ r1_tarski(k9_relat_1(C_135,A_134),B_136)
      | ~ r1_tarski(A_134,k1_relat_1(C_135))
      | ~ v1_funct_1(C_135)
      | ~ v1_relat_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2976,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2734,c_2973])).

tff(c_2988,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_2631,c_2976])).

tff(c_2998,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_2988])).

tff(c_3001,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_2998])).

tff(c_3003,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2941,c_3001])).

tff(c_3005,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_50,plain,
    ( ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3072,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3005,c_50])).

tff(c_3004,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,
    ( r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2'))
    | r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3010,plain,(
    r1_tarski(k9_relat_1('#skF_1','#skF_3'),k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_3005,c_52])).

tff(c_3987,plain,(
    ! [A_181,C_182,B_183] :
      ( r1_tarski(A_181,k10_relat_1(C_182,B_183))
      | ~ r1_tarski(k9_relat_1(C_182,A_181),B_183)
      | ~ r1_tarski(A_181,k1_relat_1(C_182))
      | ~ v1_funct_1(C_182)
      | ~ v1_relat_1(C_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4012,plain,
    ( r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3010,c_3987])).

tff(c_4028,plain,(
    r1_tarski('#skF_3',k10_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_3004,c_4012])).

tff(c_4034,plain,
    ( r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_4028])).

tff(c_4037,plain,(
    r1_tarski('#skF_3',k1_relat_1(k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_4034])).

tff(c_4039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3072,c_4037])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.44/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.44/2.03  
% 5.44/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.44/2.03  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.44/2.03  
% 5.44/2.03  %Foreground sorts:
% 5.44/2.03  
% 5.44/2.03  
% 5.44/2.03  %Background operators:
% 5.44/2.03  
% 5.44/2.03  
% 5.44/2.03  %Foreground operators:
% 5.44/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.44/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.44/2.03  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.44/2.03  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 5.44/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.44/2.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.44/2.03  tff('#skF_2', type, '#skF_2': $i).
% 5.44/2.03  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.44/2.03  tff('#skF_3', type, '#skF_3': $i).
% 5.44/2.03  tff('#skF_1', type, '#skF_1': $i).
% 5.44/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.44/2.03  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.44/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.44/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.44/2.03  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.44/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.44/2.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.44/2.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.44/2.03  
% 5.44/2.05  tff(f_131, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_funct_1)).
% 5.44/2.05  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 5.44/2.05  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.44/2.05  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.44/2.05  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 5.44/2.05  tff(f_98, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 5.44/2.05  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 5.44/2.05  tff(f_94, axiom, (![A, B]: ((((v1_relat_1(A) & v1_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v1_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_funct_1)).
% 5.44/2.05  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.44/2.05  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 5.44/2.05  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 5.44/2.05  tff(f_39, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 5.44/2.05  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 5.44/2.05  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 5.44/2.05  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 5.44/2.05  tff(f_114, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 5.44/2.05  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.44/2.05  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.44/2.05  tff(c_127, plain, (![A_59, B_60]: (r1_tarski(k1_relat_1(k5_relat_1(A_59, B_60)), k1_relat_1(A_59)) | ~v1_relat_1(B_60) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.44/2.05  tff(c_54, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.44/2.05  tff(c_71, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_54])).
% 5.44/2.05  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.44/2.05  tff(c_75, plain, (k2_xboole_0('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_71, c_4])).
% 5.44/2.05  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.44/2.05  tff(c_121, plain, (![C_3]: (r1_tarski('#skF_4', C_3) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_1', '#skF_2')), C_3))), inference(superposition, [status(thm), theory('equality')], [c_75, c_2])).
% 5.44/2.05  tff(c_131, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_127, c_121])).
% 5.44/2.05  tff(c_140, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_131])).
% 5.44/2.05  tff(c_48, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.44/2.05  tff(c_349, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_48])).
% 5.44/2.05  tff(c_350, plain, (~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_349])).
% 5.44/2.05  tff(c_12, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.44/2.05  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.44/2.05  tff(c_28, plain, (![A_29]: (v1_relat_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.44/2.05  tff(c_30, plain, (![A_29]: (v1_funct_1(k6_relat_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.44/2.05  tff(c_20, plain, (![A_24, B_25]: (k5_relat_1(k6_relat_1(A_24), B_25)=k7_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.44/2.05  tff(c_261, plain, (![A_67, B_68]: (v1_funct_1(k5_relat_1(A_67, B_68)) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.44/2.05  tff(c_264, plain, (![B_25, A_24]: (v1_funct_1(k7_relat_1(B_25, A_24)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25) | ~v1_funct_1(k6_relat_1(A_24)) | ~v1_relat_1(k6_relat_1(A_24)) | ~v1_relat_1(B_25))), inference(superposition, [status(thm), theory('equality')], [c_20, c_261])).
% 5.44/2.05  tff(c_266, plain, (![B_25, A_24]: (v1_funct_1(k7_relat_1(B_25, A_24)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_264])).
% 5.44/2.05  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.44/2.05  tff(c_164, plain, (![B_64, A_65]: (k1_relat_1(k7_relat_1(B_64, A_65))=A_65 | ~r1_tarski(A_65, k1_relat_1(B_64)) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.44/2.05  tff(c_170, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_140, c_164])).
% 5.44/2.05  tff(c_186, plain, (k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_170])).
% 5.44/2.05  tff(c_761, plain, (![B_77, C_78, A_79]: (k7_relat_1(k5_relat_1(B_77, C_78), A_79)=k5_relat_1(k7_relat_1(B_77, A_79), C_78) | ~v1_relat_1(C_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.44/2.05  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k5_relat_1(A_6, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.44/2.05  tff(c_189, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4' | ~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_71, c_164])).
% 5.44/2.05  tff(c_251, plain, (~v1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_189])).
% 5.44/2.05  tff(c_254, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_251])).
% 5.44/2.05  tff(c_258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_254])).
% 5.44/2.05  tff(c_259, plain, (k1_relat_1(k7_relat_1(k5_relat_1('#skF_1', '#skF_2'), '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_189])).
% 5.44/2.05  tff(c_770, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_761, c_259])).
% 5.44/2.05  tff(c_796, plain, (k1_relat_1(k5_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_770])).
% 5.44/2.05  tff(c_16, plain, (![A_19, B_21]: (r1_tarski(k1_relat_1(k5_relat_1(A_19, B_21)), k1_relat_1(A_19)) | ~v1_relat_1(B_21) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.44/2.05  tff(c_821, plain, (r1_tarski('#skF_4', k1_relat_1(k7_relat_1('#skF_1', '#skF_4'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_796, c_16])).
% 5.44/2.05  tff(c_838, plain, (r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_186, c_821])).
% 5.44/2.05  tff(c_840, plain, (~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_838])).
% 5.44/2.05  tff(c_843, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_8, c_840])).
% 5.44/2.05  tff(c_847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_843])).
% 5.44/2.05  tff(c_849, plain, (v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitRight, [status(thm)], [c_838])).
% 5.44/2.05  tff(c_22, plain, (![A_26]: (k7_relat_1(A_26, k1_relat_1(A_26))=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.44/2.05  tff(c_205, plain, (k7_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_4')=k7_relat_1('#skF_1', '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_22])).
% 5.44/2.05  tff(c_879, plain, (k7_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_4')=k7_relat_1('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_849, c_205])).
% 5.44/2.05  tff(c_889, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_4')=k2_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_879, c_12])).
% 5.44/2.05  tff(c_900, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_4')=k2_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_849, c_889])).
% 5.44/2.05  tff(c_410, plain, (![A_72, B_73]: (k10_relat_1(A_72, k1_relat_1(B_73))=k1_relat_1(k5_relat_1(A_72, B_73)) | ~v1_relat_1(B_73) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.44/2.05  tff(c_32, plain, (![B_31, A_30]: (r1_tarski(k9_relat_1(B_31, k10_relat_1(B_31, A_30)), A_30) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.44/2.05  tff(c_2420, plain, (![A_125, B_126]: (r1_tarski(k9_relat_1(A_125, k1_relat_1(k5_relat_1(A_125, B_126))), k1_relat_1(B_126)) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125) | ~v1_relat_1(B_126) | ~v1_relat_1(A_125))), inference(superposition, [status(thm), theory('equality')], [c_410, c_32])).
% 5.44/2.05  tff(c_2456, plain, (r1_tarski(k9_relat_1(k7_relat_1('#skF_1', '#skF_4'), '#skF_4'), k1_relat_1('#skF_2')) | ~v1_funct_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_1', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_796, c_2420])).
% 5.44/2.05  tff(c_2490, plain, (r1_tarski(k2_relat_1(k7_relat_1('#skF_1', '#skF_4')), k1_relat_1('#skF_2')) | ~v1_funct_1(k7_relat_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_849, c_38, c_849, c_900, c_2456])).
% 5.44/2.05  tff(c_2507, plain, (~v1_funct_1(k7_relat_1('#skF_1', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2490])).
% 5.44/2.05  tff(c_2510, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_266, c_2507])).
% 5.44/2.05  tff(c_2514, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2510])).
% 5.44/2.05  tff(c_2515, plain, (r1_tarski(k2_relat_1(k7_relat_1('#skF_1', '#skF_4')), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_2490])).
% 5.44/2.05  tff(c_2622, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12, c_2515])).
% 5.44/2.05  tff(c_2628, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2622])).
% 5.44/2.05  tff(c_2630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_350, c_2628])).
% 5.44/2.05  tff(c_2632, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_349])).
% 5.44/2.05  tff(c_44, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.44/2.05  tff(c_2941, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_2632, c_44])).
% 5.44/2.05  tff(c_14, plain, (![A_16, B_18]: (k10_relat_1(A_16, k1_relat_1(B_18))=k1_relat_1(k5_relat_1(A_16, B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.44/2.05  tff(c_2631, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_349])).
% 5.44/2.05  tff(c_46, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_1', '#skF_4'), k1_relat_1('#skF_2')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.44/2.05  tff(c_2734, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_2632, c_46])).
% 5.44/2.05  tff(c_2973, plain, (![A_134, C_135, B_136]: (r1_tarski(A_134, k10_relat_1(C_135, B_136)) | ~r1_tarski(k9_relat_1(C_135, A_134), B_136) | ~r1_tarski(A_134, k1_relat_1(C_135)) | ~v1_funct_1(C_135) | ~v1_relat_1(C_135))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.44/2.05  tff(c_2976, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2734, c_2973])).
% 5.44/2.05  tff(c_2988, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_2631, c_2976])).
% 5.44/2.05  tff(c_2998, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_2988])).
% 5.44/2.05  tff(c_3001, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_2998])).
% 5.44/2.05  tff(c_3003, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2941, c_3001])).
% 5.44/2.05  tff(c_3005, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_54])).
% 5.44/2.05  tff(c_50, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.44/2.05  tff(c_3072, plain, (~r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_3005, c_50])).
% 5.44/2.05  tff(c_3004, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_54])).
% 5.44/2.05  tff(c_52, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2')) | r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.44/2.05  tff(c_3010, plain, (r1_tarski(k9_relat_1('#skF_1', '#skF_3'), k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_3005, c_52])).
% 5.44/2.05  tff(c_3987, plain, (![A_181, C_182, B_183]: (r1_tarski(A_181, k10_relat_1(C_182, B_183)) | ~r1_tarski(k9_relat_1(C_182, A_181), B_183) | ~r1_tarski(A_181, k1_relat_1(C_182)) | ~v1_funct_1(C_182) | ~v1_relat_1(C_182))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.44/2.05  tff(c_4012, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~r1_tarski('#skF_3', k1_relat_1('#skF_1')) | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3010, c_3987])).
% 5.44/2.05  tff(c_4028, plain, (r1_tarski('#skF_3', k10_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_3004, c_4012])).
% 5.44/2.05  tff(c_4034, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_4028])).
% 5.44/2.05  tff(c_4037, plain, (r1_tarski('#skF_3', k1_relat_1(k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_4034])).
% 5.44/2.05  tff(c_4039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3072, c_4037])).
% 5.44/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.44/2.05  
% 5.44/2.05  Inference rules
% 5.44/2.05  ----------------------
% 5.44/2.05  #Ref     : 0
% 5.44/2.05  #Sup     : 975
% 5.44/2.05  #Fact    : 0
% 5.44/2.05  #Define  : 0
% 5.44/2.05  #Split   : 10
% 5.44/2.05  #Chain   : 0
% 5.44/2.05  #Close   : 0
% 5.44/2.05  
% 5.44/2.05  Ordering : KBO
% 5.44/2.05  
% 5.44/2.05  Simplification rules
% 5.44/2.05  ----------------------
% 5.44/2.05  #Subsume      : 48
% 5.44/2.05  #Demod        : 708
% 5.44/2.05  #Tautology    : 380
% 5.44/2.05  #SimpNegUnit  : 5
% 5.44/2.05  #BackRed      : 4
% 5.44/2.05  
% 5.44/2.05  #Partial instantiations: 0
% 5.44/2.05  #Strategies tried      : 1
% 5.44/2.05  
% 5.44/2.05  Timing (in seconds)
% 5.44/2.05  ----------------------
% 5.44/2.05  Preprocessing        : 0.34
% 5.44/2.05  Parsing              : 0.18
% 5.44/2.05  CNF conversion       : 0.02
% 5.44/2.05  Main loop            : 0.97
% 5.44/2.05  Inferencing          : 0.32
% 5.44/2.05  Reduction            : 0.36
% 5.44/2.05  Demodulation         : 0.27
% 5.44/2.05  BG Simplification    : 0.04
% 5.44/2.05  Subsumption          : 0.18
% 5.44/2.05  Abstraction          : 0.05
% 5.44/2.05  MUC search           : 0.00
% 5.44/2.05  Cooper               : 0.00
% 5.44/2.05  Total                : 1.34
% 5.44/2.05  Index Insertion      : 0.00
% 5.44/2.05  Index Deletion       : 0.00
% 5.44/2.06  Index Matching       : 0.00
% 5.44/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
