%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:31 EST 2020

% Result     : Theorem 6.01s
% Output     : CNFRefutation 6.01s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 251 expanded)
%              Number of leaves         :   21 (  98 expanded)
%              Depth                    :   13
%              Number of atoms          :  139 ( 769 expanded)
%              Number of equality atoms :   45 ( 300 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( k1_relat_1(A) = k1_relat_1(B)
                  & ! [D] :
                      ( r2_hidden(D,C)
                     => k1_funct_1(A,D) = k1_funct_1(B,D) ) )
               => k7_relat_1(A,C) = k7_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ! [C] :
              ( ( r1_tarski(C,k1_relat_1(A))
                & r1_tarski(C,k1_relat_1(B)) )
             => ( k7_relat_1(A,C) = k7_relat_1(B,C)
              <=> ! [D] :
                    ( r2_hidden(D,C)
                   => k1_funct_1(A,D) = k1_funct_1(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t165_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_20,plain,(
    k7_relat_1('#skF_2','#skF_4') != k7_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    k1_relat_1('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_45,plain,(
    ! [B_48,A_49] :
      ( k3_xboole_0(k1_relat_1(B_48),A_49) = k1_relat_1(k7_relat_1(B_48,A_49))
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    ! [A_49] :
      ( k3_xboole_0(k1_relat_1('#skF_3'),A_49) = k1_relat_1(k7_relat_1('#skF_2',A_49))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_45])).

tff(c_59,plain,(
    ! [A_50] : k3_xboole_0(k1_relat_1('#skF_3'),A_50) = k1_relat_1(k7_relat_1('#skF_2',A_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_54])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k3_xboole_0(k1_relat_1(B_9),A_8) = k1_relat_1(k7_relat_1(B_9,A_8))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_65,plain,(
    ! [A_50] :
      ( k1_relat_1(k7_relat_1('#skF_2',A_50)) = k1_relat_1(k7_relat_1('#skF_3',A_50))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_12])).

tff(c_75,plain,(
    ! [A_50] : k1_relat_1(k7_relat_1('#skF_2',A_50)) = k1_relat_1(k7_relat_1('#skF_3',A_50)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_65])).

tff(c_38,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_45,A_46)),k1_relat_1(B_45))
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_41,plain,(
    ! [A_46] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_2',A_46)),k1_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_38])).

tff(c_43,plain,(
    ! [A_46] : r1_tarski(k1_relat_1(k7_relat_1('#skF_2',A_46)),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_41])).

tff(c_80,plain,(
    ! [A_46] : r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_46)),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_43])).

tff(c_58,plain,(
    ! [A_49] : k3_xboole_0(k1_relat_1('#skF_3'),A_49) = k1_relat_1(k7_relat_1('#skF_2',A_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_54])).

tff(c_139,plain,(
    ! [A_55] : k3_xboole_0(k1_relat_1('#skF_3'),A_55) = k1_relat_1(k7_relat_1('#skF_3',A_55)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_58])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k7_relat_1(B_2,k3_xboole_0(k1_relat_1(B_2),A_1)) = k7_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_145,plain,(
    ! [A_55] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3',A_55))) = k7_relat_1('#skF_3',A_55)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_2])).

tff(c_158,plain,(
    ! [A_55] : k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3',A_55))) = k7_relat_1('#skF_3',A_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_145])).

tff(c_79,plain,(
    ! [A_49] : k3_xboole_0(k1_relat_1('#skF_3'),A_49) = k1_relat_1(k7_relat_1('#skF_3',A_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_58])).

tff(c_104,plain,(
    ! [B_53,A_54] :
      ( k7_relat_1(B_53,k3_xboole_0(k1_relat_1(B_53),A_54)) = k7_relat_1(B_53,A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_130,plain,(
    ! [A_54] :
      ( k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_3'),A_54)) = k7_relat_1('#skF_2',A_54)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_104])).

tff(c_138,plain,(
    ! [A_54] : k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_3'),A_54)) = k7_relat_1('#skF_2',A_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_130])).

tff(c_166,plain,(
    ! [A_54] : k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3',A_54))) = k7_relat_1('#skF_2',A_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_138])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,A_6)),k1_relat_1(B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_749,plain,(
    ! [A_86,B_87,C_88] :
      ( r2_hidden('#skF_1'(A_86,B_87,C_88),C_88)
      | k7_relat_1(B_87,C_88) = k7_relat_1(A_86,C_88)
      | ~ r1_tarski(C_88,k1_relat_1(B_87))
      | ~ r1_tarski(C_88,k1_relat_1(A_86))
      | ~ v1_funct_1(B_87)
      | ~ v1_relat_1(B_87)
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden(A_3,B_4)
      | ~ r2_hidden(A_3,k1_relat_1(k7_relat_1(C_5,B_4)))
      | ~ v1_relat_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1983,plain,(
    ! [A_138,B_139,C_140,B_141] :
      ( r2_hidden('#skF_1'(A_138,B_139,k1_relat_1(k7_relat_1(C_140,B_141))),B_141)
      | ~ v1_relat_1(C_140)
      | k7_relat_1(B_139,k1_relat_1(k7_relat_1(C_140,B_141))) = k7_relat_1(A_138,k1_relat_1(k7_relat_1(C_140,B_141)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_140,B_141)),k1_relat_1(B_139))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_140,B_141)),k1_relat_1(A_138))
      | ~ v1_funct_1(B_139)
      | ~ v1_relat_1(B_139)
      | ~ v1_funct_1(A_138)
      | ~ v1_relat_1(A_138) ) ),
    inference(resolution,[status(thm)],[c_749,c_8])).

tff(c_22,plain,(
    ! [D_43] :
      ( k1_funct_1('#skF_2',D_43) = k1_funct_1('#skF_3',D_43)
      | ~ r2_hidden(D_43,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2303,plain,(
    ! [A_151,B_152,C_153] :
      ( k1_funct_1('#skF_2','#skF_1'(A_151,B_152,k1_relat_1(k7_relat_1(C_153,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'(A_151,B_152,k1_relat_1(k7_relat_1(C_153,'#skF_4'))))
      | ~ v1_relat_1(C_153)
      | k7_relat_1(B_152,k1_relat_1(k7_relat_1(C_153,'#skF_4'))) = k7_relat_1(A_151,k1_relat_1(k7_relat_1(C_153,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_153,'#skF_4')),k1_relat_1(B_152))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_153,'#skF_4')),k1_relat_1(A_151))
      | ~ v1_funct_1(B_152)
      | ~ v1_relat_1(B_152)
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(resolution,[status(thm)],[c_1983,c_22])).

tff(c_3177,plain,(
    ! [A_179,B_180] :
      ( k1_funct_1('#skF_2','#skF_1'(A_179,B_180,k1_relat_1(k7_relat_1(B_180,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'(A_179,B_180,k1_relat_1(k7_relat_1(B_180,'#skF_4'))))
      | k7_relat_1(B_180,k1_relat_1(k7_relat_1(B_180,'#skF_4'))) = k7_relat_1(A_179,k1_relat_1(k7_relat_1(B_180,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_180,'#skF_4')),k1_relat_1(A_179))
      | ~ v1_funct_1(B_180)
      | ~ v1_funct_1(A_179)
      | ~ v1_relat_1(A_179)
      | ~ v1_relat_1(B_180) ) ),
    inference(resolution,[status(thm)],[c_10,c_2303])).

tff(c_3203,plain,(
    ! [B_180] :
      ( k1_funct_1('#skF_2','#skF_1'('#skF_2',B_180,k1_relat_1(k7_relat_1(B_180,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2',B_180,k1_relat_1(k7_relat_1(B_180,'#skF_4'))))
      | k7_relat_1(B_180,k1_relat_1(k7_relat_1(B_180,'#skF_4'))) = k7_relat_1('#skF_2',k1_relat_1(k7_relat_1(B_180,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_180,'#skF_4')),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(B_180)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(B_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3177])).

tff(c_3614,plain,(
    ! [B_190] :
      ( k1_funct_1('#skF_2','#skF_1'('#skF_2',B_190,k1_relat_1(k7_relat_1(B_190,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2',B_190,k1_relat_1(k7_relat_1(B_190,'#skF_4'))))
      | k7_relat_1(B_190,k1_relat_1(k7_relat_1(B_190,'#skF_4'))) = k7_relat_1('#skF_2',k1_relat_1(k7_relat_1(B_190,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_190,'#skF_4')),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(B_190)
      | ~ v1_relat_1(B_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_3203])).

tff(c_3620,plain,
    ( k1_funct_1('#skF_2','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))))
    | k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))) = k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_3614])).

tff(c_3629,plain,
    ( k1_funct_1('#skF_2','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))))
    | k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_158,c_166,c_3620])).

tff(c_3630,plain,(
    k1_funct_1('#skF_2','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_3629])).

tff(c_16,plain,(
    ! [B_22,A_10,C_28] :
      ( k1_funct_1(B_22,'#skF_1'(A_10,B_22,C_28)) != k1_funct_1(A_10,'#skF_1'(A_10,B_22,C_28))
      | k7_relat_1(B_22,C_28) = k7_relat_1(A_10,C_28)
      | ~ r1_tarski(C_28,k1_relat_1(B_22))
      | ~ r1_tarski(C_28,k1_relat_1(A_10))
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3639,plain,
    ( k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))) = k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_4')),k1_relat_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_4')),k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3630,c_16])).

tff(c_3644,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_26,c_80,c_24,c_80,c_158,c_166,c_3639])).

tff(c_3646,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_3644])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:56:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.01/2.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.16  
% 6.01/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.16  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 6.01/2.16  
% 6.01/2.16  %Foreground sorts:
% 6.01/2.16  
% 6.01/2.16  
% 6.01/2.16  %Background operators:
% 6.01/2.16  
% 6.01/2.16  
% 6.01/2.16  %Foreground operators:
% 6.01/2.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.01/2.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.01/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.01/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.01/2.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.01/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.01/2.16  tff('#skF_2', type, '#skF_2': $i).
% 6.01/2.16  tff('#skF_3', type, '#skF_3': $i).
% 6.01/2.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.01/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.01/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.01/2.16  tff('#skF_4', type, '#skF_4': $i).
% 6.01/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.01/2.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.01/2.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.01/2.16  
% 6.01/2.19  tff(f_86, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (((k1_relat_1(A) = k1_relat_1(B)) & (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))) => (k7_relat_1(A, C) = k7_relat_1(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_funct_1)).
% 6.01/2.19  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 6.01/2.19  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 6.01/2.19  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 6.01/2.19  tff(f_66, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((r1_tarski(C, k1_relat_1(A)) & r1_tarski(C, k1_relat_1(B))) => ((k7_relat_1(A, C) = k7_relat_1(B, C)) <=> (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t165_funct_1)).
% 6.01/2.19  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 6.01/2.19  tff(c_20, plain, (k7_relat_1('#skF_2', '#skF_4')!=k7_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.01/2.19  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.01/2.19  tff(c_30, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.01/2.19  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.01/2.19  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.01/2.19  tff(c_24, plain, (k1_relat_1('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.01/2.19  tff(c_45, plain, (![B_48, A_49]: (k3_xboole_0(k1_relat_1(B_48), A_49)=k1_relat_1(k7_relat_1(B_48, A_49)) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.01/2.19  tff(c_54, plain, (![A_49]: (k3_xboole_0(k1_relat_1('#skF_3'), A_49)=k1_relat_1(k7_relat_1('#skF_2', A_49)) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_45])).
% 6.01/2.19  tff(c_59, plain, (![A_50]: (k3_xboole_0(k1_relat_1('#skF_3'), A_50)=k1_relat_1(k7_relat_1('#skF_2', A_50)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_54])).
% 6.01/2.19  tff(c_12, plain, (![B_9, A_8]: (k3_xboole_0(k1_relat_1(B_9), A_8)=k1_relat_1(k7_relat_1(B_9, A_8)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.01/2.19  tff(c_65, plain, (![A_50]: (k1_relat_1(k7_relat_1('#skF_2', A_50))=k1_relat_1(k7_relat_1('#skF_3', A_50)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_59, c_12])).
% 6.01/2.19  tff(c_75, plain, (![A_50]: (k1_relat_1(k7_relat_1('#skF_2', A_50))=k1_relat_1(k7_relat_1('#skF_3', A_50)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_65])).
% 6.01/2.19  tff(c_38, plain, (![B_45, A_46]: (r1_tarski(k1_relat_1(k7_relat_1(B_45, A_46)), k1_relat_1(B_45)) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.01/2.19  tff(c_41, plain, (![A_46]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_2', A_46)), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_38])).
% 6.01/2.19  tff(c_43, plain, (![A_46]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_2', A_46)), k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_41])).
% 6.01/2.19  tff(c_80, plain, (![A_46]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_46)), k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_43])).
% 6.01/2.19  tff(c_58, plain, (![A_49]: (k3_xboole_0(k1_relat_1('#skF_3'), A_49)=k1_relat_1(k7_relat_1('#skF_2', A_49)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_54])).
% 6.01/2.19  tff(c_139, plain, (![A_55]: (k3_xboole_0(k1_relat_1('#skF_3'), A_55)=k1_relat_1(k7_relat_1('#skF_3', A_55)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_58])).
% 6.01/2.19  tff(c_2, plain, (![B_2, A_1]: (k7_relat_1(B_2, k3_xboole_0(k1_relat_1(B_2), A_1))=k7_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.01/2.19  tff(c_145, plain, (![A_55]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', A_55)))=k7_relat_1('#skF_3', A_55) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_139, c_2])).
% 6.01/2.19  tff(c_158, plain, (![A_55]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', A_55)))=k7_relat_1('#skF_3', A_55))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_145])).
% 6.01/2.19  tff(c_79, plain, (![A_49]: (k3_xboole_0(k1_relat_1('#skF_3'), A_49)=k1_relat_1(k7_relat_1('#skF_3', A_49)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_58])).
% 6.01/2.19  tff(c_104, plain, (![B_53, A_54]: (k7_relat_1(B_53, k3_xboole_0(k1_relat_1(B_53), A_54))=k7_relat_1(B_53, A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.01/2.19  tff(c_130, plain, (![A_54]: (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_3'), A_54))=k7_relat_1('#skF_2', A_54) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_104])).
% 6.01/2.19  tff(c_138, plain, (![A_54]: (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_3'), A_54))=k7_relat_1('#skF_2', A_54))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_130])).
% 6.01/2.19  tff(c_166, plain, (![A_54]: (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', A_54)))=k7_relat_1('#skF_2', A_54))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_138])).
% 6.01/2.19  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, A_6)), k1_relat_1(B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.01/2.19  tff(c_749, plain, (![A_86, B_87, C_88]: (r2_hidden('#skF_1'(A_86, B_87, C_88), C_88) | k7_relat_1(B_87, C_88)=k7_relat_1(A_86, C_88) | ~r1_tarski(C_88, k1_relat_1(B_87)) | ~r1_tarski(C_88, k1_relat_1(A_86)) | ~v1_funct_1(B_87) | ~v1_relat_1(B_87) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.01/2.19  tff(c_8, plain, (![A_3, B_4, C_5]: (r2_hidden(A_3, B_4) | ~r2_hidden(A_3, k1_relat_1(k7_relat_1(C_5, B_4))) | ~v1_relat_1(C_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.01/2.19  tff(c_1983, plain, (![A_138, B_139, C_140, B_141]: (r2_hidden('#skF_1'(A_138, B_139, k1_relat_1(k7_relat_1(C_140, B_141))), B_141) | ~v1_relat_1(C_140) | k7_relat_1(B_139, k1_relat_1(k7_relat_1(C_140, B_141)))=k7_relat_1(A_138, k1_relat_1(k7_relat_1(C_140, B_141))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_140, B_141)), k1_relat_1(B_139)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_140, B_141)), k1_relat_1(A_138)) | ~v1_funct_1(B_139) | ~v1_relat_1(B_139) | ~v1_funct_1(A_138) | ~v1_relat_1(A_138))), inference(resolution, [status(thm)], [c_749, c_8])).
% 6.01/2.19  tff(c_22, plain, (![D_43]: (k1_funct_1('#skF_2', D_43)=k1_funct_1('#skF_3', D_43) | ~r2_hidden(D_43, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.01/2.19  tff(c_2303, plain, (![A_151, B_152, C_153]: (k1_funct_1('#skF_2', '#skF_1'(A_151, B_152, k1_relat_1(k7_relat_1(C_153, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'(A_151, B_152, k1_relat_1(k7_relat_1(C_153, '#skF_4')))) | ~v1_relat_1(C_153) | k7_relat_1(B_152, k1_relat_1(k7_relat_1(C_153, '#skF_4')))=k7_relat_1(A_151, k1_relat_1(k7_relat_1(C_153, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_153, '#skF_4')), k1_relat_1(B_152)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_153, '#skF_4')), k1_relat_1(A_151)) | ~v1_funct_1(B_152) | ~v1_relat_1(B_152) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151))), inference(resolution, [status(thm)], [c_1983, c_22])).
% 6.01/2.19  tff(c_3177, plain, (![A_179, B_180]: (k1_funct_1('#skF_2', '#skF_1'(A_179, B_180, k1_relat_1(k7_relat_1(B_180, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'(A_179, B_180, k1_relat_1(k7_relat_1(B_180, '#skF_4')))) | k7_relat_1(B_180, k1_relat_1(k7_relat_1(B_180, '#skF_4')))=k7_relat_1(A_179, k1_relat_1(k7_relat_1(B_180, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_180, '#skF_4')), k1_relat_1(A_179)) | ~v1_funct_1(B_180) | ~v1_funct_1(A_179) | ~v1_relat_1(A_179) | ~v1_relat_1(B_180))), inference(resolution, [status(thm)], [c_10, c_2303])).
% 6.01/2.19  tff(c_3203, plain, (![B_180]: (k1_funct_1('#skF_2', '#skF_1'('#skF_2', B_180, k1_relat_1(k7_relat_1(B_180, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', B_180, k1_relat_1(k7_relat_1(B_180, '#skF_4')))) | k7_relat_1(B_180, k1_relat_1(k7_relat_1(B_180, '#skF_4')))=k7_relat_1('#skF_2', k1_relat_1(k7_relat_1(B_180, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_180, '#skF_4')), k1_relat_1('#skF_3')) | ~v1_funct_1(B_180) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(B_180))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3177])).
% 6.01/2.19  tff(c_3614, plain, (![B_190]: (k1_funct_1('#skF_2', '#skF_1'('#skF_2', B_190, k1_relat_1(k7_relat_1(B_190, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', B_190, k1_relat_1(k7_relat_1(B_190, '#skF_4')))) | k7_relat_1(B_190, k1_relat_1(k7_relat_1(B_190, '#skF_4')))=k7_relat_1('#skF_2', k1_relat_1(k7_relat_1(B_190, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_190, '#skF_4')), k1_relat_1('#skF_3')) | ~v1_funct_1(B_190) | ~v1_relat_1(B_190))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_3203])).
% 6.01/2.19  tff(c_3620, plain, (k1_funct_1('#skF_2', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))) | k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))=k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_3614])).
% 6.01/2.19  tff(c_3629, plain, (k1_funct_1('#skF_2', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))) | k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_158, c_166, c_3620])).
% 6.01/2.19  tff(c_3630, plain, (k1_funct_1('#skF_2', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_20, c_3629])).
% 6.01/2.19  tff(c_16, plain, (![B_22, A_10, C_28]: (k1_funct_1(B_22, '#skF_1'(A_10, B_22, C_28))!=k1_funct_1(A_10, '#skF_1'(A_10, B_22, C_28)) | k7_relat_1(B_22, C_28)=k7_relat_1(A_10, C_28) | ~r1_tarski(C_28, k1_relat_1(B_22)) | ~r1_tarski(C_28, k1_relat_1(A_10)) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.01/2.19  tff(c_3639, plain, (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))=k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_4')), k1_relat_1('#skF_3')) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_4')), k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3630, c_16])).
% 6.01/2.19  tff(c_3644, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_26, c_80, c_24, c_80, c_158, c_166, c_3639])).
% 6.01/2.19  tff(c_3646, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_3644])).
% 6.01/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.01/2.19  
% 6.01/2.19  Inference rules
% 6.01/2.19  ----------------------
% 6.01/2.19  #Ref     : 2
% 6.01/2.19  #Sup     : 849
% 6.01/2.19  #Fact    : 0
% 6.01/2.19  #Define  : 0
% 6.01/2.19  #Split   : 1
% 6.01/2.19  #Chain   : 0
% 6.01/2.19  #Close   : 0
% 6.01/2.19  
% 6.01/2.19  Ordering : KBO
% 6.01/2.19  
% 6.01/2.19  Simplification rules
% 6.01/2.19  ----------------------
% 6.01/2.19  #Subsume      : 274
% 6.01/2.19  #Demod        : 2295
% 6.01/2.19  #Tautology    : 176
% 6.01/2.19  #SimpNegUnit  : 3
% 6.01/2.19  #BackRed      : 2
% 6.01/2.19  
% 6.01/2.19  #Partial instantiations: 0
% 6.01/2.19  #Strategies tried      : 1
% 6.01/2.19  
% 6.01/2.19  Timing (in seconds)
% 6.01/2.19  ----------------------
% 6.01/2.20  Preprocessing        : 0.30
% 6.01/2.20  Parsing              : 0.16
% 6.01/2.20  CNF conversion       : 0.02
% 6.01/2.20  Main loop            : 1.10
% 6.01/2.20  Inferencing          : 0.33
% 6.01/2.20  Reduction            : 0.45
% 6.01/2.20  Demodulation         : 0.36
% 6.01/2.20  BG Simplification    : 0.05
% 6.01/2.20  Subsumption          : 0.22
% 6.01/2.20  Abstraction          : 0.07
% 6.01/2.20  MUC search           : 0.00
% 6.01/2.20  Cooper               : 0.00
% 6.01/2.20  Total                : 1.45
% 6.01/2.20  Index Insertion      : 0.00
% 6.01/2.20  Index Deletion       : 0.00
% 6.01/2.20  Index Matching       : 0.00
% 6.01/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
