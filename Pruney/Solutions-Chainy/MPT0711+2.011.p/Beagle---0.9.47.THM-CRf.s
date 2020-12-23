%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:31 EST 2020

% Result     : Theorem 9.84s
% Output     : CNFRefutation 9.96s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 777 expanded)
%              Number of leaves         :   24 ( 278 expanded)
%              Depth                    :   18
%              Number of atoms          :  211 (2339 expanded)
%              Number of equality atoms :   63 ( 804 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_113,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_93,axiom,(
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

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_32,plain,(
    k7_relat_1('#skF_3','#skF_5') != k7_relat_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_10,A_9)),k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    k1_relat_1('#skF_3') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_112,plain,(
    ! [B_77,A_78] :
      ( k1_relat_1(k7_relat_1(B_77,A_78)) = A_78
      | ~ r1_tarski(A_78,k1_relat_1(B_77))
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_132,plain,(
    ! [A_78] :
      ( k1_relat_1(k7_relat_1('#skF_3',A_78)) = A_78
      | ~ r1_tarski(A_78,k1_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_112])).

tff(c_143,plain,(
    ! [A_79] :
      ( k1_relat_1(k7_relat_1('#skF_3',A_79)) = A_79
      | ~ r1_tarski(A_79,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_132])).

tff(c_154,plain,(
    ! [A_9] :
      ( k1_relat_1(k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_4',A_9)))) = k1_relat_1(k7_relat_1('#skF_4',A_9))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_143])).

tff(c_375,plain,(
    ! [A_104] : k1_relat_1(k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_4',A_104)))) = k1_relat_1(k7_relat_1('#skF_4',A_104)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_154])).

tff(c_62,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_65,A_66)),k1_relat_1(B_65))
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,(
    ! [A_66] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_66)),k1_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_62])).

tff(c_72,plain,(
    ! [A_66] : r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_66)),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_68])).

tff(c_403,plain,(
    ! [A_104] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_104)),k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_375,c_72])).

tff(c_24,plain,(
    ! [A_15,B_16] : v1_relat_1('#skF_1'(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_15,B_16] : k1_relat_1('#skF_1'(A_15,B_16)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_471,plain,(
    ! [A_107,B_108] :
      ( k7_relat_1(A_107,k1_relat_1(k7_relat_1(B_108,k1_relat_1(A_107)))) = k7_relat_1(A_107,k1_relat_1(B_108))
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_591,plain,(
    ! [B_108] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1(B_108,k1_relat_1('#skF_4')))) = k7_relat_1('#skF_3',k1_relat_1(B_108))
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_471])).

tff(c_644,plain,(
    ! [B_109] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1(B_109,k1_relat_1('#skF_4')))) = k7_relat_1('#skF_3',k1_relat_1(B_109))
      | ~ v1_relat_1(B_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_591])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_8,A_7)),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_686,plain,(
    ! [B_109] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_3',k1_relat_1(B_109))),k1_relat_1(k7_relat_1(B_109,k1_relat_1('#skF_4'))))
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_10])).

tff(c_1933,plain,(
    ! [B_141] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_3',k1_relat_1(B_141))),k1_relat_1(k7_relat_1(B_141,k1_relat_1('#skF_4'))))
      | ~ v1_relat_1(B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_686])).

tff(c_2011,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_15)),k1_relat_1(k7_relat_1('#skF_1'(A_15,B_16),k1_relat_1('#skF_4'))))
      | ~ v1_relat_1('#skF_1'(A_15,B_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1933])).

tff(c_2042,plain,(
    ! [A_15,B_16] : r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_15)),k1_relat_1(k7_relat_1('#skF_1'(A_15,B_16),k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2011])).

tff(c_588,plain,(
    ! [A_15,B_16,B_108] :
      ( k7_relat_1('#skF_1'(A_15,B_16),k1_relat_1(k7_relat_1(B_108,A_15))) = k7_relat_1('#skF_1'(A_15,B_16),k1_relat_1(B_108))
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1('#skF_1'(A_15,B_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_471])).

tff(c_3911,plain,(
    ! [A_218,B_219,B_220] :
      ( k7_relat_1('#skF_1'(A_218,B_219),k1_relat_1(k7_relat_1(B_220,A_218))) = k7_relat_1('#skF_1'(A_218,B_219),k1_relat_1(B_220))
      | ~ v1_relat_1(B_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_588])).

tff(c_4003,plain,(
    ! [A_218,B_219,B_220] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_1'(A_218,B_219),k1_relat_1(B_220))),k1_relat_1(k7_relat_1(B_220,A_218)))
      | ~ v1_relat_1('#skF_1'(A_218,B_219))
      | ~ v1_relat_1(B_220) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3911,c_10])).

tff(c_4325,plain,(
    ! [A_233,B_234,B_235] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_1'(A_233,B_234),k1_relat_1(B_235))),k1_relat_1(k7_relat_1(B_235,A_233)))
      | ~ v1_relat_1(B_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4003])).

tff(c_4469,plain,(
    ! [A_233,B_234] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_1'(A_233,B_234),k1_relat_1('#skF_4'))),k1_relat_1(k7_relat_1('#skF_3',A_233)))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4325])).

tff(c_4685,plain,(
    ! [A_238,B_239] : r1_tarski(k1_relat_1(k7_relat_1('#skF_1'(A_238,B_239),k1_relat_1('#skF_4'))),k1_relat_1(k7_relat_1('#skF_3',A_238))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_4469])).

tff(c_84,plain,(
    ! [B_74,A_75] :
      ( k7_relat_1(B_74,A_75) = B_74
      | ~ r1_tarski(k1_relat_1(B_74),A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_99,plain,(
    ! [A_15,B_16,A_75] :
      ( k7_relat_1('#skF_1'(A_15,B_16),A_75) = '#skF_1'(A_15,B_16)
      | ~ r1_tarski(A_15,A_75)
      | ~ v1_relat_1('#skF_1'(A_15,B_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_84])).

tff(c_281,plain,(
    ! [A_90,B_91,A_92] :
      ( k7_relat_1('#skF_1'(A_90,B_91),A_92) = '#skF_1'(A_90,B_91)
      | ~ r1_tarski(A_90,A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_99])).

tff(c_129,plain,(
    ! [A_15,B_16,A_78] :
      ( k1_relat_1(k7_relat_1('#skF_1'(A_15,B_16),A_78)) = A_78
      | ~ r1_tarski(A_78,A_15)
      | ~ v1_relat_1('#skF_1'(A_15,B_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_112])).

tff(c_140,plain,(
    ! [A_15,B_16,A_78] :
      ( k1_relat_1(k7_relat_1('#skF_1'(A_15,B_16),A_78)) = A_78
      | ~ r1_tarski(A_78,A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_129])).

tff(c_290,plain,(
    ! [A_90,B_91,A_92] :
      ( k1_relat_1('#skF_1'(A_90,B_91)) = A_92
      | ~ r1_tarski(A_92,A_90)
      | ~ r1_tarski(A_90,A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_140])).

tff(c_306,plain,(
    ! [A_92,A_90] :
      ( A_92 = A_90
      | ~ r1_tarski(A_92,A_90)
      | ~ r1_tarski(A_90,A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_290])).

tff(c_4697,plain,(
    ! [A_238,B_239] :
      ( k1_relat_1(k7_relat_1('#skF_1'(A_238,B_239),k1_relat_1('#skF_4'))) = k1_relat_1(k7_relat_1('#skF_3',A_238))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_238)),k1_relat_1(k7_relat_1('#skF_1'(A_238,B_239),k1_relat_1('#skF_4')))) ) ),
    inference(resolution,[status(thm)],[c_4685,c_306])).

tff(c_5204,plain,(
    ! [A_243,B_244] : k1_relat_1(k7_relat_1('#skF_1'(A_243,B_244),k1_relat_1('#skF_4'))) = k1_relat_1(k7_relat_1('#skF_3',A_243)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2042,c_4697])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k7_relat_1(A_1,k1_relat_1(k7_relat_1(B_3,k1_relat_1(A_1)))) = k7_relat_1(A_1,k1_relat_1(B_3))
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5313,plain,(
    ! [A_243,B_244] :
      ( k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_3',A_243))) = k7_relat_1('#skF_4',k1_relat_1('#skF_1'(A_243,B_244)))
      | ~ v1_relat_1('#skF_1'(A_243,B_244))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5204,c_2])).

tff(c_5401,plain,(
    ! [A_243] : k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_3',A_243))) = k7_relat_1('#skF_4',A_243) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_24,c_20,c_5313])).

tff(c_119,plain,(
    ! [A_66] :
      ( k1_relat_1(k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_3',A_66)))) = k1_relat_1(k7_relat_1('#skF_3',A_66))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_112])).

tff(c_136,plain,(
    ! [A_66] : k1_relat_1(k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_3',A_66)))) = k1_relat_1(k7_relat_1('#skF_3',A_66)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_119])).

tff(c_5857,plain,(
    ! [A_66] : k1_relat_1(k7_relat_1('#skF_3',A_66)) = k1_relat_1(k7_relat_1('#skF_4',A_66)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5401,c_136])).

tff(c_640,plain,(
    ! [B_108] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1(B_108,k1_relat_1('#skF_4')))) = k7_relat_1('#skF_3',k1_relat_1(B_108))
      | ~ v1_relat_1(B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_591])).

tff(c_5307,plain,(
    ! [A_243,B_244] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3',A_243))) = k7_relat_1('#skF_3',k1_relat_1('#skF_1'(A_243,B_244)))
      | ~ v1_relat_1('#skF_1'(A_243,B_244)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5204,c_640])).

tff(c_5399,plain,(
    ! [A_243] : k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3',A_243))) = k7_relat_1('#skF_3',A_243) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_5307])).

tff(c_6029,plain,(
    ! [A_243] : k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_4',A_243))) = k7_relat_1('#skF_3',A_243) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5857,c_5399])).

tff(c_6028,plain,(
    ! [A_243] : k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_4',A_243))) = k7_relat_1('#skF_4',A_243) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5857,c_5401])).

tff(c_1435,plain,(
    ! [A_130,B_131,C_132] :
      ( r2_hidden('#skF_2'(A_130,B_131,C_132),C_132)
      | k7_relat_1(B_131,C_132) = k7_relat_1(A_130,C_132)
      | ~ r1_tarski(C_132,k1_relat_1(B_131))
      | ~ r1_tarski(C_132,k1_relat_1(A_130))
      | ~ v1_funct_1(B_131)
      | ~ v1_relat_1(B_131)
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_8,plain,(
    ! [A_4,B_5,C_6] :
      ( r2_hidden(A_4,B_5)
      | ~ r2_hidden(A_4,k1_relat_1(k7_relat_1(C_6,B_5)))
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_11531,plain,(
    ! [A_323,B_324,C_325,B_326] :
      ( r2_hidden('#skF_2'(A_323,B_324,k1_relat_1(k7_relat_1(C_325,B_326))),B_326)
      | ~ v1_relat_1(C_325)
      | k7_relat_1(B_324,k1_relat_1(k7_relat_1(C_325,B_326))) = k7_relat_1(A_323,k1_relat_1(k7_relat_1(C_325,B_326)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_325,B_326)),k1_relat_1(B_324))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_325,B_326)),k1_relat_1(A_323))
      | ~ v1_funct_1(B_324)
      | ~ v1_relat_1(B_324)
      | ~ v1_funct_1(A_323)
      | ~ v1_relat_1(A_323) ) ),
    inference(resolution,[status(thm)],[c_1435,c_8])).

tff(c_34,plain,(
    ! [D_55] :
      ( k1_funct_1('#skF_3',D_55) = k1_funct_1('#skF_4',D_55)
      | ~ r2_hidden(D_55,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_11696,plain,(
    ! [A_327,B_328,C_329] :
      ( k1_funct_1('#skF_3','#skF_2'(A_327,B_328,k1_relat_1(k7_relat_1(C_329,'#skF_5')))) = k1_funct_1('#skF_4','#skF_2'(A_327,B_328,k1_relat_1(k7_relat_1(C_329,'#skF_5'))))
      | ~ v1_relat_1(C_329)
      | k7_relat_1(B_328,k1_relat_1(k7_relat_1(C_329,'#skF_5'))) = k7_relat_1(A_327,k1_relat_1(k7_relat_1(C_329,'#skF_5')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_329,'#skF_5')),k1_relat_1(B_328))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_329,'#skF_5')),k1_relat_1(A_327))
      | ~ v1_funct_1(B_328)
      | ~ v1_relat_1(B_328)
      | ~ v1_funct_1(A_327)
      | ~ v1_relat_1(A_327) ) ),
    inference(resolution,[status(thm)],[c_11531,c_34])).

tff(c_13618,plain,(
    ! [A_352,B_353] :
      ( k1_funct_1('#skF_3','#skF_2'(A_352,B_353,k1_relat_1(k7_relat_1(B_353,'#skF_5')))) = k1_funct_1('#skF_4','#skF_2'(A_352,B_353,k1_relat_1(k7_relat_1(B_353,'#skF_5'))))
      | k7_relat_1(B_353,k1_relat_1(k7_relat_1(B_353,'#skF_5'))) = k7_relat_1(A_352,k1_relat_1(k7_relat_1(B_353,'#skF_5')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_353,'#skF_5')),k1_relat_1(A_352))
      | ~ v1_funct_1(B_353)
      | ~ v1_funct_1(A_352)
      | ~ v1_relat_1(A_352)
      | ~ v1_relat_1(B_353) ) ),
    inference(resolution,[status(thm)],[c_12,c_11696])).

tff(c_13728,plain,(
    ! [B_353] :
      ( k1_funct_1('#skF_3','#skF_2'('#skF_3',B_353,k1_relat_1(k7_relat_1(B_353,'#skF_5')))) = k1_funct_1('#skF_4','#skF_2'('#skF_3',B_353,k1_relat_1(k7_relat_1(B_353,'#skF_5'))))
      | k7_relat_1(B_353,k1_relat_1(k7_relat_1(B_353,'#skF_5'))) = k7_relat_1('#skF_3',k1_relat_1(k7_relat_1(B_353,'#skF_5')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_353,'#skF_5')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(B_353)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_353) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_13618])).

tff(c_13892,plain,(
    ! [B_359] :
      ( k1_funct_1('#skF_3','#skF_2'('#skF_3',B_359,k1_relat_1(k7_relat_1(B_359,'#skF_5')))) = k1_funct_1('#skF_4','#skF_2'('#skF_3',B_359,k1_relat_1(k7_relat_1(B_359,'#skF_5'))))
      | k7_relat_1(B_359,k1_relat_1(k7_relat_1(B_359,'#skF_5'))) = k7_relat_1('#skF_3',k1_relat_1(k7_relat_1(B_359,'#skF_5')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_359,'#skF_5')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(B_359)
      | ~ v1_relat_1(B_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_13728])).

tff(c_13928,plain,
    ( k1_funct_1('#skF_3','#skF_2'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))) = k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5'))))
    | k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_4','#skF_5'))) = k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_403,c_13892])).

tff(c_13967,plain,
    ( k1_funct_1('#skF_3','#skF_2'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))) = k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5'))))
    | k7_relat_1('#skF_3','#skF_5') = k7_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_6029,c_6028,c_13928])).

tff(c_13968,plain,(
    k1_funct_1('#skF_3','#skF_2'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))) = k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_13967])).

tff(c_28,plain,(
    ! [B_34,A_22,C_40] :
      ( k1_funct_1(B_34,'#skF_2'(A_22,B_34,C_40)) != k1_funct_1(A_22,'#skF_2'(A_22,B_34,C_40))
      | k7_relat_1(B_34,C_40) = k7_relat_1(A_22,C_40)
      | ~ r1_tarski(C_40,k1_relat_1(B_34))
      | ~ r1_tarski(C_40,k1_relat_1(A_22))
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_15160,plain,
    ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_4','#skF_5'))) = k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_5')),k1_relat_1('#skF_4'))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_5')),k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13968,c_28])).

tff(c_15165,plain,(
    k7_relat_1('#skF_3','#skF_5') = k7_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_403,c_36,c_403,c_6029,c_6028,c_15160])).

tff(c_15167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_15165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:30:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.84/3.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.96/3.69  
% 9.96/3.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.96/3.69  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 9.96/3.69  
% 9.96/3.69  %Foreground sorts:
% 9.96/3.69  
% 9.96/3.69  
% 9.96/3.69  %Background operators:
% 9.96/3.69  
% 9.96/3.69  
% 9.96/3.69  %Foreground operators:
% 9.96/3.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.96/3.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.96/3.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.96/3.69  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.96/3.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.96/3.69  tff('#skF_5', type, '#skF_5': $i).
% 9.96/3.69  tff('#skF_3', type, '#skF_3': $i).
% 9.96/3.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.96/3.69  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.96/3.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.96/3.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.96/3.69  tff('#skF_4', type, '#skF_4': $i).
% 9.96/3.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.96/3.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.96/3.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.96/3.69  
% 9.96/3.71  tff(f_113, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (((k1_relat_1(A) = k1_relat_1(B)) & (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))) => (k7_relat_1(A, C) = k7_relat_1(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_funct_1)).
% 9.96/3.71  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 9.96/3.71  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 9.96/3.71  tff(f_72, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 9.96/3.71  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 9.96/3.71  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 9.96/3.71  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 9.96/3.71  tff(f_93, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((r1_tarski(C, k1_relat_1(A)) & r1_tarski(C, k1_relat_1(B))) => ((k7_relat_1(A, C) = k7_relat_1(B, C)) <=> (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t165_funct_1)).
% 9.96/3.71  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 9.96/3.71  tff(c_32, plain, (k7_relat_1('#skF_3', '#skF_5')!=k7_relat_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.96/3.71  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.96/3.71  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.96/3.71  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.96/3.71  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.96/3.71  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(k7_relat_1(B_10, A_9)), k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.96/3.71  tff(c_36, plain, (k1_relat_1('#skF_3')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.96/3.71  tff(c_112, plain, (![B_77, A_78]: (k1_relat_1(k7_relat_1(B_77, A_78))=A_78 | ~r1_tarski(A_78, k1_relat_1(B_77)) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.96/3.71  tff(c_132, plain, (![A_78]: (k1_relat_1(k7_relat_1('#skF_3', A_78))=A_78 | ~r1_tarski(A_78, k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_112])).
% 9.96/3.71  tff(c_143, plain, (![A_79]: (k1_relat_1(k7_relat_1('#skF_3', A_79))=A_79 | ~r1_tarski(A_79, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_132])).
% 9.96/3.71  tff(c_154, plain, (![A_9]: (k1_relat_1(k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_4', A_9))))=k1_relat_1(k7_relat_1('#skF_4', A_9)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_143])).
% 9.96/3.71  tff(c_375, plain, (![A_104]: (k1_relat_1(k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_4', A_104))))=k1_relat_1(k7_relat_1('#skF_4', A_104)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_154])).
% 9.96/3.71  tff(c_62, plain, (![B_65, A_66]: (r1_tarski(k1_relat_1(k7_relat_1(B_65, A_66)), k1_relat_1(B_65)) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.96/3.71  tff(c_68, plain, (![A_66]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_66)), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_62])).
% 9.96/3.71  tff(c_72, plain, (![A_66]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_66)), k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_68])).
% 9.96/3.71  tff(c_403, plain, (![A_104]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_104)), k1_relat_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_375, c_72])).
% 9.96/3.71  tff(c_24, plain, (![A_15, B_16]: (v1_relat_1('#skF_1'(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.96/3.71  tff(c_20, plain, (![A_15, B_16]: (k1_relat_1('#skF_1'(A_15, B_16))=A_15)), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.96/3.71  tff(c_471, plain, (![A_107, B_108]: (k7_relat_1(A_107, k1_relat_1(k7_relat_1(B_108, k1_relat_1(A_107))))=k7_relat_1(A_107, k1_relat_1(B_108)) | ~v1_relat_1(B_108) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.96/3.71  tff(c_591, plain, (![B_108]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1(B_108, k1_relat_1('#skF_4'))))=k7_relat_1('#skF_3', k1_relat_1(B_108)) | ~v1_relat_1(B_108) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_471])).
% 9.96/3.71  tff(c_644, plain, (![B_109]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1(B_109, k1_relat_1('#skF_4'))))=k7_relat_1('#skF_3', k1_relat_1(B_109)) | ~v1_relat_1(B_109))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_591])).
% 9.96/3.71  tff(c_10, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(k7_relat_1(B_8, A_7)), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.96/3.71  tff(c_686, plain, (![B_109]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', k1_relat_1(B_109))), k1_relat_1(k7_relat_1(B_109, k1_relat_1('#skF_4')))) | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_109))), inference(superposition, [status(thm), theory('equality')], [c_644, c_10])).
% 9.96/3.71  tff(c_1933, plain, (![B_141]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', k1_relat_1(B_141))), k1_relat_1(k7_relat_1(B_141, k1_relat_1('#skF_4')))) | ~v1_relat_1(B_141))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_686])).
% 9.96/3.71  tff(c_2011, plain, (![A_15, B_16]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_15)), k1_relat_1(k7_relat_1('#skF_1'(A_15, B_16), k1_relat_1('#skF_4')))) | ~v1_relat_1('#skF_1'(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1933])).
% 9.96/3.71  tff(c_2042, plain, (![A_15, B_16]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_15)), k1_relat_1(k7_relat_1('#skF_1'(A_15, B_16), k1_relat_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2011])).
% 9.96/3.71  tff(c_588, plain, (![A_15, B_16, B_108]: (k7_relat_1('#skF_1'(A_15, B_16), k1_relat_1(k7_relat_1(B_108, A_15)))=k7_relat_1('#skF_1'(A_15, B_16), k1_relat_1(B_108)) | ~v1_relat_1(B_108) | ~v1_relat_1('#skF_1'(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_471])).
% 9.96/3.71  tff(c_3911, plain, (![A_218, B_219, B_220]: (k7_relat_1('#skF_1'(A_218, B_219), k1_relat_1(k7_relat_1(B_220, A_218)))=k7_relat_1('#skF_1'(A_218, B_219), k1_relat_1(B_220)) | ~v1_relat_1(B_220))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_588])).
% 9.96/3.71  tff(c_4003, plain, (![A_218, B_219, B_220]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_1'(A_218, B_219), k1_relat_1(B_220))), k1_relat_1(k7_relat_1(B_220, A_218))) | ~v1_relat_1('#skF_1'(A_218, B_219)) | ~v1_relat_1(B_220))), inference(superposition, [status(thm), theory('equality')], [c_3911, c_10])).
% 9.96/3.71  tff(c_4325, plain, (![A_233, B_234, B_235]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_1'(A_233, B_234), k1_relat_1(B_235))), k1_relat_1(k7_relat_1(B_235, A_233))) | ~v1_relat_1(B_235))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4003])).
% 9.96/3.71  tff(c_4469, plain, (![A_233, B_234]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_1'(A_233, B_234), k1_relat_1('#skF_4'))), k1_relat_1(k7_relat_1('#skF_3', A_233))) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_4325])).
% 9.96/3.71  tff(c_4685, plain, (![A_238, B_239]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_1'(A_238, B_239), k1_relat_1('#skF_4'))), k1_relat_1(k7_relat_1('#skF_3', A_238))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_4469])).
% 9.96/3.71  tff(c_84, plain, (![B_74, A_75]: (k7_relat_1(B_74, A_75)=B_74 | ~r1_tarski(k1_relat_1(B_74), A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.96/3.71  tff(c_99, plain, (![A_15, B_16, A_75]: (k7_relat_1('#skF_1'(A_15, B_16), A_75)='#skF_1'(A_15, B_16) | ~r1_tarski(A_15, A_75) | ~v1_relat_1('#skF_1'(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_84])).
% 9.96/3.71  tff(c_281, plain, (![A_90, B_91, A_92]: (k7_relat_1('#skF_1'(A_90, B_91), A_92)='#skF_1'(A_90, B_91) | ~r1_tarski(A_90, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_99])).
% 9.96/3.71  tff(c_129, plain, (![A_15, B_16, A_78]: (k1_relat_1(k7_relat_1('#skF_1'(A_15, B_16), A_78))=A_78 | ~r1_tarski(A_78, A_15) | ~v1_relat_1('#skF_1'(A_15, B_16)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_112])).
% 9.96/3.71  tff(c_140, plain, (![A_15, B_16, A_78]: (k1_relat_1(k7_relat_1('#skF_1'(A_15, B_16), A_78))=A_78 | ~r1_tarski(A_78, A_15))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_129])).
% 9.96/3.71  tff(c_290, plain, (![A_90, B_91, A_92]: (k1_relat_1('#skF_1'(A_90, B_91))=A_92 | ~r1_tarski(A_92, A_90) | ~r1_tarski(A_90, A_92))), inference(superposition, [status(thm), theory('equality')], [c_281, c_140])).
% 9.96/3.71  tff(c_306, plain, (![A_92, A_90]: (A_92=A_90 | ~r1_tarski(A_92, A_90) | ~r1_tarski(A_90, A_92))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_290])).
% 9.96/3.71  tff(c_4697, plain, (![A_238, B_239]: (k1_relat_1(k7_relat_1('#skF_1'(A_238, B_239), k1_relat_1('#skF_4')))=k1_relat_1(k7_relat_1('#skF_3', A_238)) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_238)), k1_relat_1(k7_relat_1('#skF_1'(A_238, B_239), k1_relat_1('#skF_4')))))), inference(resolution, [status(thm)], [c_4685, c_306])).
% 9.96/3.71  tff(c_5204, plain, (![A_243, B_244]: (k1_relat_1(k7_relat_1('#skF_1'(A_243, B_244), k1_relat_1('#skF_4')))=k1_relat_1(k7_relat_1('#skF_3', A_243)))), inference(demodulation, [status(thm), theory('equality')], [c_2042, c_4697])).
% 9.96/3.71  tff(c_2, plain, (![A_1, B_3]: (k7_relat_1(A_1, k1_relat_1(k7_relat_1(B_3, k1_relat_1(A_1))))=k7_relat_1(A_1, k1_relat_1(B_3)) | ~v1_relat_1(B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.96/3.71  tff(c_5313, plain, (![A_243, B_244]: (k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_3', A_243)))=k7_relat_1('#skF_4', k1_relat_1('#skF_1'(A_243, B_244))) | ~v1_relat_1('#skF_1'(A_243, B_244)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5204, c_2])).
% 9.96/3.71  tff(c_5401, plain, (![A_243]: (k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_3', A_243)))=k7_relat_1('#skF_4', A_243))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_24, c_20, c_5313])).
% 9.96/3.71  tff(c_119, plain, (![A_66]: (k1_relat_1(k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_3', A_66))))=k1_relat_1(k7_relat_1('#skF_3', A_66)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_112])).
% 9.96/3.71  tff(c_136, plain, (![A_66]: (k1_relat_1(k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_3', A_66))))=k1_relat_1(k7_relat_1('#skF_3', A_66)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_119])).
% 9.96/3.71  tff(c_5857, plain, (![A_66]: (k1_relat_1(k7_relat_1('#skF_3', A_66))=k1_relat_1(k7_relat_1('#skF_4', A_66)))), inference(demodulation, [status(thm), theory('equality')], [c_5401, c_136])).
% 9.96/3.71  tff(c_640, plain, (![B_108]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1(B_108, k1_relat_1('#skF_4'))))=k7_relat_1('#skF_3', k1_relat_1(B_108)) | ~v1_relat_1(B_108))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_591])).
% 9.96/3.71  tff(c_5307, plain, (![A_243, B_244]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', A_243)))=k7_relat_1('#skF_3', k1_relat_1('#skF_1'(A_243, B_244))) | ~v1_relat_1('#skF_1'(A_243, B_244)))), inference(superposition, [status(thm), theory('equality')], [c_5204, c_640])).
% 9.96/3.71  tff(c_5399, plain, (![A_243]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', A_243)))=k7_relat_1('#skF_3', A_243))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_5307])).
% 9.96/3.71  tff(c_6029, plain, (![A_243]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_4', A_243)))=k7_relat_1('#skF_3', A_243))), inference(demodulation, [status(thm), theory('equality')], [c_5857, c_5399])).
% 9.96/3.71  tff(c_6028, plain, (![A_243]: (k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_4', A_243)))=k7_relat_1('#skF_4', A_243))), inference(demodulation, [status(thm), theory('equality')], [c_5857, c_5401])).
% 9.96/3.71  tff(c_1435, plain, (![A_130, B_131, C_132]: (r2_hidden('#skF_2'(A_130, B_131, C_132), C_132) | k7_relat_1(B_131, C_132)=k7_relat_1(A_130, C_132) | ~r1_tarski(C_132, k1_relat_1(B_131)) | ~r1_tarski(C_132, k1_relat_1(A_130)) | ~v1_funct_1(B_131) | ~v1_relat_1(B_131) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.96/3.71  tff(c_8, plain, (![A_4, B_5, C_6]: (r2_hidden(A_4, B_5) | ~r2_hidden(A_4, k1_relat_1(k7_relat_1(C_6, B_5))) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.96/3.71  tff(c_11531, plain, (![A_323, B_324, C_325, B_326]: (r2_hidden('#skF_2'(A_323, B_324, k1_relat_1(k7_relat_1(C_325, B_326))), B_326) | ~v1_relat_1(C_325) | k7_relat_1(B_324, k1_relat_1(k7_relat_1(C_325, B_326)))=k7_relat_1(A_323, k1_relat_1(k7_relat_1(C_325, B_326))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_325, B_326)), k1_relat_1(B_324)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_325, B_326)), k1_relat_1(A_323)) | ~v1_funct_1(B_324) | ~v1_relat_1(B_324) | ~v1_funct_1(A_323) | ~v1_relat_1(A_323))), inference(resolution, [status(thm)], [c_1435, c_8])).
% 9.96/3.71  tff(c_34, plain, (![D_55]: (k1_funct_1('#skF_3', D_55)=k1_funct_1('#skF_4', D_55) | ~r2_hidden(D_55, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.96/3.71  tff(c_11696, plain, (![A_327, B_328, C_329]: (k1_funct_1('#skF_3', '#skF_2'(A_327, B_328, k1_relat_1(k7_relat_1(C_329, '#skF_5'))))=k1_funct_1('#skF_4', '#skF_2'(A_327, B_328, k1_relat_1(k7_relat_1(C_329, '#skF_5')))) | ~v1_relat_1(C_329) | k7_relat_1(B_328, k1_relat_1(k7_relat_1(C_329, '#skF_5')))=k7_relat_1(A_327, k1_relat_1(k7_relat_1(C_329, '#skF_5'))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_329, '#skF_5')), k1_relat_1(B_328)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_329, '#skF_5')), k1_relat_1(A_327)) | ~v1_funct_1(B_328) | ~v1_relat_1(B_328) | ~v1_funct_1(A_327) | ~v1_relat_1(A_327))), inference(resolution, [status(thm)], [c_11531, c_34])).
% 9.96/3.71  tff(c_13618, plain, (![A_352, B_353]: (k1_funct_1('#skF_3', '#skF_2'(A_352, B_353, k1_relat_1(k7_relat_1(B_353, '#skF_5'))))=k1_funct_1('#skF_4', '#skF_2'(A_352, B_353, k1_relat_1(k7_relat_1(B_353, '#skF_5')))) | k7_relat_1(B_353, k1_relat_1(k7_relat_1(B_353, '#skF_5')))=k7_relat_1(A_352, k1_relat_1(k7_relat_1(B_353, '#skF_5'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_353, '#skF_5')), k1_relat_1(A_352)) | ~v1_funct_1(B_353) | ~v1_funct_1(A_352) | ~v1_relat_1(A_352) | ~v1_relat_1(B_353))), inference(resolution, [status(thm)], [c_12, c_11696])).
% 9.96/3.71  tff(c_13728, plain, (![B_353]: (k1_funct_1('#skF_3', '#skF_2'('#skF_3', B_353, k1_relat_1(k7_relat_1(B_353, '#skF_5'))))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', B_353, k1_relat_1(k7_relat_1(B_353, '#skF_5')))) | k7_relat_1(B_353, k1_relat_1(k7_relat_1(B_353, '#skF_5')))=k7_relat_1('#skF_3', k1_relat_1(k7_relat_1(B_353, '#skF_5'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_353, '#skF_5')), k1_relat_1('#skF_4')) | ~v1_funct_1(B_353) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_353))), inference(superposition, [status(thm), theory('equality')], [c_36, c_13618])).
% 9.96/3.71  tff(c_13892, plain, (![B_359]: (k1_funct_1('#skF_3', '#skF_2'('#skF_3', B_359, k1_relat_1(k7_relat_1(B_359, '#skF_5'))))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', B_359, k1_relat_1(k7_relat_1(B_359, '#skF_5')))) | k7_relat_1(B_359, k1_relat_1(k7_relat_1(B_359, '#skF_5')))=k7_relat_1('#skF_3', k1_relat_1(k7_relat_1(B_359, '#skF_5'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_359, '#skF_5')), k1_relat_1('#skF_4')) | ~v1_funct_1(B_359) | ~v1_relat_1(B_359))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_13728])).
% 9.96/3.71  tff(c_13928, plain, (k1_funct_1('#skF_3', '#skF_2'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5')))) | k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_4', '#skF_5')))=k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_403, c_13892])).
% 9.96/3.71  tff(c_13967, plain, (k1_funct_1('#skF_3', '#skF_2'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5')))) | k7_relat_1('#skF_3', '#skF_5')=k7_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_6029, c_6028, c_13928])).
% 9.96/3.71  tff(c_13968, plain, (k1_funct_1('#skF_3', '#skF_2'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_32, c_13967])).
% 9.96/3.71  tff(c_28, plain, (![B_34, A_22, C_40]: (k1_funct_1(B_34, '#skF_2'(A_22, B_34, C_40))!=k1_funct_1(A_22, '#skF_2'(A_22, B_34, C_40)) | k7_relat_1(B_34, C_40)=k7_relat_1(A_22, C_40) | ~r1_tarski(C_40, k1_relat_1(B_34)) | ~r1_tarski(C_40, k1_relat_1(A_22)) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.96/3.71  tff(c_15160, plain, (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_4', '#skF_5')))=k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_5')), k1_relat_1('#skF_4')) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_5')), k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13968, c_28])).
% 9.96/3.71  tff(c_15165, plain, (k7_relat_1('#skF_3', '#skF_5')=k7_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_403, c_36, c_403, c_6029, c_6028, c_15160])).
% 9.96/3.71  tff(c_15167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_15165])).
% 9.96/3.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.96/3.71  
% 9.96/3.71  Inference rules
% 9.96/3.71  ----------------------
% 9.96/3.71  #Ref     : 2
% 9.96/3.71  #Sup     : 3549
% 9.96/3.71  #Fact    : 0
% 9.96/3.71  #Define  : 0
% 9.96/3.71  #Split   : 3
% 9.96/3.71  #Chain   : 0
% 9.96/3.71  #Close   : 0
% 9.96/3.71  
% 9.96/3.71  Ordering : KBO
% 9.96/3.71  
% 9.96/3.71  Simplification rules
% 9.96/3.71  ----------------------
% 9.96/3.71  #Subsume      : 716
% 9.96/3.71  #Demod        : 4139
% 9.96/3.71  #Tautology    : 886
% 9.96/3.71  #SimpNegUnit  : 24
% 9.96/3.71  #BackRed      : 20
% 9.96/3.71  
% 9.96/3.71  #Partial instantiations: 0
% 9.96/3.71  #Strategies tried      : 1
% 9.96/3.71  
% 9.96/3.71  Timing (in seconds)
% 9.96/3.71  ----------------------
% 9.96/3.72  Preprocessing        : 0.32
% 9.96/3.72  Parsing              : 0.17
% 9.96/3.72  CNF conversion       : 0.03
% 9.96/3.72  Main loop            : 2.60
% 9.96/3.72  Inferencing          : 0.63
% 9.96/3.72  Reduction            : 1.07
% 9.96/3.72  Demodulation         : 0.85
% 9.96/3.72  BG Simplification    : 0.11
% 9.96/3.72  Subsumption          : 0.65
% 9.96/3.72  Abstraction          : 0.17
% 9.96/3.72  MUC search           : 0.00
% 9.96/3.72  Cooper               : 0.00
% 9.96/3.72  Total                : 2.97
% 9.96/3.72  Index Insertion      : 0.00
% 9.96/3.72  Index Deletion       : 0.00
% 9.96/3.72  Index Matching       : 0.00
% 9.96/3.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
