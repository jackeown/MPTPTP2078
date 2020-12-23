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
% DateTime   : Thu Dec  3 10:05:30 EST 2020

% Result     : Theorem 12.02s
% Output     : CNFRefutation 12.28s
% Verified   : 
% Statistics : Number of formulae       :   96 (1045 expanded)
%              Number of leaves         :   26 ( 368 expanded)
%              Depth                    :   20
%              Number of atoms          :  220 (2704 expanded)
%              Number of equality atoms :   66 ( 829 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_118,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_85,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t165_funct_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_36,plain,(
    k7_relat_1('#skF_3','#skF_5') != k7_relat_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_10,A_9)),k1_relat_1(B_10))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    k1_relat_1('#skF_3') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_176,plain,(
    ! [B_82,A_83] :
      ( k1_relat_1(k7_relat_1(B_82,A_83)) = A_83
      | ~ r1_tarski(A_83,k1_relat_1(B_82))
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_196,plain,(
    ! [A_83] :
      ( k1_relat_1(k7_relat_1('#skF_3',A_83)) = A_83
      | ~ r1_tarski(A_83,k1_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_176])).

tff(c_211,plain,(
    ! [A_84] :
      ( k1_relat_1(k7_relat_1('#skF_3',A_84)) = A_84
      | ~ r1_tarski(A_84,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_196])).

tff(c_222,plain,(
    ! [A_9] :
      ( k1_relat_1(k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_4',A_9)))) = k1_relat_1(k7_relat_1('#skF_4',A_9))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_211])).

tff(c_303,plain,(
    ! [A_92] : k1_relat_1(k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_4',A_92)))) = k1_relat_1(k7_relat_1('#skF_4',A_92)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_222])).

tff(c_83,plain,(
    ! [B_63,A_64] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_63,A_64)),k1_relat_1(B_63))
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_86,plain,(
    ! [A_64] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_64)),k1_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_83])).

tff(c_91,plain,(
    ! [A_64] : r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_64)),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_86])).

tff(c_326,plain,(
    ! [A_92] : r1_tarski(k1_relat_1(k7_relat_1('#skF_4',A_92)),k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_91])).

tff(c_18,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_15] : v1_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    ! [A_38] :
      ( k1_relat_1(k6_relat_1(A_38)) = A_38
      | ~ v1_funct_1(k6_relat_1(A_38))
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_50,plain,(
    ! [A_38] :
      ( k1_relat_1(k6_relat_1(A_38)) = A_38
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_34])).

tff(c_54,plain,(
    ! [A_38] : k1_relat_1(k6_relat_1(A_38)) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_50])).

tff(c_1052,plain,(
    ! [A_119,B_120] :
      ( k7_relat_1(A_119,k1_relat_1(k7_relat_1(B_120,k1_relat_1(A_119)))) = k7_relat_1(A_119,k1_relat_1(B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1236,plain,(
    ! [B_120] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1(B_120,k1_relat_1('#skF_4')))) = k7_relat_1('#skF_3',k1_relat_1(B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1052])).

tff(c_1418,plain,(
    ! [B_122] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1(B_122,k1_relat_1('#skF_4')))) = k7_relat_1('#skF_3',k1_relat_1(B_122))
      | ~ v1_relat_1(B_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1236])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_8,A_7)),A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1469,plain,(
    ! [B_122] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_3',k1_relat_1(B_122))),k1_relat_1(k7_relat_1(B_122,k1_relat_1('#skF_4'))))
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1418,c_10])).

tff(c_2731,plain,(
    ! [B_143] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_3',k1_relat_1(B_143))),k1_relat_1(k7_relat_1(B_143,k1_relat_1('#skF_4'))))
      | ~ v1_relat_1(B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1469])).

tff(c_2815,plain,(
    ! [A_38] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_38)),k1_relat_1(k7_relat_1(k6_relat_1(A_38),k1_relat_1('#skF_4'))))
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2731])).

tff(c_2846,plain,(
    ! [A_38] : r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_38)),k1_relat_1(k7_relat_1(k6_relat_1(A_38),k1_relat_1('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_2815])).

tff(c_1239,plain,(
    ! [A_38,B_120] :
      ( k7_relat_1(k6_relat_1(A_38),k1_relat_1(k7_relat_1(B_120,A_38))) = k7_relat_1(k6_relat_1(A_38),k1_relat_1(B_120))
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1052])).

tff(c_4115,plain,(
    ! [A_170,B_171] :
      ( k7_relat_1(k6_relat_1(A_170),k1_relat_1(k7_relat_1(B_171,A_170))) = k7_relat_1(k6_relat_1(A_170),k1_relat_1(B_171))
      | ~ v1_relat_1(B_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1239])).

tff(c_4191,plain,(
    ! [A_170,B_171] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_170),k1_relat_1(B_171))),k1_relat_1(k7_relat_1(B_171,A_170)))
      | ~ v1_relat_1(k6_relat_1(A_170))
      | ~ v1_relat_1(B_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4115,c_10])).

tff(c_4498,plain,(
    ! [A_178,B_179] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_178),k1_relat_1(B_179))),k1_relat_1(k7_relat_1(B_179,A_178)))
      | ~ v1_relat_1(B_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4191])).

tff(c_4654,plain,(
    ! [A_178] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_178),k1_relat_1('#skF_4'))),k1_relat_1(k7_relat_1('#skF_3',A_178)))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4498])).

tff(c_4714,plain,(
    ! [A_180] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_180),k1_relat_1('#skF_4'))),k1_relat_1(k7_relat_1('#skF_3',A_180))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4654])).

tff(c_96,plain,(
    ! [B_68,A_69] :
      ( k7_relat_1(B_68,A_69) = B_68
      | ~ r1_tarski(k1_relat_1(B_68),A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_114,plain,(
    ! [A_38,A_69] :
      ( k7_relat_1(k6_relat_1(A_38),A_69) = k6_relat_1(A_38)
      | ~ r1_tarski(A_38,A_69)
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_96])).

tff(c_122,plain,(
    ! [A_38,A_69] :
      ( k7_relat_1(k6_relat_1(A_38),A_69) = k6_relat_1(A_38)
      | ~ r1_tarski(A_38,A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_114])).

tff(c_199,plain,(
    ! [A_38,A_83] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_38),A_83)) = A_83
      | ~ r1_tarski(A_83,A_38)
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_176])).

tff(c_239,plain,(
    ! [A_88,A_89] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_88),A_89)) = A_89
      | ~ r1_tarski(A_89,A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_199])).

tff(c_272,plain,(
    ! [A_38,A_69] :
      ( k1_relat_1(k6_relat_1(A_38)) = A_69
      | ~ r1_tarski(A_69,A_38)
      | ~ r1_tarski(A_38,A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_239])).

tff(c_283,plain,(
    ! [A_69,A_38] :
      ( A_69 = A_38
      | ~ r1_tarski(A_69,A_38)
      | ~ r1_tarski(A_38,A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_272])).

tff(c_4724,plain,(
    ! [A_180] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_180),k1_relat_1('#skF_4'))) = k1_relat_1(k7_relat_1('#skF_3',A_180))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_180)),k1_relat_1(k7_relat_1(k6_relat_1(A_180),k1_relat_1('#skF_4')))) ) ),
    inference(resolution,[status(thm)],[c_4714,c_283])).

tff(c_4824,plain,(
    ! [A_181] : k1_relat_1(k7_relat_1(k6_relat_1(A_181),k1_relat_1('#skF_4'))) = k1_relat_1(k7_relat_1('#skF_3',A_181)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2846,c_4724])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k7_relat_1(A_1,k1_relat_1(k7_relat_1(B_3,k1_relat_1(A_1)))) = k7_relat_1(A_1,k1_relat_1(B_3))
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4890,plain,(
    ! [A_181] :
      ( k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_3',A_181))) = k7_relat_1('#skF_4',k1_relat_1(k6_relat_1(A_181)))
      | ~ v1_relat_1(k6_relat_1(A_181))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4824,c_2])).

tff(c_5005,plain,(
    ! [A_181] : k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_3',A_181))) = k7_relat_1('#skF_4',A_181) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18,c_54,c_4890])).

tff(c_186,plain,(
    ! [A_64] :
      ( k1_relat_1(k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_3',A_64)))) = k1_relat_1(k7_relat_1('#skF_3',A_64))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_91,c_176])).

tff(c_204,plain,(
    ! [A_64] : k1_relat_1(k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_3',A_64)))) = k1_relat_1(k7_relat_1('#skF_3',A_64)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_186])).

tff(c_5289,plain,(
    ! [A_64] : k1_relat_1(k7_relat_1('#skF_3',A_64)) = k1_relat_1(k7_relat_1('#skF_4',A_64)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5005,c_204])).

tff(c_5467,plain,(
    ! [A_181] : k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_4',A_181))) = k7_relat_1('#skF_4',A_181) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5289,c_5005])).

tff(c_1314,plain,(
    ! [B_120] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1(B_120,k1_relat_1('#skF_4')))) = k7_relat_1('#skF_3',k1_relat_1(B_120))
      | ~ v1_relat_1(B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1236])).

tff(c_4884,plain,(
    ! [A_181] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3',A_181))) = k7_relat_1('#skF_3',k1_relat_1(k6_relat_1(A_181)))
      | ~ v1_relat_1(k6_relat_1(A_181)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4824,c_1314])).

tff(c_5003,plain,(
    ! [A_181] : k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3',A_181))) = k7_relat_1('#skF_3',A_181) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_54,c_4884])).

tff(c_5922,plain,(
    ! [A_181] : k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_4',A_181))) = k7_relat_1('#skF_3',A_181) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5289,c_5003])).

tff(c_2255,plain,(
    ! [A_132,B_133,C_134] :
      ( r2_hidden('#skF_1'(A_132,B_133,C_134),C_134)
      | k7_relat_1(B_133,C_134) = k7_relat_1(A_132,C_134)
      | ~ r1_tarski(C_134,k1_relat_1(B_133))
      | ~ r1_tarski(C_134,k1_relat_1(A_132))
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133)
      | ~ v1_funct_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [A_4,B_5,C_6] :
      ( r2_hidden(A_4,B_5)
      | ~ r2_hidden(A_4,k1_relat_1(k7_relat_1(C_6,B_5)))
      | ~ v1_relat_1(C_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14559,plain,(
    ! [A_286,B_287,C_288,B_289] :
      ( r2_hidden('#skF_1'(A_286,B_287,k1_relat_1(k7_relat_1(C_288,B_289))),B_289)
      | ~ v1_relat_1(C_288)
      | k7_relat_1(B_287,k1_relat_1(k7_relat_1(C_288,B_289))) = k7_relat_1(A_286,k1_relat_1(k7_relat_1(C_288,B_289)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_288,B_289)),k1_relat_1(B_287))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_288,B_289)),k1_relat_1(A_286))
      | ~ v1_funct_1(B_287)
      | ~ v1_relat_1(B_287)
      | ~ v1_funct_1(A_286)
      | ~ v1_relat_1(A_286) ) ),
    inference(resolution,[status(thm)],[c_2255,c_8])).

tff(c_38,plain,(
    ! [D_54] :
      ( k1_funct_1('#skF_3',D_54) = k1_funct_1('#skF_4',D_54)
      | ~ r2_hidden(D_54,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_16178,plain,(
    ! [A_296,B_297,C_298] :
      ( k1_funct_1('#skF_3','#skF_1'(A_296,B_297,k1_relat_1(k7_relat_1(C_298,'#skF_5')))) = k1_funct_1('#skF_4','#skF_1'(A_296,B_297,k1_relat_1(k7_relat_1(C_298,'#skF_5'))))
      | ~ v1_relat_1(C_298)
      | k7_relat_1(B_297,k1_relat_1(k7_relat_1(C_298,'#skF_5'))) = k7_relat_1(A_296,k1_relat_1(k7_relat_1(C_298,'#skF_5')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_298,'#skF_5')),k1_relat_1(B_297))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_298,'#skF_5')),k1_relat_1(A_296))
      | ~ v1_funct_1(B_297)
      | ~ v1_relat_1(B_297)
      | ~ v1_funct_1(A_296)
      | ~ v1_relat_1(A_296) ) ),
    inference(resolution,[status(thm)],[c_14559,c_38])).

tff(c_18751,plain,(
    ! [A_326,B_327] :
      ( k1_funct_1('#skF_3','#skF_1'(A_326,B_327,k1_relat_1(k7_relat_1(B_327,'#skF_5')))) = k1_funct_1('#skF_4','#skF_1'(A_326,B_327,k1_relat_1(k7_relat_1(B_327,'#skF_5'))))
      | k7_relat_1(B_327,k1_relat_1(k7_relat_1(B_327,'#skF_5'))) = k7_relat_1(A_326,k1_relat_1(k7_relat_1(B_327,'#skF_5')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_327,'#skF_5')),k1_relat_1(A_326))
      | ~ v1_funct_1(B_327)
      | ~ v1_funct_1(A_326)
      | ~ v1_relat_1(A_326)
      | ~ v1_relat_1(B_327) ) ),
    inference(resolution,[status(thm)],[c_12,c_16178])).

tff(c_18878,plain,(
    ! [B_327] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_3',B_327,k1_relat_1(k7_relat_1(B_327,'#skF_5')))) = k1_funct_1('#skF_4','#skF_1'('#skF_3',B_327,k1_relat_1(k7_relat_1(B_327,'#skF_5'))))
      | k7_relat_1(B_327,k1_relat_1(k7_relat_1(B_327,'#skF_5'))) = k7_relat_1('#skF_3',k1_relat_1(k7_relat_1(B_327,'#skF_5')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_327,'#skF_5')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(B_327)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_327) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_18751])).

tff(c_19319,plain,(
    ! [B_339] :
      ( k1_funct_1('#skF_3','#skF_1'('#skF_3',B_339,k1_relat_1(k7_relat_1(B_339,'#skF_5')))) = k1_funct_1('#skF_4','#skF_1'('#skF_3',B_339,k1_relat_1(k7_relat_1(B_339,'#skF_5'))))
      | k7_relat_1(B_339,k1_relat_1(k7_relat_1(B_339,'#skF_5'))) = k7_relat_1('#skF_3',k1_relat_1(k7_relat_1(B_339,'#skF_5')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_339,'#skF_5')),k1_relat_1('#skF_4'))
      | ~ v1_funct_1(B_339)
      | ~ v1_relat_1(B_339) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_18878])).

tff(c_19376,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5'))))
    | k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_4','#skF_5'))) = k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_19319])).

tff(c_19418,plain,
    ( k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5'))))
    | k7_relat_1('#skF_3','#skF_5') = k7_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_5467,c_5922,c_19376])).

tff(c_19419,plain,(
    k1_funct_1('#skF_3','#skF_1'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))) = k1_funct_1('#skF_4','#skF_1'('#skF_3','#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_19418])).

tff(c_24,plain,(
    ! [B_28,A_16,C_34] :
      ( k1_funct_1(B_28,'#skF_1'(A_16,B_28,C_34)) != k1_funct_1(A_16,'#skF_1'(A_16,B_28,C_34))
      | k7_relat_1(B_28,C_34) = k7_relat_1(A_16,C_34)
      | ~ r1_tarski(C_34,k1_relat_1(B_28))
      | ~ r1_tarski(C_34,k1_relat_1(A_16))
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20721,plain,
    ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_4','#skF_5'))) = k7_relat_1('#skF_4',k1_relat_1(k7_relat_1('#skF_4','#skF_5')))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_5')),k1_relat_1('#skF_4'))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_5')),k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_19419,c_24])).

tff(c_20726,plain,(
    k7_relat_1('#skF_3','#skF_5') = k7_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_326,c_40,c_326,c_5467,c_5922,c_20721])).

tff(c_20728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_20726])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:28:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.02/4.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.16/4.55  
% 12.16/4.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.16/4.56  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 12.16/4.56  
% 12.16/4.56  %Foreground sorts:
% 12.16/4.56  
% 12.16/4.56  
% 12.16/4.56  %Background operators:
% 12.16/4.56  
% 12.16/4.56  
% 12.16/4.56  %Foreground operators:
% 12.16/4.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.16/4.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.16/4.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.16/4.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.16/4.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.16/4.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.16/4.56  tff('#skF_5', type, '#skF_5': $i).
% 12.16/4.56  tff('#skF_3', type, '#skF_3': $i).
% 12.16/4.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.16/4.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.16/4.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.16/4.56  tff('#skF_4', type, '#skF_4': $i).
% 12.16/4.56  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.16/4.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.16/4.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.16/4.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.16/4.56  
% 12.28/4.58  tff(f_118, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (((k1_relat_1(A) = k1_relat_1(B)) & (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))) => (k7_relat_1(A, C) = k7_relat_1(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_funct_1)).
% 12.28/4.58  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 12.28/4.58  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 12.28/4.58  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 12.28/4.58  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_funct_1)).
% 12.28/4.58  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_relat_1)).
% 12.28/4.58  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 12.28/4.58  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 12.28/4.58  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((r1_tarski(C, k1_relat_1(A)) & r1_tarski(C, k1_relat_1(B))) => ((k7_relat_1(A, C) = k7_relat_1(B, C)) <=> (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t165_funct_1)).
% 12.28/4.58  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 12.28/4.58  tff(c_36, plain, (k7_relat_1('#skF_3', '#skF_5')!=k7_relat_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.28/4.58  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.28/4.58  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.28/4.58  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.28/4.58  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.28/4.58  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(k7_relat_1(B_10, A_9)), k1_relat_1(B_10)) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.28/4.58  tff(c_40, plain, (k1_relat_1('#skF_3')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.28/4.58  tff(c_176, plain, (![B_82, A_83]: (k1_relat_1(k7_relat_1(B_82, A_83))=A_83 | ~r1_tarski(A_83, k1_relat_1(B_82)) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_54])).
% 12.28/4.58  tff(c_196, plain, (![A_83]: (k1_relat_1(k7_relat_1('#skF_3', A_83))=A_83 | ~r1_tarski(A_83, k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_176])).
% 12.28/4.58  tff(c_211, plain, (![A_84]: (k1_relat_1(k7_relat_1('#skF_3', A_84))=A_84 | ~r1_tarski(A_84, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_196])).
% 12.28/4.58  tff(c_222, plain, (![A_9]: (k1_relat_1(k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_4', A_9))))=k1_relat_1(k7_relat_1('#skF_4', A_9)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_211])).
% 12.28/4.58  tff(c_303, plain, (![A_92]: (k1_relat_1(k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_4', A_92))))=k1_relat_1(k7_relat_1('#skF_4', A_92)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_222])).
% 12.28/4.58  tff(c_83, plain, (![B_63, A_64]: (r1_tarski(k1_relat_1(k7_relat_1(B_63, A_64)), k1_relat_1(B_63)) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.28/4.58  tff(c_86, plain, (![A_64]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_64)), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_83])).
% 12.28/4.58  tff(c_91, plain, (![A_64]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_64)), k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_86])).
% 12.28/4.58  tff(c_326, plain, (![A_92]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_4', A_92)), k1_relat_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_303, c_91])).
% 12.28/4.58  tff(c_18, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.28/4.58  tff(c_20, plain, (![A_15]: (v1_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.28/4.58  tff(c_34, plain, (![A_38]: (k1_relat_1(k6_relat_1(A_38))=A_38 | ~v1_funct_1(k6_relat_1(A_38)) | ~v1_relat_1(k6_relat_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.28/4.58  tff(c_50, plain, (![A_38]: (k1_relat_1(k6_relat_1(A_38))=A_38 | ~v1_relat_1(k6_relat_1(A_38)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_34])).
% 12.28/4.58  tff(c_54, plain, (![A_38]: (k1_relat_1(k6_relat_1(A_38))=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_50])).
% 12.28/4.58  tff(c_1052, plain, (![A_119, B_120]: (k7_relat_1(A_119, k1_relat_1(k7_relat_1(B_120, k1_relat_1(A_119))))=k7_relat_1(A_119, k1_relat_1(B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.28/4.58  tff(c_1236, plain, (![B_120]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1(B_120, k1_relat_1('#skF_4'))))=k7_relat_1('#skF_3', k1_relat_1(B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1052])).
% 12.28/4.58  tff(c_1418, plain, (![B_122]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1(B_122, k1_relat_1('#skF_4'))))=k7_relat_1('#skF_3', k1_relat_1(B_122)) | ~v1_relat_1(B_122))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1236])).
% 12.28/4.58  tff(c_10, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(k7_relat_1(B_8, A_7)), A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.28/4.58  tff(c_1469, plain, (![B_122]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', k1_relat_1(B_122))), k1_relat_1(k7_relat_1(B_122, k1_relat_1('#skF_4')))) | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_122))), inference(superposition, [status(thm), theory('equality')], [c_1418, c_10])).
% 12.28/4.58  tff(c_2731, plain, (![B_143]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', k1_relat_1(B_143))), k1_relat_1(k7_relat_1(B_143, k1_relat_1('#skF_4')))) | ~v1_relat_1(B_143))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1469])).
% 12.28/4.58  tff(c_2815, plain, (![A_38]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_38)), k1_relat_1(k7_relat_1(k6_relat_1(A_38), k1_relat_1('#skF_4')))) | ~v1_relat_1(k6_relat_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2731])).
% 12.28/4.58  tff(c_2846, plain, (![A_38]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_38)), k1_relat_1(k7_relat_1(k6_relat_1(A_38), k1_relat_1('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_2815])).
% 12.28/4.58  tff(c_1239, plain, (![A_38, B_120]: (k7_relat_1(k6_relat_1(A_38), k1_relat_1(k7_relat_1(B_120, A_38)))=k7_relat_1(k6_relat_1(A_38), k1_relat_1(B_120)) | ~v1_relat_1(B_120) | ~v1_relat_1(k6_relat_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1052])).
% 12.28/4.58  tff(c_4115, plain, (![A_170, B_171]: (k7_relat_1(k6_relat_1(A_170), k1_relat_1(k7_relat_1(B_171, A_170)))=k7_relat_1(k6_relat_1(A_170), k1_relat_1(B_171)) | ~v1_relat_1(B_171))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1239])).
% 12.28/4.58  tff(c_4191, plain, (![A_170, B_171]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_170), k1_relat_1(B_171))), k1_relat_1(k7_relat_1(B_171, A_170))) | ~v1_relat_1(k6_relat_1(A_170)) | ~v1_relat_1(B_171))), inference(superposition, [status(thm), theory('equality')], [c_4115, c_10])).
% 12.28/4.58  tff(c_4498, plain, (![A_178, B_179]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_178), k1_relat_1(B_179))), k1_relat_1(k7_relat_1(B_179, A_178))) | ~v1_relat_1(B_179))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_4191])).
% 12.28/4.58  tff(c_4654, plain, (![A_178]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_178), k1_relat_1('#skF_4'))), k1_relat_1(k7_relat_1('#skF_3', A_178))) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4498])).
% 12.28/4.58  tff(c_4714, plain, (![A_180]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(A_180), k1_relat_1('#skF_4'))), k1_relat_1(k7_relat_1('#skF_3', A_180))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4654])).
% 12.28/4.58  tff(c_96, plain, (![B_68, A_69]: (k7_relat_1(B_68, A_69)=B_68 | ~r1_tarski(k1_relat_1(B_68), A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.28/4.58  tff(c_114, plain, (![A_38, A_69]: (k7_relat_1(k6_relat_1(A_38), A_69)=k6_relat_1(A_38) | ~r1_tarski(A_38, A_69) | ~v1_relat_1(k6_relat_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_96])).
% 12.28/4.58  tff(c_122, plain, (![A_38, A_69]: (k7_relat_1(k6_relat_1(A_38), A_69)=k6_relat_1(A_38) | ~r1_tarski(A_38, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_114])).
% 12.28/4.58  tff(c_199, plain, (![A_38, A_83]: (k1_relat_1(k7_relat_1(k6_relat_1(A_38), A_83))=A_83 | ~r1_tarski(A_83, A_38) | ~v1_relat_1(k6_relat_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_176])).
% 12.28/4.58  tff(c_239, plain, (![A_88, A_89]: (k1_relat_1(k7_relat_1(k6_relat_1(A_88), A_89))=A_89 | ~r1_tarski(A_89, A_88))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_199])).
% 12.28/4.58  tff(c_272, plain, (![A_38, A_69]: (k1_relat_1(k6_relat_1(A_38))=A_69 | ~r1_tarski(A_69, A_38) | ~r1_tarski(A_38, A_69))), inference(superposition, [status(thm), theory('equality')], [c_122, c_239])).
% 12.28/4.58  tff(c_283, plain, (![A_69, A_38]: (A_69=A_38 | ~r1_tarski(A_69, A_38) | ~r1_tarski(A_38, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_272])).
% 12.28/4.58  tff(c_4724, plain, (![A_180]: (k1_relat_1(k7_relat_1(k6_relat_1(A_180), k1_relat_1('#skF_4')))=k1_relat_1(k7_relat_1('#skF_3', A_180)) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_180)), k1_relat_1(k7_relat_1(k6_relat_1(A_180), k1_relat_1('#skF_4')))))), inference(resolution, [status(thm)], [c_4714, c_283])).
% 12.28/4.58  tff(c_4824, plain, (![A_181]: (k1_relat_1(k7_relat_1(k6_relat_1(A_181), k1_relat_1('#skF_4')))=k1_relat_1(k7_relat_1('#skF_3', A_181)))), inference(demodulation, [status(thm), theory('equality')], [c_2846, c_4724])).
% 12.28/4.58  tff(c_2, plain, (![A_1, B_3]: (k7_relat_1(A_1, k1_relat_1(k7_relat_1(B_3, k1_relat_1(A_1))))=k7_relat_1(A_1, k1_relat_1(B_3)) | ~v1_relat_1(B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 12.28/4.58  tff(c_4890, plain, (![A_181]: (k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_3', A_181)))=k7_relat_1('#skF_4', k1_relat_1(k6_relat_1(A_181))) | ~v1_relat_1(k6_relat_1(A_181)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4824, c_2])).
% 12.28/4.58  tff(c_5005, plain, (![A_181]: (k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_3', A_181)))=k7_relat_1('#skF_4', A_181))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18, c_54, c_4890])).
% 12.28/4.58  tff(c_186, plain, (![A_64]: (k1_relat_1(k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_3', A_64))))=k1_relat_1(k7_relat_1('#skF_3', A_64)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_91, c_176])).
% 12.28/4.58  tff(c_204, plain, (![A_64]: (k1_relat_1(k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_3', A_64))))=k1_relat_1(k7_relat_1('#skF_3', A_64)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_186])).
% 12.28/4.58  tff(c_5289, plain, (![A_64]: (k1_relat_1(k7_relat_1('#skF_3', A_64))=k1_relat_1(k7_relat_1('#skF_4', A_64)))), inference(demodulation, [status(thm), theory('equality')], [c_5005, c_204])).
% 12.28/4.58  tff(c_5467, plain, (![A_181]: (k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_4', A_181)))=k7_relat_1('#skF_4', A_181))), inference(demodulation, [status(thm), theory('equality')], [c_5289, c_5005])).
% 12.28/4.58  tff(c_1314, plain, (![B_120]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1(B_120, k1_relat_1('#skF_4'))))=k7_relat_1('#skF_3', k1_relat_1(B_120)) | ~v1_relat_1(B_120))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1236])).
% 12.28/4.58  tff(c_4884, plain, (![A_181]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', A_181)))=k7_relat_1('#skF_3', k1_relat_1(k6_relat_1(A_181))) | ~v1_relat_1(k6_relat_1(A_181)))), inference(superposition, [status(thm), theory('equality')], [c_4824, c_1314])).
% 12.28/4.58  tff(c_5003, plain, (![A_181]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', A_181)))=k7_relat_1('#skF_3', A_181))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_54, c_4884])).
% 12.28/4.58  tff(c_5922, plain, (![A_181]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_4', A_181)))=k7_relat_1('#skF_3', A_181))), inference(demodulation, [status(thm), theory('equality')], [c_5289, c_5003])).
% 12.28/4.58  tff(c_2255, plain, (![A_132, B_133, C_134]: (r2_hidden('#skF_1'(A_132, B_133, C_134), C_134) | k7_relat_1(B_133, C_134)=k7_relat_1(A_132, C_134) | ~r1_tarski(C_134, k1_relat_1(B_133)) | ~r1_tarski(C_134, k1_relat_1(A_132)) | ~v1_funct_1(B_133) | ~v1_relat_1(B_133) | ~v1_funct_1(A_132) | ~v1_relat_1(A_132))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.28/4.58  tff(c_8, plain, (![A_4, B_5, C_6]: (r2_hidden(A_4, B_5) | ~r2_hidden(A_4, k1_relat_1(k7_relat_1(C_6, B_5))) | ~v1_relat_1(C_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.28/4.58  tff(c_14559, plain, (![A_286, B_287, C_288, B_289]: (r2_hidden('#skF_1'(A_286, B_287, k1_relat_1(k7_relat_1(C_288, B_289))), B_289) | ~v1_relat_1(C_288) | k7_relat_1(B_287, k1_relat_1(k7_relat_1(C_288, B_289)))=k7_relat_1(A_286, k1_relat_1(k7_relat_1(C_288, B_289))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_288, B_289)), k1_relat_1(B_287)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_288, B_289)), k1_relat_1(A_286)) | ~v1_funct_1(B_287) | ~v1_relat_1(B_287) | ~v1_funct_1(A_286) | ~v1_relat_1(A_286))), inference(resolution, [status(thm)], [c_2255, c_8])).
% 12.28/4.58  tff(c_38, plain, (![D_54]: (k1_funct_1('#skF_3', D_54)=k1_funct_1('#skF_4', D_54) | ~r2_hidden(D_54, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.28/4.58  tff(c_16178, plain, (![A_296, B_297, C_298]: (k1_funct_1('#skF_3', '#skF_1'(A_296, B_297, k1_relat_1(k7_relat_1(C_298, '#skF_5'))))=k1_funct_1('#skF_4', '#skF_1'(A_296, B_297, k1_relat_1(k7_relat_1(C_298, '#skF_5')))) | ~v1_relat_1(C_298) | k7_relat_1(B_297, k1_relat_1(k7_relat_1(C_298, '#skF_5')))=k7_relat_1(A_296, k1_relat_1(k7_relat_1(C_298, '#skF_5'))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_298, '#skF_5')), k1_relat_1(B_297)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_298, '#skF_5')), k1_relat_1(A_296)) | ~v1_funct_1(B_297) | ~v1_relat_1(B_297) | ~v1_funct_1(A_296) | ~v1_relat_1(A_296))), inference(resolution, [status(thm)], [c_14559, c_38])).
% 12.28/4.58  tff(c_18751, plain, (![A_326, B_327]: (k1_funct_1('#skF_3', '#skF_1'(A_326, B_327, k1_relat_1(k7_relat_1(B_327, '#skF_5'))))=k1_funct_1('#skF_4', '#skF_1'(A_326, B_327, k1_relat_1(k7_relat_1(B_327, '#skF_5')))) | k7_relat_1(B_327, k1_relat_1(k7_relat_1(B_327, '#skF_5')))=k7_relat_1(A_326, k1_relat_1(k7_relat_1(B_327, '#skF_5'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_327, '#skF_5')), k1_relat_1(A_326)) | ~v1_funct_1(B_327) | ~v1_funct_1(A_326) | ~v1_relat_1(A_326) | ~v1_relat_1(B_327))), inference(resolution, [status(thm)], [c_12, c_16178])).
% 12.28/4.58  tff(c_18878, plain, (![B_327]: (k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_327, k1_relat_1(k7_relat_1(B_327, '#skF_5'))))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', B_327, k1_relat_1(k7_relat_1(B_327, '#skF_5')))) | k7_relat_1(B_327, k1_relat_1(k7_relat_1(B_327, '#skF_5')))=k7_relat_1('#skF_3', k1_relat_1(k7_relat_1(B_327, '#skF_5'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_327, '#skF_5')), k1_relat_1('#skF_4')) | ~v1_funct_1(B_327) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_327))), inference(superposition, [status(thm), theory('equality')], [c_40, c_18751])).
% 12.28/4.58  tff(c_19319, plain, (![B_339]: (k1_funct_1('#skF_3', '#skF_1'('#skF_3', B_339, k1_relat_1(k7_relat_1(B_339, '#skF_5'))))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', B_339, k1_relat_1(k7_relat_1(B_339, '#skF_5')))) | k7_relat_1(B_339, k1_relat_1(k7_relat_1(B_339, '#skF_5')))=k7_relat_1('#skF_3', k1_relat_1(k7_relat_1(B_339, '#skF_5'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_339, '#skF_5')), k1_relat_1('#skF_4')) | ~v1_funct_1(B_339) | ~v1_relat_1(B_339))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_18878])).
% 12.28/4.58  tff(c_19376, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5')))) | k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_4', '#skF_5')))=k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_19319])).
% 12.28/4.58  tff(c_19418, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5')))) | k7_relat_1('#skF_3', '#skF_5')=k7_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_5467, c_5922, c_19376])).
% 12.28/4.58  tff(c_19419, plain, (k1_funct_1('#skF_3', '#skF_1'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))))=k1_funct_1('#skF_4', '#skF_1'('#skF_3', '#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_36, c_19418])).
% 12.28/4.58  tff(c_24, plain, (![B_28, A_16, C_34]: (k1_funct_1(B_28, '#skF_1'(A_16, B_28, C_34))!=k1_funct_1(A_16, '#skF_1'(A_16, B_28, C_34)) | k7_relat_1(B_28, C_34)=k7_relat_1(A_16, C_34) | ~r1_tarski(C_34, k1_relat_1(B_28)) | ~r1_tarski(C_34, k1_relat_1(A_16)) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.28/4.58  tff(c_20721, plain, (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_4', '#skF_5')))=k7_relat_1('#skF_4', k1_relat_1(k7_relat_1('#skF_4', '#skF_5'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_5')), k1_relat_1('#skF_4')) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_5')), k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_19419, c_24])).
% 12.28/4.58  tff(c_20726, plain, (k7_relat_1('#skF_3', '#skF_5')=k7_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_326, c_40, c_326, c_5467, c_5922, c_20721])).
% 12.28/4.58  tff(c_20728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_20726])).
% 12.28/4.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.28/4.58  
% 12.28/4.58  Inference rules
% 12.28/4.58  ----------------------
% 12.28/4.58  #Ref     : 2
% 12.28/4.58  #Sup     : 4893
% 12.28/4.58  #Fact    : 0
% 12.28/4.58  #Define  : 0
% 12.28/4.58  #Split   : 6
% 12.28/4.58  #Chain   : 0
% 12.28/4.58  #Close   : 0
% 12.28/4.58  
% 12.28/4.58  Ordering : KBO
% 12.28/4.58  
% 12.28/4.58  Simplification rules
% 12.28/4.58  ----------------------
% 12.28/4.58  #Subsume      : 996
% 12.28/4.58  #Demod        : 6432
% 12.28/4.58  #Tautology    : 1125
% 12.28/4.58  #SimpNegUnit  : 26
% 12.28/4.58  #BackRed      : 45
% 12.28/4.58  
% 12.28/4.58  #Partial instantiations: 0
% 12.28/4.58  #Strategies tried      : 1
% 12.28/4.58  
% 12.28/4.58  Timing (in seconds)
% 12.28/4.58  ----------------------
% 12.28/4.58  Preprocessing        : 0.33
% 12.28/4.58  Parsing              : 0.17
% 12.28/4.58  CNF conversion       : 0.03
% 12.28/4.58  Main loop            : 3.47
% 12.28/4.58  Inferencing          : 0.80
% 12.28/4.58  Reduction            : 1.49
% 12.28/4.58  Demodulation         : 1.22
% 12.28/4.58  BG Simplification    : 0.13
% 12.28/4.58  Subsumption          : 0.87
% 12.28/4.58  Abstraction          : 0.23
% 12.28/4.58  MUC search           : 0.00
% 12.28/4.58  Cooper               : 0.00
% 12.28/4.58  Total                : 3.84
% 12.28/4.58  Index Insertion      : 0.00
% 12.28/4.58  Index Deletion       : 0.00
% 12.28/4.58  Index Matching       : 0.00
% 12.28/4.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
