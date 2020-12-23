%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:30 EST 2020

% Result     : Theorem 10.01s
% Output     : CNFRefutation 10.01s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 559 expanded)
%              Number of leaves         :   25 ( 206 expanded)
%              Depth                    :   21
%              Number of atoms          :  192 (1648 expanded)
%              Number of equality atoms :   63 ( 605 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_103,negated_conjecture,(
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

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_36,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_83,axiom,(
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

tff(f_44,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(c_30,plain,(
    k7_relat_1('#skF_2','#skF_4') != k7_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_11,A_10)),k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    k1_relat_1('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_82,plain,(
    ! [B_61,A_62] :
      ( k1_relat_1(k7_relat_1(B_61,A_62)) = A_62
      | ~ r1_tarski(A_62,k1_relat_1(B_61))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_102,plain,(
    ! [A_62] :
      ( k1_relat_1(k7_relat_1('#skF_2',A_62)) = A_62
      | ~ r1_tarski(A_62,k1_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_82])).

tff(c_154,plain,(
    ! [A_67] :
      ( k1_relat_1(k7_relat_1('#skF_2',A_67)) = A_67
      | ~ r1_tarski(A_67,k1_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_102])).

tff(c_165,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3',A_10)))) = k1_relat_1(k7_relat_1('#skF_3',A_10))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_16,c_154])).

tff(c_191,plain,(
    ! [A_72] : k1_relat_1(k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3',A_72)))) = k1_relat_1(k7_relat_1('#skF_3',A_72)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_165])).

tff(c_68,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_55,A_56)),k1_relat_1(B_55))
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_74,plain,(
    ! [A_56] :
      ( r1_tarski(k1_relat_1(k7_relat_1('#skF_2',A_56)),k1_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_68])).

tff(c_78,plain,(
    ! [A_56] : r1_tarski(k1_relat_1(k7_relat_1('#skF_2',A_56)),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_74])).

tff(c_208,plain,(
    ! [A_72] : r1_tarski(k1_relat_1(k7_relat_1('#skF_3',A_72)),k1_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_78])).

tff(c_20,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_4] : k1_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_443,plain,(
    ! [A_89,B_90] :
      ( k7_relat_1(A_89,k1_relat_1(k7_relat_1(B_90,k1_relat_1(A_89)))) = k7_relat_1(A_89,k1_relat_1(B_90))
      | ~ v1_relat_1(B_90)
      | ~ v1_relat_1(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_565,plain,(
    ! [A_4,B_90] :
      ( k7_relat_1(k6_relat_1(A_4),k1_relat_1(k7_relat_1(B_90,A_4))) = k7_relat_1(k6_relat_1(A_4),k1_relat_1(B_90))
      | ~ v1_relat_1(B_90)
      | ~ v1_relat_1(k6_relat_1(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_443])).

tff(c_612,plain,(
    ! [A_4,B_90] :
      ( k7_relat_1(k6_relat_1(A_4),k1_relat_1(k7_relat_1(B_90,A_4))) = k7_relat_1(k6_relat_1(A_4),k1_relat_1(B_90))
      | ~ v1_relat_1(B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_565])).

tff(c_568,plain,(
    ! [B_90] :
      ( k7_relat_1('#skF_2',k1_relat_1(k7_relat_1(B_90,k1_relat_1('#skF_3')))) = k7_relat_1('#skF_2',k1_relat_1(B_90))
      | ~ v1_relat_1(B_90)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_443])).

tff(c_614,plain,(
    ! [B_90] :
      ( k7_relat_1('#skF_2',k1_relat_1(k7_relat_1(B_90,k1_relat_1('#skF_3')))) = k7_relat_1('#skF_2',k1_relat_1(B_90))
      | ~ v1_relat_1(B_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_568])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1167,plain,(
    ! [B_103] :
      ( k1_relat_1(k7_relat_1('#skF_2',k1_relat_1(k7_relat_1(B_103,k1_relat_1('#skF_3'))))) = k1_relat_1(k7_relat_1(B_103,k1_relat_1('#skF_3')))
      | ~ v1_relat_1(B_103) ) ),
    inference(resolution,[status(thm)],[c_14,c_154])).

tff(c_5756,plain,(
    ! [B_206] :
      ( k1_relat_1(k7_relat_1(B_206,k1_relat_1('#skF_3'))) = k1_relat_1(k7_relat_1('#skF_2',k1_relat_1(B_206)))
      | ~ v1_relat_1(B_206)
      | ~ v1_relat_1(B_206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_1167])).

tff(c_2,plain,(
    ! [A_1,B_3] :
      ( k7_relat_1(A_1,k1_relat_1(k7_relat_1(B_3,k1_relat_1(A_1)))) = k7_relat_1(A_1,k1_relat_1(B_3))
      | ~ v1_relat_1(B_3)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6043,plain,(
    ! [B_206] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_2',k1_relat_1(B_206)))) = k7_relat_1('#skF_3',k1_relat_1(B_206))
      | ~ v1_relat_1(B_206)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_206)
      | ~ v1_relat_1(B_206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5756,c_2])).

tff(c_8162,plain,(
    ! [B_226] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_2',k1_relat_1(B_226)))) = k7_relat_1('#skF_3',k1_relat_1(B_226))
      | ~ v1_relat_1(B_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6043])).

tff(c_8344,plain,(
    ! [A_4] :
      ( k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_2',A_4))) = k7_relat_1('#skF_3',k1_relat_1(k6_relat_1(A_4)))
      | ~ v1_relat_1(k6_relat_1(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_8162])).

tff(c_8426,plain,(
    ! [A_4] : k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_2',A_4))) = k7_relat_1('#skF_3',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4,c_8344])).

tff(c_85,plain,(
    ! [A_56] :
      ( k1_relat_1(k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_2',A_56)))) = k1_relat_1(k7_relat_1('#skF_2',A_56))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_78,c_82])).

tff(c_105,plain,(
    ! [A_56] : k1_relat_1(k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_2',A_56)))) = k1_relat_1(k7_relat_1('#skF_2',A_56)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_85])).

tff(c_8614,plain,(
    ! [A_56] : k1_relat_1(k7_relat_1('#skF_2',A_56)) = k1_relat_1(k7_relat_1('#skF_3',A_56)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8426,c_105])).

tff(c_8848,plain,(
    ! [A_229] : k1_relat_1(k7_relat_1('#skF_2',A_229)) = k1_relat_1(k7_relat_1('#skF_3',A_229)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8426,c_105])).

tff(c_3957,plain,(
    ! [B_180,B_181] :
      ( k1_relat_1(k7_relat_1(B_180,k1_relat_1(k7_relat_1(B_181,k1_relat_1(B_180))))) = k1_relat_1(k7_relat_1(B_181,k1_relat_1(B_180)))
      | ~ v1_relat_1(B_180)
      | ~ v1_relat_1(B_181) ) ),
    inference(resolution,[status(thm)],[c_14,c_82])).

tff(c_4307,plain,(
    ! [A_4,B_181] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_4),k1_relat_1(k7_relat_1(B_181,A_4)))) = k1_relat_1(k7_relat_1(B_181,k1_relat_1(k6_relat_1(A_4))))
      | ~ v1_relat_1(k6_relat_1(A_4))
      | ~ v1_relat_1(B_181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_3957])).

tff(c_4437,plain,(
    ! [A_4,B_181] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_4),k1_relat_1(k7_relat_1(B_181,A_4)))) = k1_relat_1(k7_relat_1(B_181,A_4))
      | ~ v1_relat_1(B_181) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4,c_4307])).

tff(c_8881,plain,(
    ! [A_229] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_229),k1_relat_1(k7_relat_1('#skF_3',A_229)))) = k1_relat_1(k7_relat_1('#skF_2',A_229))
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8848,c_4437])).

tff(c_11054,plain,(
    ! [A_255] : k1_relat_1(k7_relat_1(k6_relat_1(A_255),k1_relat_1(k7_relat_1('#skF_3',A_255)))) = k1_relat_1(k7_relat_1('#skF_3',A_255)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8614,c_8881])).

tff(c_11256,plain,(
    ! [A_4] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_4),k1_relat_1('#skF_3'))) = k1_relat_1(k7_relat_1('#skF_3',A_4))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_11054])).

tff(c_11367,plain,(
    ! [A_256] : k1_relat_1(k7_relat_1(k6_relat_1(A_256),k1_relat_1('#skF_3'))) = k1_relat_1(k7_relat_1('#skF_3',A_256)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_11256])).

tff(c_11533,plain,(
    ! [A_256] :
      ( k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3',A_256))) = k7_relat_1('#skF_2',k1_relat_1(k6_relat_1(A_256)))
      | ~ v1_relat_1(k6_relat_1(A_256)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11367,c_614])).

tff(c_11655,plain,(
    ! [A_256] : k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3',A_256))) = k7_relat_1('#skF_2',A_256) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_4,c_11533])).

tff(c_8819,plain,(
    ! [A_4] : k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3',A_4))) = k7_relat_1('#skF_3',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8614,c_8426])).

tff(c_1794,plain,(
    ! [A_111,B_112,C_113] :
      ( r2_hidden('#skF_1'(A_111,B_112,C_113),C_113)
      | k7_relat_1(B_112,C_113) = k7_relat_1(A_111,C_113)
      | ~ r1_tarski(C_113,k1_relat_1(B_112))
      | ~ r1_tarski(C_113,k1_relat_1(A_111))
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112)
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [A_5,B_6,C_7] :
      ( r2_hidden(A_5,B_6)
      | ~ r2_hidden(A_5,k1_relat_1(k7_relat_1(C_7,B_6)))
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_9732,plain,(
    ! [A_239,B_240,C_241,B_242] :
      ( r2_hidden('#skF_1'(A_239,B_240,k1_relat_1(k7_relat_1(C_241,B_242))),B_242)
      | ~ v1_relat_1(C_241)
      | k7_relat_1(B_240,k1_relat_1(k7_relat_1(C_241,B_242))) = k7_relat_1(A_239,k1_relat_1(k7_relat_1(C_241,B_242)))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_241,B_242)),k1_relat_1(B_240))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_241,B_242)),k1_relat_1(A_239))
      | ~ v1_funct_1(B_240)
      | ~ v1_relat_1(B_240)
      | ~ v1_funct_1(A_239)
      | ~ v1_relat_1(A_239) ) ),
    inference(resolution,[status(thm)],[c_1794,c_12])).

tff(c_32,plain,(
    ! [D_48] :
      ( k1_funct_1('#skF_2',D_48) = k1_funct_1('#skF_3',D_48)
      | ~ r2_hidden(D_48,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_10019,plain,(
    ! [A_246,B_247,C_248] :
      ( k1_funct_1('#skF_2','#skF_1'(A_246,B_247,k1_relat_1(k7_relat_1(C_248,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'(A_246,B_247,k1_relat_1(k7_relat_1(C_248,'#skF_4'))))
      | ~ v1_relat_1(C_248)
      | k7_relat_1(B_247,k1_relat_1(k7_relat_1(C_248,'#skF_4'))) = k7_relat_1(A_246,k1_relat_1(k7_relat_1(C_248,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_248,'#skF_4')),k1_relat_1(B_247))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_248,'#skF_4')),k1_relat_1(A_246))
      | ~ v1_funct_1(B_247)
      | ~ v1_relat_1(B_247)
      | ~ v1_funct_1(A_246)
      | ~ v1_relat_1(A_246) ) ),
    inference(resolution,[status(thm)],[c_9732,c_32])).

tff(c_13649,plain,(
    ! [A_278,B_279] :
      ( k1_funct_1('#skF_2','#skF_1'(A_278,B_279,k1_relat_1(k7_relat_1(B_279,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'(A_278,B_279,k1_relat_1(k7_relat_1(B_279,'#skF_4'))))
      | k7_relat_1(B_279,k1_relat_1(k7_relat_1(B_279,'#skF_4'))) = k7_relat_1(A_278,k1_relat_1(k7_relat_1(B_279,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_279,'#skF_4')),k1_relat_1(A_278))
      | ~ v1_funct_1(B_279)
      | ~ v1_funct_1(A_278)
      | ~ v1_relat_1(A_278)
      | ~ v1_relat_1(B_279) ) ),
    inference(resolution,[status(thm)],[c_16,c_10019])).

tff(c_13750,plain,(
    ! [B_279] :
      ( k1_funct_1('#skF_2','#skF_1'('#skF_2',B_279,k1_relat_1(k7_relat_1(B_279,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2',B_279,k1_relat_1(k7_relat_1(B_279,'#skF_4'))))
      | k7_relat_1(B_279,k1_relat_1(k7_relat_1(B_279,'#skF_4'))) = k7_relat_1('#skF_2',k1_relat_1(k7_relat_1(B_279,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_279,'#skF_4')),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(B_279)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(B_279) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_13649])).

tff(c_14614,plain,(
    ! [B_286] :
      ( k1_funct_1('#skF_2','#skF_1'('#skF_2',B_286,k1_relat_1(k7_relat_1(B_286,'#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2',B_286,k1_relat_1(k7_relat_1(B_286,'#skF_4'))))
      | k7_relat_1(B_286,k1_relat_1(k7_relat_1(B_286,'#skF_4'))) = k7_relat_1('#skF_2',k1_relat_1(k7_relat_1(B_286,'#skF_4')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(B_286,'#skF_4')),k1_relat_1('#skF_3'))
      | ~ v1_funct_1(B_286)
      | ~ v1_relat_1(B_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_13750])).

tff(c_14656,plain,
    ( k1_funct_1('#skF_2','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))))
    | k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))) = k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_14614])).

tff(c_14693,plain,
    ( k1_funct_1('#skF_2','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))))
    | k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_11655,c_8819,c_14656])).

tff(c_14694,plain,(
    k1_funct_1('#skF_2','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) = k1_funct_1('#skF_3','#skF_1'('#skF_2','#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_14693])).

tff(c_26,plain,(
    ! [B_27,A_15,C_33] :
      ( k1_funct_1(B_27,'#skF_1'(A_15,B_27,C_33)) != k1_funct_1(A_15,'#skF_1'(A_15,B_27,C_33))
      | k7_relat_1(B_27,C_33) = k7_relat_1(A_15,C_33)
      | ~ r1_tarski(C_33,k1_relat_1(B_27))
      | ~ r1_tarski(C_33,k1_relat_1(A_15))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_15001,plain,
    ( k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_3','#skF_4'))) = k7_relat_1('#skF_3',k1_relat_1(k7_relat_1('#skF_3','#skF_4')))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_4')),k1_relat_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_3','#skF_4')),k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_14694,c_26])).

tff(c_15006,plain,(
    k7_relat_1('#skF_2','#skF_4') = k7_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_208,c_34,c_208,c_11655,c_8819,c_15001])).

tff(c_15008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_15006])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:36:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.01/3.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.01/3.54  
% 10.01/3.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.01/3.54  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 10.01/3.54  
% 10.01/3.54  %Foreground sorts:
% 10.01/3.54  
% 10.01/3.54  
% 10.01/3.54  %Background operators:
% 10.01/3.54  
% 10.01/3.54  
% 10.01/3.54  %Foreground operators:
% 10.01/3.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.01/3.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.01/3.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.01/3.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.01/3.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.01/3.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.01/3.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.01/3.54  tff('#skF_2', type, '#skF_2': $i).
% 10.01/3.54  tff('#skF_3', type, '#skF_3': $i).
% 10.01/3.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 10.01/3.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.01/3.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.01/3.54  tff('#skF_4', type, '#skF_4': $i).
% 10.01/3.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.01/3.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.01/3.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.01/3.54  
% 10.01/3.56  tff(f_103, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (((k1_relat_1(A) = k1_relat_1(B)) & (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))) => (k7_relat_1(A, C) = k7_relat_1(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_funct_1)).
% 10.01/3.56  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 10.01/3.56  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 10.01/3.56  tff(f_62, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 10.01/3.56  tff(f_36, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 10.01/3.56  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_relat_1)).
% 10.01/3.56  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 10.01/3.56  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((r1_tarski(C, k1_relat_1(A)) & r1_tarski(C, k1_relat_1(B))) => ((k7_relat_1(A, C) = k7_relat_1(B, C)) <=> (![D]: (r2_hidden(D, C) => (k1_funct_1(A, D) = k1_funct_1(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t165_funct_1)).
% 10.01/3.56  tff(f_44, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 10.01/3.56  tff(c_30, plain, (k7_relat_1('#skF_2', '#skF_4')!=k7_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.01/3.56  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.01/3.56  tff(c_40, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.01/3.56  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.01/3.56  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.01/3.56  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(k7_relat_1(B_11, A_10)), k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.01/3.56  tff(c_34, plain, (k1_relat_1('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.01/3.56  tff(c_82, plain, (![B_61, A_62]: (k1_relat_1(k7_relat_1(B_61, A_62))=A_62 | ~r1_tarski(A_62, k1_relat_1(B_61)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.01/3.56  tff(c_102, plain, (![A_62]: (k1_relat_1(k7_relat_1('#skF_2', A_62))=A_62 | ~r1_tarski(A_62, k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_82])).
% 10.01/3.56  tff(c_154, plain, (![A_67]: (k1_relat_1(k7_relat_1('#skF_2', A_67))=A_67 | ~r1_tarski(A_67, k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_102])).
% 10.01/3.56  tff(c_165, plain, (![A_10]: (k1_relat_1(k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', A_10))))=k1_relat_1(k7_relat_1('#skF_3', A_10)) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_154])).
% 10.01/3.56  tff(c_191, plain, (![A_72]: (k1_relat_1(k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', A_72))))=k1_relat_1(k7_relat_1('#skF_3', A_72)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_165])).
% 10.01/3.56  tff(c_68, plain, (![B_55, A_56]: (r1_tarski(k1_relat_1(k7_relat_1(B_55, A_56)), k1_relat_1(B_55)) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_52])).
% 10.01/3.56  tff(c_74, plain, (![A_56]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_2', A_56)), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_68])).
% 10.01/3.56  tff(c_78, plain, (![A_56]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_2', A_56)), k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_74])).
% 10.01/3.56  tff(c_208, plain, (![A_72]: (r1_tarski(k1_relat_1(k7_relat_1('#skF_3', A_72)), k1_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_191, c_78])).
% 10.01/3.56  tff(c_20, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.01/3.56  tff(c_4, plain, (![A_4]: (k1_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.01/3.56  tff(c_443, plain, (![A_89, B_90]: (k7_relat_1(A_89, k1_relat_1(k7_relat_1(B_90, k1_relat_1(A_89))))=k7_relat_1(A_89, k1_relat_1(B_90)) | ~v1_relat_1(B_90) | ~v1_relat_1(A_89))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.01/3.56  tff(c_565, plain, (![A_4, B_90]: (k7_relat_1(k6_relat_1(A_4), k1_relat_1(k7_relat_1(B_90, A_4)))=k7_relat_1(k6_relat_1(A_4), k1_relat_1(B_90)) | ~v1_relat_1(B_90) | ~v1_relat_1(k6_relat_1(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_443])).
% 10.01/3.56  tff(c_612, plain, (![A_4, B_90]: (k7_relat_1(k6_relat_1(A_4), k1_relat_1(k7_relat_1(B_90, A_4)))=k7_relat_1(k6_relat_1(A_4), k1_relat_1(B_90)) | ~v1_relat_1(B_90))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_565])).
% 10.01/3.56  tff(c_568, plain, (![B_90]: (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1(B_90, k1_relat_1('#skF_3'))))=k7_relat_1('#skF_2', k1_relat_1(B_90)) | ~v1_relat_1(B_90) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_443])).
% 10.01/3.56  tff(c_614, plain, (![B_90]: (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1(B_90, k1_relat_1('#skF_3'))))=k7_relat_1('#skF_2', k1_relat_1(B_90)) | ~v1_relat_1(B_90))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_568])).
% 10.01/3.56  tff(c_14, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.01/3.56  tff(c_1167, plain, (![B_103]: (k1_relat_1(k7_relat_1('#skF_2', k1_relat_1(k7_relat_1(B_103, k1_relat_1('#skF_3')))))=k1_relat_1(k7_relat_1(B_103, k1_relat_1('#skF_3'))) | ~v1_relat_1(B_103))), inference(resolution, [status(thm)], [c_14, c_154])).
% 10.01/3.56  tff(c_5756, plain, (![B_206]: (k1_relat_1(k7_relat_1(B_206, k1_relat_1('#skF_3')))=k1_relat_1(k7_relat_1('#skF_2', k1_relat_1(B_206))) | ~v1_relat_1(B_206) | ~v1_relat_1(B_206))), inference(superposition, [status(thm), theory('equality')], [c_614, c_1167])).
% 10.01/3.56  tff(c_2, plain, (![A_1, B_3]: (k7_relat_1(A_1, k1_relat_1(k7_relat_1(B_3, k1_relat_1(A_1))))=k7_relat_1(A_1, k1_relat_1(B_3)) | ~v1_relat_1(B_3) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.01/3.56  tff(c_6043, plain, (![B_206]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_2', k1_relat_1(B_206))))=k7_relat_1('#skF_3', k1_relat_1(B_206)) | ~v1_relat_1(B_206) | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_206) | ~v1_relat_1(B_206))), inference(superposition, [status(thm), theory('equality')], [c_5756, c_2])).
% 10.01/3.56  tff(c_8162, plain, (![B_226]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_2', k1_relat_1(B_226))))=k7_relat_1('#skF_3', k1_relat_1(B_226)) | ~v1_relat_1(B_226))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6043])).
% 10.01/3.56  tff(c_8344, plain, (![A_4]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_2', A_4)))=k7_relat_1('#skF_3', k1_relat_1(k6_relat_1(A_4))) | ~v1_relat_1(k6_relat_1(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_8162])).
% 10.01/3.56  tff(c_8426, plain, (![A_4]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_2', A_4)))=k7_relat_1('#skF_3', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4, c_8344])).
% 10.01/3.56  tff(c_85, plain, (![A_56]: (k1_relat_1(k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_2', A_56))))=k1_relat_1(k7_relat_1('#skF_2', A_56)) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_78, c_82])).
% 10.01/3.56  tff(c_105, plain, (![A_56]: (k1_relat_1(k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_2', A_56))))=k1_relat_1(k7_relat_1('#skF_2', A_56)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_85])).
% 10.01/3.56  tff(c_8614, plain, (![A_56]: (k1_relat_1(k7_relat_1('#skF_2', A_56))=k1_relat_1(k7_relat_1('#skF_3', A_56)))), inference(demodulation, [status(thm), theory('equality')], [c_8426, c_105])).
% 10.01/3.56  tff(c_8848, plain, (![A_229]: (k1_relat_1(k7_relat_1('#skF_2', A_229))=k1_relat_1(k7_relat_1('#skF_3', A_229)))), inference(demodulation, [status(thm), theory('equality')], [c_8426, c_105])).
% 10.01/3.56  tff(c_3957, plain, (![B_180, B_181]: (k1_relat_1(k7_relat_1(B_180, k1_relat_1(k7_relat_1(B_181, k1_relat_1(B_180)))))=k1_relat_1(k7_relat_1(B_181, k1_relat_1(B_180))) | ~v1_relat_1(B_180) | ~v1_relat_1(B_181))), inference(resolution, [status(thm)], [c_14, c_82])).
% 10.01/3.56  tff(c_4307, plain, (![A_4, B_181]: (k1_relat_1(k7_relat_1(k6_relat_1(A_4), k1_relat_1(k7_relat_1(B_181, A_4))))=k1_relat_1(k7_relat_1(B_181, k1_relat_1(k6_relat_1(A_4)))) | ~v1_relat_1(k6_relat_1(A_4)) | ~v1_relat_1(B_181))), inference(superposition, [status(thm), theory('equality')], [c_4, c_3957])).
% 10.01/3.56  tff(c_4437, plain, (![A_4, B_181]: (k1_relat_1(k7_relat_1(k6_relat_1(A_4), k1_relat_1(k7_relat_1(B_181, A_4))))=k1_relat_1(k7_relat_1(B_181, A_4)) | ~v1_relat_1(B_181))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4, c_4307])).
% 10.01/3.56  tff(c_8881, plain, (![A_229]: (k1_relat_1(k7_relat_1(k6_relat_1(A_229), k1_relat_1(k7_relat_1('#skF_3', A_229))))=k1_relat_1(k7_relat_1('#skF_2', A_229)) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8848, c_4437])).
% 10.01/3.56  tff(c_11054, plain, (![A_255]: (k1_relat_1(k7_relat_1(k6_relat_1(A_255), k1_relat_1(k7_relat_1('#skF_3', A_255))))=k1_relat_1(k7_relat_1('#skF_3', A_255)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8614, c_8881])).
% 10.01/3.56  tff(c_11256, plain, (![A_4]: (k1_relat_1(k7_relat_1(k6_relat_1(A_4), k1_relat_1('#skF_3')))=k1_relat_1(k7_relat_1('#skF_3', A_4)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_612, c_11054])).
% 10.01/3.56  tff(c_11367, plain, (![A_256]: (k1_relat_1(k7_relat_1(k6_relat_1(A_256), k1_relat_1('#skF_3')))=k1_relat_1(k7_relat_1('#skF_3', A_256)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_11256])).
% 10.01/3.56  tff(c_11533, plain, (![A_256]: (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', A_256)))=k7_relat_1('#skF_2', k1_relat_1(k6_relat_1(A_256))) | ~v1_relat_1(k6_relat_1(A_256)))), inference(superposition, [status(thm), theory('equality')], [c_11367, c_614])).
% 10.01/3.56  tff(c_11655, plain, (![A_256]: (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', A_256)))=k7_relat_1('#skF_2', A_256))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_4, c_11533])).
% 10.01/3.56  tff(c_8819, plain, (![A_4]: (k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', A_4)))=k7_relat_1('#skF_3', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_8614, c_8426])).
% 10.01/3.56  tff(c_1794, plain, (![A_111, B_112, C_113]: (r2_hidden('#skF_1'(A_111, B_112, C_113), C_113) | k7_relat_1(B_112, C_113)=k7_relat_1(A_111, C_113) | ~r1_tarski(C_113, k1_relat_1(B_112)) | ~r1_tarski(C_113, k1_relat_1(A_111)) | ~v1_funct_1(B_112) | ~v1_relat_1(B_112) | ~v1_funct_1(A_111) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.01/3.56  tff(c_12, plain, (![A_5, B_6, C_7]: (r2_hidden(A_5, B_6) | ~r2_hidden(A_5, k1_relat_1(k7_relat_1(C_7, B_6))) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.01/3.56  tff(c_9732, plain, (![A_239, B_240, C_241, B_242]: (r2_hidden('#skF_1'(A_239, B_240, k1_relat_1(k7_relat_1(C_241, B_242))), B_242) | ~v1_relat_1(C_241) | k7_relat_1(B_240, k1_relat_1(k7_relat_1(C_241, B_242)))=k7_relat_1(A_239, k1_relat_1(k7_relat_1(C_241, B_242))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_241, B_242)), k1_relat_1(B_240)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_241, B_242)), k1_relat_1(A_239)) | ~v1_funct_1(B_240) | ~v1_relat_1(B_240) | ~v1_funct_1(A_239) | ~v1_relat_1(A_239))), inference(resolution, [status(thm)], [c_1794, c_12])).
% 10.01/3.56  tff(c_32, plain, (![D_48]: (k1_funct_1('#skF_2', D_48)=k1_funct_1('#skF_3', D_48) | ~r2_hidden(D_48, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.01/3.56  tff(c_10019, plain, (![A_246, B_247, C_248]: (k1_funct_1('#skF_2', '#skF_1'(A_246, B_247, k1_relat_1(k7_relat_1(C_248, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'(A_246, B_247, k1_relat_1(k7_relat_1(C_248, '#skF_4')))) | ~v1_relat_1(C_248) | k7_relat_1(B_247, k1_relat_1(k7_relat_1(C_248, '#skF_4')))=k7_relat_1(A_246, k1_relat_1(k7_relat_1(C_248, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(C_248, '#skF_4')), k1_relat_1(B_247)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_248, '#skF_4')), k1_relat_1(A_246)) | ~v1_funct_1(B_247) | ~v1_relat_1(B_247) | ~v1_funct_1(A_246) | ~v1_relat_1(A_246))), inference(resolution, [status(thm)], [c_9732, c_32])).
% 10.01/3.56  tff(c_13649, plain, (![A_278, B_279]: (k1_funct_1('#skF_2', '#skF_1'(A_278, B_279, k1_relat_1(k7_relat_1(B_279, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'(A_278, B_279, k1_relat_1(k7_relat_1(B_279, '#skF_4')))) | k7_relat_1(B_279, k1_relat_1(k7_relat_1(B_279, '#skF_4')))=k7_relat_1(A_278, k1_relat_1(k7_relat_1(B_279, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_279, '#skF_4')), k1_relat_1(A_278)) | ~v1_funct_1(B_279) | ~v1_funct_1(A_278) | ~v1_relat_1(A_278) | ~v1_relat_1(B_279))), inference(resolution, [status(thm)], [c_16, c_10019])).
% 10.01/3.56  tff(c_13750, plain, (![B_279]: (k1_funct_1('#skF_2', '#skF_1'('#skF_2', B_279, k1_relat_1(k7_relat_1(B_279, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', B_279, k1_relat_1(k7_relat_1(B_279, '#skF_4')))) | k7_relat_1(B_279, k1_relat_1(k7_relat_1(B_279, '#skF_4')))=k7_relat_1('#skF_2', k1_relat_1(k7_relat_1(B_279, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_279, '#skF_4')), k1_relat_1('#skF_3')) | ~v1_funct_1(B_279) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(B_279))), inference(superposition, [status(thm), theory('equality')], [c_34, c_13649])).
% 10.01/3.56  tff(c_14614, plain, (![B_286]: (k1_funct_1('#skF_2', '#skF_1'('#skF_2', B_286, k1_relat_1(k7_relat_1(B_286, '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', B_286, k1_relat_1(k7_relat_1(B_286, '#skF_4')))) | k7_relat_1(B_286, k1_relat_1(k7_relat_1(B_286, '#skF_4')))=k7_relat_1('#skF_2', k1_relat_1(k7_relat_1(B_286, '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1(B_286, '#skF_4')), k1_relat_1('#skF_3')) | ~v1_funct_1(B_286) | ~v1_relat_1(B_286))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_13750])).
% 10.01/3.56  tff(c_14656, plain, (k1_funct_1('#skF_2', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))) | k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))=k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_14614])).
% 10.01/3.56  tff(c_14693, plain, (k1_funct_1('#skF_2', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))) | k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_11655, c_8819, c_14656])).
% 10.01/3.56  tff(c_14694, plain, (k1_funct_1('#skF_2', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))=k1_funct_1('#skF_3', '#skF_1'('#skF_2', '#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_30, c_14693])).
% 10.01/3.56  tff(c_26, plain, (![B_27, A_15, C_33]: (k1_funct_1(B_27, '#skF_1'(A_15, B_27, C_33))!=k1_funct_1(A_15, '#skF_1'(A_15, B_27, C_33)) | k7_relat_1(B_27, C_33)=k7_relat_1(A_15, C_33) | ~r1_tarski(C_33, k1_relat_1(B_27)) | ~r1_tarski(C_33, k1_relat_1(A_15)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.01/3.56  tff(c_15001, plain, (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_3', '#skF_4')))=k7_relat_1('#skF_3', k1_relat_1(k7_relat_1('#skF_3', '#skF_4'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_4')), k1_relat_1('#skF_3')) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_3', '#skF_4')), k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_14694, c_26])).
% 10.01/3.56  tff(c_15006, plain, (k7_relat_1('#skF_2', '#skF_4')=k7_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_208, c_34, c_208, c_11655, c_8819, c_15001])).
% 10.01/3.56  tff(c_15008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_15006])).
% 10.01/3.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.01/3.56  
% 10.01/3.56  Inference rules
% 10.01/3.56  ----------------------
% 10.01/3.56  #Ref     : 2
% 10.01/3.56  #Sup     : 3491
% 10.01/3.56  #Fact    : 0
% 10.01/3.56  #Define  : 0
% 10.01/3.56  #Split   : 3
% 10.01/3.56  #Chain   : 0
% 10.01/3.56  #Close   : 0
% 10.01/3.56  
% 10.01/3.56  Ordering : KBO
% 10.01/3.56  
% 10.01/3.56  Simplification rules
% 10.01/3.56  ----------------------
% 10.01/3.56  #Subsume      : 536
% 10.01/3.56  #Demod        : 4190
% 10.01/3.56  #Tautology    : 872
% 10.01/3.56  #SimpNegUnit  : 16
% 10.01/3.56  #BackRed      : 28
% 10.01/3.56  
% 10.01/3.56  #Partial instantiations: 0
% 10.01/3.56  #Strategies tried      : 1
% 10.01/3.56  
% 10.01/3.56  Timing (in seconds)
% 10.01/3.56  ----------------------
% 10.01/3.56  Preprocessing        : 0.38
% 10.01/3.56  Parsing              : 0.20
% 10.01/3.56  CNF conversion       : 0.03
% 10.01/3.56  Main loop            : 2.40
% 10.01/3.56  Inferencing          : 0.61
% 10.01/3.56  Reduction            : 0.99
% 10.01/3.56  Demodulation         : 0.78
% 10.01/3.56  BG Simplification    : 0.11
% 10.01/3.56  Subsumption          : 0.57
% 10.01/3.56  Abstraction          : 0.15
% 10.01/3.56  MUC search           : 0.00
% 10.01/3.56  Cooper               : 0.00
% 10.01/3.56  Total                : 2.82
% 10.01/3.57  Index Insertion      : 0.00
% 10.01/3.57  Index Deletion       : 0.00
% 10.01/3.57  Index Matching       : 0.00
% 10.01/3.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
