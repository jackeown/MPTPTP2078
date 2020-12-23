%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:37 EST 2020

% Result     : Theorem 15.65s
% Output     : CNFRefutation 15.77s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 318 expanded)
%              Number of leaves         :   28 ( 120 expanded)
%              Depth                    :   20
%              Number of atoms          :  278 ( 972 expanded)
%              Number of equality atoms :   14 (  45 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k2_xboole_0 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_112,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_53,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_57,plain,(
    ! [B_7] : k2_xboole_0(B_7,B_7) = B_7 ),
    inference(resolution,[status(thm)],[c_12,c_53])).

tff(c_36,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2596,plain,(
    ! [A_199,C_200,B_201] :
      ( r2_hidden(A_199,k1_relat_1(C_200))
      | ~ r2_hidden(A_199,k1_relat_1(k5_relat_1(C_200,B_201)))
      | ~ v1_funct_1(C_200)
      | ~ v1_relat_1(C_200)
      | ~ v1_funct_1(B_201)
      | ~ v1_relat_1(B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_7594,plain,(
    ! [C_398,B_399,B_400] :
      ( r2_hidden('#skF_1'(k1_relat_1(k5_relat_1(C_398,B_399)),B_400),k1_relat_1(C_398))
      | ~ v1_funct_1(C_398)
      | ~ v1_relat_1(C_398)
      | ~ v1_funct_1(B_399)
      | ~ v1_relat_1(B_399)
      | r1_tarski(k1_relat_1(k5_relat_1(C_398,B_399)),B_400) ) ),
    inference(resolution,[status(thm)],[c_6,c_2596])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7607,plain,(
    ! [C_398,B_399] :
      ( ~ v1_funct_1(C_398)
      | ~ v1_relat_1(C_398)
      | ~ v1_funct_1(B_399)
      | ~ v1_relat_1(B_399)
      | r1_tarski(k1_relat_1(k5_relat_1(C_398,B_399)),k1_relat_1(C_398)) ) ),
    inference(resolution,[status(thm)],[c_7594,c_4])).

tff(c_404,plain,(
    ! [A_77,B_78] :
      ( k10_relat_1(A_77,k1_relat_1(B_78)) = k1_relat_1(k5_relat_1(A_77,B_78))
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k9_relat_1(B_22,k10_relat_1(B_22,A_21)),A_21)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4390,plain,(
    ! [A_288,B_289] :
      ( r1_tarski(k9_relat_1(A_288,k1_relat_1(k5_relat_1(A_288,B_289))),k1_relat_1(B_289))
      | ~ v1_funct_1(A_288)
      | ~ v1_relat_1(A_288)
      | ~ v1_relat_1(B_289)
      | ~ v1_relat_1(A_288) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_22])).

tff(c_24,plain,(
    ! [A_23,C_25,B_24] :
      ( r1_tarski(A_23,k10_relat_1(C_25,B_24))
      | ~ r1_tarski(k9_relat_1(C_25,A_23),B_24)
      | ~ r1_tarski(A_23,k1_relat_1(C_25))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12297,plain,(
    ! [A_517,B_518] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_517,B_518)),k10_relat_1(A_517,k1_relat_1(B_518)))
      | ~ r1_tarski(k1_relat_1(k5_relat_1(A_517,B_518)),k1_relat_1(A_517))
      | ~ v1_funct_1(A_517)
      | ~ v1_relat_1(B_518)
      | ~ v1_relat_1(A_517) ) ),
    inference(resolution,[status(thm)],[c_4390,c_24])).

tff(c_50,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_90,plain,(
    r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_94,plain,(
    k2_xboole_0('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) = k1_relat_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_90,c_16])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(k2_xboole_0(A_8,B_9),C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_249,plain,(
    ! [C_10] :
      ( r1_tarski('#skF_5',C_10)
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_2','#skF_3')),C_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_14])).

tff(c_12337,plain,
    ( r1_tarski('#skF_5',k10_relat_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_2','#skF_3')),k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12297,c_249])).

tff(c_12375,plain,
    ( r1_tarski('#skF_5',k10_relat_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_2','#skF_3')),k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_36,c_12337])).

tff(c_12379,plain,(
    ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_2','#skF_3')),k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_12375])).

tff(c_12382,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7607,c_12379])).

tff(c_12389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_38,c_36,c_12382])).

tff(c_12391,plain,(
    r1_tarski(k1_relat_1(k5_relat_1('#skF_2','#skF_3')),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_12375])).

tff(c_20,plain,(
    ! [A_18,B_20] :
      ( k10_relat_1(A_18,k1_relat_1(B_20)) = k1_relat_1(k5_relat_1(A_18,B_20))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12390,plain,(
    r1_tarski('#skF_5',k10_relat_1('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_12375])).

tff(c_12428,plain,(
    k2_xboole_0('#skF_5',k10_relat_1('#skF_2',k1_relat_1('#skF_3'))) = k10_relat_1('#skF_2',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_12390,c_16])).

tff(c_13225,plain,
    ( k2_xboole_0('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) = k10_relat_1('#skF_2',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_12428])).

tff(c_13247,plain,(
    k10_relat_1('#skF_2',k1_relat_1('#skF_3')) = k1_relat_1(k5_relat_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_94,c_13225])).

tff(c_326,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(k9_relat_1(B_67,k10_relat_1(B_67,A_68)),A_68)
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_416,plain,(
    ! [B_79,A_80] :
      ( k2_xboole_0(k9_relat_1(B_79,k10_relat_1(B_79,A_80)),A_80) = A_80
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_326,c_16])).

tff(c_67,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,C_39)
      | ~ r1_tarski(k2_xboole_0(A_38,B_40),C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [A_41,B_42] : r1_tarski(A_41,k2_xboole_0(A_41,B_42)) ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_87,plain,(
    ! [A_8,B_9,B_42] : r1_tarski(A_8,k2_xboole_0(k2_xboole_0(A_8,B_9),B_42)) ),
    inference(resolution,[status(thm)],[c_76,c_14])).

tff(c_434,plain,(
    ! [B_79,A_80,B_42] :
      ( r1_tarski(k9_relat_1(B_79,k10_relat_1(B_79,A_80)),k2_xboole_0(A_80,B_42))
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_87])).

tff(c_13485,plain,(
    ! [B_42] :
      ( r1_tarski(k9_relat_1('#skF_2',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))),k2_xboole_0(k1_relat_1('#skF_3'),B_42))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13247,c_434])).

tff(c_14378,plain,(
    ! [B_544] : r1_tarski(k9_relat_1('#skF_2',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))),k2_xboole_0(k1_relat_1('#skF_3'),B_544)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_13485])).

tff(c_14401,plain,(
    ! [B_544] :
      ( r1_tarski(k1_relat_1(k5_relat_1('#skF_2','#skF_3')),k10_relat_1('#skF_2',k2_xboole_0(k1_relat_1('#skF_3'),B_544)))
      | ~ r1_tarski(k1_relat_1(k5_relat_1('#skF_2','#skF_3')),k1_relat_1('#skF_2'))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14378,c_24])).

tff(c_14620,plain,(
    ! [B_547] : r1_tarski(k1_relat_1(k5_relat_1('#skF_2','#skF_3')),k10_relat_1('#skF_2',k2_xboole_0(k1_relat_1('#skF_3'),B_547))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_12391,c_14401])).

tff(c_14714,plain,(
    ! [B_547] : r1_tarski('#skF_5',k10_relat_1('#skF_2',k2_xboole_0(k1_relat_1('#skF_3'),B_547))) ),
    inference(resolution,[status(thm)],[c_14620,c_249])).

tff(c_2427,plain,(
    ! [C_186,A_187,D_188,B_189] :
      ( r1_tarski(k9_relat_1(C_186,A_187),k9_relat_1(D_188,B_189))
      | ~ r1_tarski(A_187,B_189)
      | ~ r1_tarski(C_186,D_188)
      | ~ v1_relat_1(D_188)
      | ~ v1_relat_1(C_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5089,plain,(
    ! [C_316,A_317,D_318,B_319] :
      ( k2_xboole_0(k9_relat_1(C_316,A_317),k9_relat_1(D_318,B_319)) = k9_relat_1(D_318,B_319)
      | ~ r1_tarski(A_317,B_319)
      | ~ r1_tarski(C_316,D_318)
      | ~ v1_relat_1(D_318)
      | ~ v1_relat_1(C_316) ) ),
    inference(resolution,[status(thm)],[c_2427,c_16])).

tff(c_11527,plain,(
    ! [C_500,B_501,D_502,C_504,A_503] :
      ( r1_tarski(k9_relat_1(C_500,A_503),C_504)
      | ~ r1_tarski(k9_relat_1(D_502,B_501),C_504)
      | ~ r1_tarski(A_503,B_501)
      | ~ r1_tarski(C_500,D_502)
      | ~ v1_relat_1(D_502)
      | ~ v1_relat_1(C_500) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5089,c_14])).

tff(c_37141,plain,(
    ! [C_948,A_949,A_950,B_951] :
      ( r1_tarski(k9_relat_1(C_948,A_949),A_950)
      | ~ r1_tarski(A_949,k10_relat_1(B_951,A_950))
      | ~ r1_tarski(C_948,B_951)
      | ~ v1_relat_1(C_948)
      | ~ v1_funct_1(B_951)
      | ~ v1_relat_1(B_951) ) ),
    inference(resolution,[status(thm)],[c_22,c_11527])).

tff(c_37174,plain,(
    ! [C_948,B_547] :
      ( r1_tarski(k9_relat_1(C_948,'#skF_5'),k2_xboole_0(k1_relat_1('#skF_3'),B_547))
      | ~ r1_tarski(C_948,'#skF_2')
      | ~ v1_relat_1(C_948)
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14714,c_37141])).

tff(c_37250,plain,(
    ! [C_952,B_953] :
      ( r1_tarski(k9_relat_1(C_952,'#skF_5'),k2_xboole_0(k1_relat_1('#skF_3'),B_953))
      | ~ r1_tarski(C_952,'#skF_2')
      | ~ v1_relat_1(C_952) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_37174])).

tff(c_37361,plain,(
    ! [C_954] :
      ( r1_tarski(k9_relat_1(C_954,'#skF_5'),k1_relat_1('#skF_3'))
      | ~ r1_tarski(C_954,'#skF_2')
      | ~ v1_relat_1(C_954) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_37250])).

tff(c_138,plain,(
    ! [C_52,B_53,A_54] :
      ( r2_hidden(C_52,B_53)
      | ~ r2_hidden(C_52,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_334,plain,(
    ! [A_69,B_70,B_71] :
      ( r2_hidden('#skF_1'(A_69,B_70),B_71)
      | ~ r1_tarski(A_69,B_71)
      | r1_tarski(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_138])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1043,plain,(
    ! [A_121,B_122,B_123,B_124] :
      ( r2_hidden('#skF_1'(A_121,B_122),B_123)
      | ~ r1_tarski(B_124,B_123)
      | ~ r1_tarski(A_121,B_124)
      | r1_tarski(A_121,B_122) ) ),
    inference(resolution,[status(thm)],[c_334,c_2])).

tff(c_1291,plain,(
    ! [A_140,B_141] :
      ( r2_hidden('#skF_1'(A_140,B_141),k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
      | ~ r1_tarski(A_140,'#skF_5')
      | r1_tarski(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_90,c_1043])).

tff(c_30,plain,(
    ! [A_26,C_29,B_27] :
      ( r2_hidden(A_26,k1_relat_1(C_29))
      | ~ r2_hidden(A_26,k1_relat_1(k5_relat_1(C_29,B_27)))
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1294,plain,(
    ! [A_140,B_141] :
      ( r2_hidden('#skF_1'(A_140,B_141),k1_relat_1('#skF_2'))
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_140,'#skF_5')
      | r1_tarski(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_1291,c_30])).

tff(c_1994,plain,(
    ! [A_169,B_170] :
      ( r2_hidden('#skF_1'(A_169,B_170),k1_relat_1('#skF_2'))
      | ~ r1_tarski(A_169,'#skF_5')
      | r1_tarski(A_169,B_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_38,c_36,c_1294])).

tff(c_2003,plain,(
    ! [A_171] :
      ( ~ r1_tarski(A_171,'#skF_5')
      | r1_tarski(A_171,k1_relat_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1994,c_4])).

tff(c_44,plain,
    ( r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_568,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_2045,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_2003,c_568])).

tff(c_2082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2045])).

tff(c_2083,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2092,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2083])).

tff(c_37409,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_37361,c_2092])).

tff(c_37440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12,c_37409])).

tff(c_37442,plain,(
    r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2083])).

tff(c_2084,plain,(
    r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_37451,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_40])).

tff(c_37452,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_37451])).

tff(c_37461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_37442,c_37452])).

tff(c_37462,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_37451])).

tff(c_37441,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2083])).

tff(c_42,plain,
    ( r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3'))
    | ~ r1_tarski(k9_relat_1('#skF_2','#skF_5'),k1_relat_1('#skF_3'))
    | ~ r1_tarski('#skF_5',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_37473,plain,(
    r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2084,c_37442,c_42])).

tff(c_37835,plain,(
    ! [A_969,C_970,B_971] :
      ( r1_tarski(A_969,k10_relat_1(C_970,B_971))
      | ~ r1_tarski(k9_relat_1(C_970,A_969),B_971)
      | ~ r1_tarski(A_969,k1_relat_1(C_970))
      | ~ v1_funct_1(C_970)
      | ~ v1_relat_1(C_970) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_37847,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_37473,c_37835])).

tff(c_37883,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_37441,c_37847])).

tff(c_37901,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_37883])).

tff(c_37905,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_37901])).

tff(c_37907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37462,c_37905])).

tff(c_37909,plain,(
    ~ r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_46,plain,
    ( ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_38011,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_37909,c_46])).

tff(c_37908,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,
    ( r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3'))
    | r1_tarski('#skF_5',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_37914,plain,(
    r1_tarski(k9_relat_1('#skF_2','#skF_4'),k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_37909,c_48])).

tff(c_39154,plain,(
    ! [A_1054,C_1055,B_1056] :
      ( r1_tarski(A_1054,k10_relat_1(C_1055,B_1056))
      | ~ r1_tarski(k9_relat_1(C_1055,A_1054),B_1056)
      | ~ r1_tarski(A_1054,k1_relat_1(C_1055))
      | ~ v1_funct_1(C_1055)
      | ~ v1_relat_1(C_1055) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_39187,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_37914,c_39154])).

tff(c_39216,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_2',k1_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_37908,c_39187])).

tff(c_39226,plain,
    ( r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_39216])).

tff(c_39230,plain,(
    r1_tarski('#skF_4',k1_relat_1(k5_relat_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_39226])).

tff(c_39232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38011,c_39230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:17:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.65/8.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.77/8.12  
% 15.77/8.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.77/8.12  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_relat_1 > k2_xboole_0 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 15.77/8.12  
% 15.77/8.12  %Foreground sorts:
% 15.77/8.12  
% 15.77/8.12  
% 15.77/8.12  %Background operators:
% 15.77/8.12  
% 15.77/8.12  
% 15.77/8.12  %Foreground operators:
% 15.77/8.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.77/8.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.77/8.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.77/8.12  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 15.77/8.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.77/8.12  tff('#skF_5', type, '#skF_5': $i).
% 15.77/8.12  tff('#skF_2', type, '#skF_2': $i).
% 15.77/8.12  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 15.77/8.12  tff('#skF_3', type, '#skF_3': $i).
% 15.77/8.12  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 15.77/8.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.77/8.12  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 15.77/8.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.77/8.12  tff('#skF_4', type, '#skF_4': $i).
% 15.77/8.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.77/8.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.77/8.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.77/8.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.77/8.12  
% 15.77/8.14  tff(f_112, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: (r1_tarski(C, k1_relat_1(k5_relat_1(A, B))) <=> (r1_tarski(C, k1_relat_1(A)) & r1_tarski(k9_relat_1(A, C), k1_relat_1(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_funct_1)).
% 15.77/8.14  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.77/8.14  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 15.77/8.14  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 15.77/8.14  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_1)).
% 15.77/8.14  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 15.77/8.14  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 15.77/8.14  tff(f_80, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 15.77/8.14  tff(f_42, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 15.77/8.14  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_relat_1)).
% 15.77/8.14  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.77/8.14  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.77/8.14  tff(c_53, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.77/8.14  tff(c_57, plain, (![B_7]: (k2_xboole_0(B_7, B_7)=B_7)), inference(resolution, [status(thm)], [c_12, c_53])).
% 15.77/8.14  tff(c_36, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.77/8.14  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.77/8.14  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.77/8.14  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.77/8.14  tff(c_2596, plain, (![A_199, C_200, B_201]: (r2_hidden(A_199, k1_relat_1(C_200)) | ~r2_hidden(A_199, k1_relat_1(k5_relat_1(C_200, B_201))) | ~v1_funct_1(C_200) | ~v1_relat_1(C_200) | ~v1_funct_1(B_201) | ~v1_relat_1(B_201))), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.77/8.14  tff(c_7594, plain, (![C_398, B_399, B_400]: (r2_hidden('#skF_1'(k1_relat_1(k5_relat_1(C_398, B_399)), B_400), k1_relat_1(C_398)) | ~v1_funct_1(C_398) | ~v1_relat_1(C_398) | ~v1_funct_1(B_399) | ~v1_relat_1(B_399) | r1_tarski(k1_relat_1(k5_relat_1(C_398, B_399)), B_400))), inference(resolution, [status(thm)], [c_6, c_2596])).
% 15.77/8.14  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.77/8.14  tff(c_7607, plain, (![C_398, B_399]: (~v1_funct_1(C_398) | ~v1_relat_1(C_398) | ~v1_funct_1(B_399) | ~v1_relat_1(B_399) | r1_tarski(k1_relat_1(k5_relat_1(C_398, B_399)), k1_relat_1(C_398)))), inference(resolution, [status(thm)], [c_7594, c_4])).
% 15.77/8.14  tff(c_404, plain, (![A_77, B_78]: (k10_relat_1(A_77, k1_relat_1(B_78))=k1_relat_1(k5_relat_1(A_77, B_78)) | ~v1_relat_1(B_78) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.77/8.14  tff(c_22, plain, (![B_22, A_21]: (r1_tarski(k9_relat_1(B_22, k10_relat_1(B_22, A_21)), A_21) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.77/8.14  tff(c_4390, plain, (![A_288, B_289]: (r1_tarski(k9_relat_1(A_288, k1_relat_1(k5_relat_1(A_288, B_289))), k1_relat_1(B_289)) | ~v1_funct_1(A_288) | ~v1_relat_1(A_288) | ~v1_relat_1(B_289) | ~v1_relat_1(A_288))), inference(superposition, [status(thm), theory('equality')], [c_404, c_22])).
% 15.77/8.14  tff(c_24, plain, (![A_23, C_25, B_24]: (r1_tarski(A_23, k10_relat_1(C_25, B_24)) | ~r1_tarski(k9_relat_1(C_25, A_23), B_24) | ~r1_tarski(A_23, k1_relat_1(C_25)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_80])).
% 15.77/8.14  tff(c_12297, plain, (![A_517, B_518]: (r1_tarski(k1_relat_1(k5_relat_1(A_517, B_518)), k10_relat_1(A_517, k1_relat_1(B_518))) | ~r1_tarski(k1_relat_1(k5_relat_1(A_517, B_518)), k1_relat_1(A_517)) | ~v1_funct_1(A_517) | ~v1_relat_1(B_518) | ~v1_relat_1(A_517))), inference(resolution, [status(thm)], [c_4390, c_24])).
% 15.77/8.14  tff(c_50, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2')) | r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.77/8.14  tff(c_90, plain, (r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_50])).
% 15.77/8.14  tff(c_16, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.77/8.14  tff(c_94, plain, (k2_xboole_0('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))=k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_90, c_16])).
% 15.77/8.14  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(k2_xboole_0(A_8, B_9), C_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.77/8.14  tff(c_249, plain, (![C_10]: (r1_tarski('#skF_5', C_10) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_2', '#skF_3')), C_10))), inference(superposition, [status(thm), theory('equality')], [c_94, c_14])).
% 15.77/8.14  tff(c_12337, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_2', k1_relat_1('#skF_3'))) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_2', '#skF_3')), k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12297, c_249])).
% 15.77/8.14  tff(c_12375, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_2', k1_relat_1('#skF_3'))) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_2', '#skF_3')), k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_36, c_12337])).
% 15.77/8.14  tff(c_12379, plain, (~r1_tarski(k1_relat_1(k5_relat_1('#skF_2', '#skF_3')), k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_12375])).
% 15.77/8.14  tff(c_12382, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7607, c_12379])).
% 15.77/8.14  tff(c_12389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_38, c_36, c_12382])).
% 15.77/8.14  tff(c_12391, plain, (r1_tarski(k1_relat_1(k5_relat_1('#skF_2', '#skF_3')), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_12375])).
% 15.77/8.14  tff(c_20, plain, (![A_18, B_20]: (k10_relat_1(A_18, k1_relat_1(B_20))=k1_relat_1(k5_relat_1(A_18, B_20)) | ~v1_relat_1(B_20) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_64])).
% 15.77/8.14  tff(c_12390, plain, (r1_tarski('#skF_5', k10_relat_1('#skF_2', k1_relat_1('#skF_3')))), inference(splitRight, [status(thm)], [c_12375])).
% 15.77/8.14  tff(c_12428, plain, (k2_xboole_0('#skF_5', k10_relat_1('#skF_2', k1_relat_1('#skF_3')))=k10_relat_1('#skF_2', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_12390, c_16])).
% 15.77/8.14  tff(c_13225, plain, (k2_xboole_0('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))=k10_relat_1('#skF_2', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_20, c_12428])).
% 15.77/8.14  tff(c_13247, plain, (k10_relat_1('#skF_2', k1_relat_1('#skF_3'))=k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_94, c_13225])).
% 15.77/8.14  tff(c_326, plain, (![B_67, A_68]: (r1_tarski(k9_relat_1(B_67, k10_relat_1(B_67, A_68)), A_68) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.77/8.14  tff(c_416, plain, (![B_79, A_80]: (k2_xboole_0(k9_relat_1(B_79, k10_relat_1(B_79, A_80)), A_80)=A_80 | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_326, c_16])).
% 15.77/8.14  tff(c_67, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, C_39) | ~r1_tarski(k2_xboole_0(A_38, B_40), C_39))), inference(cnfTransformation, [status(thm)], [f_42])).
% 15.77/8.14  tff(c_76, plain, (![A_41, B_42]: (r1_tarski(A_41, k2_xboole_0(A_41, B_42)))), inference(resolution, [status(thm)], [c_12, c_67])).
% 15.77/8.14  tff(c_87, plain, (![A_8, B_9, B_42]: (r1_tarski(A_8, k2_xboole_0(k2_xboole_0(A_8, B_9), B_42)))), inference(resolution, [status(thm)], [c_76, c_14])).
% 15.77/8.14  tff(c_434, plain, (![B_79, A_80, B_42]: (r1_tarski(k9_relat_1(B_79, k10_relat_1(B_79, A_80)), k2_xboole_0(A_80, B_42)) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(superposition, [status(thm), theory('equality')], [c_416, c_87])).
% 15.77/8.14  tff(c_13485, plain, (![B_42]: (r1_tarski(k9_relat_1('#skF_2', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))), k2_xboole_0(k1_relat_1('#skF_3'), B_42)) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_13247, c_434])).
% 15.77/8.14  tff(c_14378, plain, (![B_544]: (r1_tarski(k9_relat_1('#skF_2', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))), k2_xboole_0(k1_relat_1('#skF_3'), B_544)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_13485])).
% 15.77/8.14  tff(c_14401, plain, (![B_544]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_2', '#skF_3')), k10_relat_1('#skF_2', k2_xboole_0(k1_relat_1('#skF_3'), B_544))) | ~r1_tarski(k1_relat_1(k5_relat_1('#skF_2', '#skF_3')), k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_14378, c_24])).
% 15.77/8.14  tff(c_14620, plain, (![B_547]: (r1_tarski(k1_relat_1(k5_relat_1('#skF_2', '#skF_3')), k10_relat_1('#skF_2', k2_xboole_0(k1_relat_1('#skF_3'), B_547))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_12391, c_14401])).
% 15.77/8.14  tff(c_14714, plain, (![B_547]: (r1_tarski('#skF_5', k10_relat_1('#skF_2', k2_xboole_0(k1_relat_1('#skF_3'), B_547))))), inference(resolution, [status(thm)], [c_14620, c_249])).
% 15.77/8.14  tff(c_2427, plain, (![C_186, A_187, D_188, B_189]: (r1_tarski(k9_relat_1(C_186, A_187), k9_relat_1(D_188, B_189)) | ~r1_tarski(A_187, B_189) | ~r1_tarski(C_186, D_188) | ~v1_relat_1(D_188) | ~v1_relat_1(C_186))), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.77/8.14  tff(c_5089, plain, (![C_316, A_317, D_318, B_319]: (k2_xboole_0(k9_relat_1(C_316, A_317), k9_relat_1(D_318, B_319))=k9_relat_1(D_318, B_319) | ~r1_tarski(A_317, B_319) | ~r1_tarski(C_316, D_318) | ~v1_relat_1(D_318) | ~v1_relat_1(C_316))), inference(resolution, [status(thm)], [c_2427, c_16])).
% 15.77/8.14  tff(c_11527, plain, (![C_500, B_501, D_502, C_504, A_503]: (r1_tarski(k9_relat_1(C_500, A_503), C_504) | ~r1_tarski(k9_relat_1(D_502, B_501), C_504) | ~r1_tarski(A_503, B_501) | ~r1_tarski(C_500, D_502) | ~v1_relat_1(D_502) | ~v1_relat_1(C_500))), inference(superposition, [status(thm), theory('equality')], [c_5089, c_14])).
% 15.77/8.14  tff(c_37141, plain, (![C_948, A_949, A_950, B_951]: (r1_tarski(k9_relat_1(C_948, A_949), A_950) | ~r1_tarski(A_949, k10_relat_1(B_951, A_950)) | ~r1_tarski(C_948, B_951) | ~v1_relat_1(C_948) | ~v1_funct_1(B_951) | ~v1_relat_1(B_951))), inference(resolution, [status(thm)], [c_22, c_11527])).
% 15.77/8.14  tff(c_37174, plain, (![C_948, B_547]: (r1_tarski(k9_relat_1(C_948, '#skF_5'), k2_xboole_0(k1_relat_1('#skF_3'), B_547)) | ~r1_tarski(C_948, '#skF_2') | ~v1_relat_1(C_948) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_14714, c_37141])).
% 15.77/8.14  tff(c_37250, plain, (![C_952, B_953]: (r1_tarski(k9_relat_1(C_952, '#skF_5'), k2_xboole_0(k1_relat_1('#skF_3'), B_953)) | ~r1_tarski(C_952, '#skF_2') | ~v1_relat_1(C_952))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_37174])).
% 15.77/8.14  tff(c_37361, plain, (![C_954]: (r1_tarski(k9_relat_1(C_954, '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski(C_954, '#skF_2') | ~v1_relat_1(C_954))), inference(superposition, [status(thm), theory('equality')], [c_57, c_37250])).
% 15.77/8.14  tff(c_138, plain, (![C_52, B_53, A_54]: (r2_hidden(C_52, B_53) | ~r2_hidden(C_52, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.77/8.14  tff(c_334, plain, (![A_69, B_70, B_71]: (r2_hidden('#skF_1'(A_69, B_70), B_71) | ~r1_tarski(A_69, B_71) | r1_tarski(A_69, B_70))), inference(resolution, [status(thm)], [c_6, c_138])).
% 15.77/8.14  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.77/8.14  tff(c_1043, plain, (![A_121, B_122, B_123, B_124]: (r2_hidden('#skF_1'(A_121, B_122), B_123) | ~r1_tarski(B_124, B_123) | ~r1_tarski(A_121, B_124) | r1_tarski(A_121, B_122))), inference(resolution, [status(thm)], [c_334, c_2])).
% 15.77/8.14  tff(c_1291, plain, (![A_140, B_141]: (r2_hidden('#skF_1'(A_140, B_141), k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~r1_tarski(A_140, '#skF_5') | r1_tarski(A_140, B_141))), inference(resolution, [status(thm)], [c_90, c_1043])).
% 15.77/8.14  tff(c_30, plain, (![A_26, C_29, B_27]: (r2_hidden(A_26, k1_relat_1(C_29)) | ~r2_hidden(A_26, k1_relat_1(k5_relat_1(C_29, B_27))) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.77/8.14  tff(c_1294, plain, (![A_140, B_141]: (r2_hidden('#skF_1'(A_140, B_141), k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_140, '#skF_5') | r1_tarski(A_140, B_141))), inference(resolution, [status(thm)], [c_1291, c_30])).
% 15.77/8.14  tff(c_1994, plain, (![A_169, B_170]: (r2_hidden('#skF_1'(A_169, B_170), k1_relat_1('#skF_2')) | ~r1_tarski(A_169, '#skF_5') | r1_tarski(A_169, B_170))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_38, c_36, c_1294])).
% 15.77/8.14  tff(c_2003, plain, (![A_171]: (~r1_tarski(A_171, '#skF_5') | r1_tarski(A_171, k1_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_1994, c_4])).
% 15.77/8.14  tff(c_44, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2')) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.77/8.14  tff(c_568, plain, (~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_44])).
% 15.77/8.14  tff(c_2045, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_2003, c_568])).
% 15.77/8.14  tff(c_2082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2045])).
% 15.77/8.14  tff(c_2083, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_44])).
% 15.77/8.14  tff(c_2092, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2083])).
% 15.77/8.14  tff(c_37409, plain, (~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_37361, c_2092])).
% 15.77/8.14  tff(c_37440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_12, c_37409])).
% 15.77/8.14  tff(c_37442, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2083])).
% 15.77/8.14  tff(c_2084, plain, (r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_44])).
% 15.77/8.14  tff(c_40, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.77/8.14  tff(c_37451, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_40])).
% 15.77/8.14  tff(c_37452, plain, (~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_37451])).
% 15.77/8.14  tff(c_37461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_37442, c_37452])).
% 15.77/8.14  tff(c_37462, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_37451])).
% 15.77/8.14  tff(c_37441, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_2083])).
% 15.77/8.14  tff(c_42, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3')) | ~r1_tarski(k9_relat_1('#skF_2', '#skF_5'), k1_relat_1('#skF_3')) | ~r1_tarski('#skF_5', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.77/8.14  tff(c_37473, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2084, c_37442, c_42])).
% 15.77/8.14  tff(c_37835, plain, (![A_969, C_970, B_971]: (r1_tarski(A_969, k10_relat_1(C_970, B_971)) | ~r1_tarski(k9_relat_1(C_970, A_969), B_971) | ~r1_tarski(A_969, k1_relat_1(C_970)) | ~v1_funct_1(C_970) | ~v1_relat_1(C_970))), inference(cnfTransformation, [status(thm)], [f_80])).
% 15.77/8.14  tff(c_37847, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3'))) | ~r1_tarski('#skF_4', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_37473, c_37835])).
% 15.77/8.14  tff(c_37883, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_37441, c_37847])).
% 15.77/8.14  tff(c_37901, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_20, c_37883])).
% 15.77/8.14  tff(c_37905, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_37901])).
% 15.77/8.14  tff(c_37907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37462, c_37905])).
% 15.77/8.14  tff(c_37909, plain, (~r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_50])).
% 15.77/8.14  tff(c_46, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.77/8.14  tff(c_38011, plain, (~r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_37909, c_46])).
% 15.77/8.14  tff(c_37908, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_50])).
% 15.77/8.14  tff(c_48, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3')) | r1_tarski('#skF_5', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 15.77/8.14  tff(c_37914, plain, (r1_tarski(k9_relat_1('#skF_2', '#skF_4'), k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_37909, c_48])).
% 15.77/8.14  tff(c_39154, plain, (![A_1054, C_1055, B_1056]: (r1_tarski(A_1054, k10_relat_1(C_1055, B_1056)) | ~r1_tarski(k9_relat_1(C_1055, A_1054), B_1056) | ~r1_tarski(A_1054, k1_relat_1(C_1055)) | ~v1_funct_1(C_1055) | ~v1_relat_1(C_1055))), inference(cnfTransformation, [status(thm)], [f_80])).
% 15.77/8.14  tff(c_39187, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3'))) | ~r1_tarski('#skF_4', k1_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_37914, c_39154])).
% 15.77/8.14  tff(c_39216, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_2', k1_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_37908, c_39187])).
% 15.77/8.14  tff(c_39226, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_20, c_39216])).
% 15.77/8.14  tff(c_39230, plain, (r1_tarski('#skF_4', k1_relat_1(k5_relat_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_39226])).
% 15.77/8.14  tff(c_39232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38011, c_39230])).
% 15.77/8.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.77/8.14  
% 15.77/8.14  Inference rules
% 15.77/8.14  ----------------------
% 15.77/8.14  #Ref     : 0
% 15.77/8.14  #Sup     : 10174
% 15.77/8.14  #Fact    : 0
% 15.77/8.14  #Define  : 0
% 15.77/8.14  #Split   : 16
% 15.77/8.14  #Chain   : 0
% 15.77/8.14  #Close   : 0
% 15.77/8.14  
% 15.77/8.14  Ordering : KBO
% 15.77/8.14  
% 15.77/8.14  Simplification rules
% 15.77/8.14  ----------------------
% 15.77/8.14  #Subsume      : 2764
% 15.77/8.14  #Demod        : 2560
% 15.77/8.14  #Tautology    : 1690
% 15.77/8.14  #SimpNegUnit  : 7
% 15.77/8.14  #BackRed      : 4
% 15.77/8.14  
% 15.77/8.14  #Partial instantiations: 0
% 15.77/8.14  #Strategies tried      : 1
% 15.77/8.14  
% 15.77/8.14  Timing (in seconds)
% 15.77/8.14  ----------------------
% 15.77/8.14  Preprocessing        : 0.33
% 15.77/8.14  Parsing              : 0.17
% 15.77/8.14  CNF conversion       : 0.02
% 15.77/8.14  Main loop            : 7.03
% 15.77/8.14  Inferencing          : 1.03
% 15.77/8.14  Reduction            : 2.16
% 15.77/8.14  Demodulation         : 1.75
% 15.77/8.14  BG Simplification    : 0.14
% 15.77/8.14  Subsumption          : 3.24
% 15.77/8.14  Abstraction          : 0.20
% 15.77/8.14  MUC search           : 0.00
% 15.77/8.14  Cooper               : 0.00
% 15.77/8.14  Total                : 7.40
% 15.77/8.14  Index Insertion      : 0.00
% 15.77/8.14  Index Deletion       : 0.00
% 15.77/8.14  Index Matching       : 0.00
% 15.77/8.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
