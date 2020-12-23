%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:09 EST 2020

% Result     : Theorem 16.70s
% Output     : CNFRefutation 16.83s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 598 expanded)
%              Number of leaves         :   29 ( 220 expanded)
%              Depth                    :   18
%              Number of atoms          :  238 (1511 expanded)
%              Number of equality atoms :   37 ( 378 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > #nlpp > k1_xboole_0 > #skF_9 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_3 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_36,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(c_48,plain,
    ( k5_relat_1('#skF_11',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_73,plain,(
    k5_relat_1(k1_xboole_0,'#skF_11') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_50,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_51,plain,(
    ! [A_113] :
      ( v1_relat_1(A_113)
      | ~ v1_xboole_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_55,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_51])).

tff(c_44,plain,(
    ! [A_108,B_109] :
      ( v1_relat_1(k5_relat_1(A_108,B_109))
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_46,plain,(
    ! [A_110] :
      ( k1_xboole_0 = A_110
      | r2_hidden(k4_tarski('#skF_9'(A_110),'#skF_10'(A_110)),A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    ! [D_100,E_101,B_61,A_9] :
      ( r2_hidden(k4_tarski(D_100,'#skF_3'(E_101,B_61,D_100,A_9,k5_relat_1(A_9,B_61))),A_9)
      | ~ r2_hidden(k4_tarski(D_100,E_101),k5_relat_1(A_9,B_61))
      | ~ v1_relat_1(k5_relat_1(A_9,B_61))
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_192,plain,(
    ! [A_143,B_144,C_145] :
      ( ~ r2_hidden('#skF_1'(A_143,B_144,C_145),B_144)
      | r2_hidden('#skF_2'(A_143,B_144,C_145),C_145)
      | k4_xboole_0(A_143,B_144) = C_145 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_199,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k4_xboole_0(A_1,A_1) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_192])).

tff(c_201,plain,(
    ! [A_146,C_147] :
      ( r2_hidden('#skF_2'(A_146,A_146,C_147),C_147)
      | k4_xboole_0(A_146,A_146) = C_147 ) ),
    inference(resolution,[status(thm)],[c_18,c_192])).

tff(c_22,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    ! [D_117,B_118,A_119] :
      ( ~ r2_hidden(D_117,B_118)
      | ~ r2_hidden(D_117,k4_xboole_0(A_119,B_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [D_117,A_7] :
      ( ~ r2_hidden(D_117,A_7)
      | ~ r2_hidden(D_117,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_64])).

tff(c_225,plain,(
    ! [A_148,C_149] :
      ( ~ r2_hidden('#skF_2'(A_148,A_148,C_149),k1_xboole_0)
      | k4_xboole_0(A_148,A_148) = C_149 ) ),
    inference(resolution,[status(thm)],[c_201,c_67])).

tff(c_236,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_199,c_225])).

tff(c_925,plain,(
    ! [E_206,B_207,D_208,A_209] :
      ( r2_hidden(k4_tarski('#skF_3'(E_206,B_207,D_208,A_209,k5_relat_1(A_209,B_207)),E_206),B_207)
      | ~ r2_hidden(k4_tarski(D_208,E_206),k5_relat_1(A_209,B_207))
      | ~ v1_relat_1(k5_relat_1(A_209,B_207))
      | ~ v1_relat_1(B_207)
      | ~ v1_relat_1(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_949,plain,(
    ! [E_206,A_209,B_2,A_1,D_208] :
      ( r2_hidden(k4_tarski('#skF_3'(E_206,k4_xboole_0(A_1,B_2),D_208,A_209,k5_relat_1(A_209,k4_xboole_0(A_1,B_2))),E_206),A_1)
      | ~ r2_hidden(k4_tarski(D_208,E_206),k5_relat_1(A_209,k4_xboole_0(A_1,B_2)))
      | ~ v1_relat_1(k5_relat_1(A_209,k4_xboole_0(A_1,B_2)))
      | ~ v1_relat_1(k4_xboole_0(A_1,B_2))
      | ~ v1_relat_1(A_209) ) ),
    inference(resolution,[status(thm)],[c_925,c_6])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24111,plain,(
    ! [A_634,E_631,A_633,D_630,B_632] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(E_631,k4_xboole_0(A_633,B_632),D_630,A_634,k5_relat_1(A_634,k4_xboole_0(A_633,B_632))),E_631),B_632)
      | ~ r2_hidden(k4_tarski(D_630,E_631),k5_relat_1(A_634,k4_xboole_0(A_633,B_632)))
      | ~ v1_relat_1(k5_relat_1(A_634,k4_xboole_0(A_633,B_632)))
      | ~ v1_relat_1(k4_xboole_0(A_633,B_632))
      | ~ v1_relat_1(A_634) ) ),
    inference(resolution,[status(thm)],[c_925,c_4])).

tff(c_24115,plain,(
    ! [D_208,E_206,A_209,A_1] :
      ( ~ r2_hidden(k4_tarski(D_208,E_206),k5_relat_1(A_209,k4_xboole_0(A_1,A_1)))
      | ~ v1_relat_1(k5_relat_1(A_209,k4_xboole_0(A_1,A_1)))
      | ~ v1_relat_1(k4_xboole_0(A_1,A_1))
      | ~ v1_relat_1(A_209) ) ),
    inference(resolution,[status(thm)],[c_949,c_24111])).

tff(c_24317,plain,(
    ! [D_635,E_636,A_637] :
      ( ~ r2_hidden(k4_tarski(D_635,E_636),k5_relat_1(A_637,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_637,k1_xboole_0))
      | ~ v1_relat_1(A_637) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_236,c_236,c_236,c_24115])).

tff(c_24376,plain,(
    ! [A_638] :
      ( ~ v1_relat_1(A_638)
      | k5_relat_1(A_638,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_638,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_46,c_24317])).

tff(c_24380,plain,(
    ! [A_108] :
      ( k5_relat_1(A_108,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_108) ) ),
    inference(resolution,[status(thm)],[c_44,c_24376])).

tff(c_24384,plain,(
    ! [A_639] :
      ( k5_relat_1(A_639,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_639) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_24380])).

tff(c_24396,plain,(
    k5_relat_1('#skF_11',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_24384])).

tff(c_24258,plain,(
    ! [D_208,E_206,A_209] :
      ( ~ r2_hidden(k4_tarski(D_208,E_206),k5_relat_1(A_209,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_209,k1_xboole_0))
      | ~ v1_relat_1(A_209) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_236,c_236,c_236,c_24115])).

tff(c_24400,plain,(
    ! [D_208,E_206] :
      ( ~ r2_hidden(k4_tarski(D_208,E_206),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1('#skF_11',k1_xboole_0))
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24396,c_24258])).

tff(c_24457,plain,(
    ! [D_640,E_641] : ~ r2_hidden(k4_tarski(D_640,E_641),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_55,c_24396,c_24400])).

tff(c_24489,plain,(
    ! [D_100,E_101,B_61] :
      ( ~ r2_hidden(k4_tarski(D_100,E_101),k5_relat_1(k1_xboole_0,B_61))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_61))
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_42,c_24457])).

tff(c_24574,plain,(
    ! [D_644,E_645,B_646] :
      ( ~ r2_hidden(k4_tarski(D_644,E_645),k5_relat_1(k1_xboole_0,B_646))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_646))
      | ~ v1_relat_1(B_646) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_24489])).

tff(c_24954,plain,(
    ! [B_652] :
      ( ~ v1_relat_1(B_652)
      | k5_relat_1(k1_xboole_0,B_652) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_652)) ) ),
    inference(resolution,[status(thm)],[c_46,c_24574])).

tff(c_24961,plain,(
    ! [B_109] :
      ( k5_relat_1(k1_xboole_0,B_109) = k1_xboole_0
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_44,c_24954])).

tff(c_24967,plain,(
    ! [B_653] :
      ( k5_relat_1(k1_xboole_0,B_653) = k1_xboole_0
      | ~ v1_relat_1(B_653) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_24961])).

tff(c_24976,plain,(
    k5_relat_1(k1_xboole_0,'#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_24967])).

tff(c_24983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_24976])).

tff(c_24984,plain,(
    k5_relat_1('#skF_11',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_24985,plain,(
    k5_relat_1(k1_xboole_0,'#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_25584,plain,(
    ! [E_719,B_720,D_721,A_722] :
      ( r2_hidden(k4_tarski('#skF_3'(E_719,B_720,D_721,A_722,k5_relat_1(A_722,B_720)),E_719),B_720)
      | ~ r2_hidden(k4_tarski(D_721,E_719),k5_relat_1(A_722,B_720))
      | ~ v1_relat_1(k5_relat_1(A_722,B_720))
      | ~ v1_relat_1(B_720)
      | ~ v1_relat_1(A_722) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_25602,plain,(
    ! [E_719,D_721] :
      ( r2_hidden(k4_tarski('#skF_3'(E_719,'#skF_11',D_721,k1_xboole_0,k1_xboole_0),E_719),'#skF_11')
      | ~ r2_hidden(k4_tarski(D_721,E_719),k5_relat_1(k1_xboole_0,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24985,c_25584])).

tff(c_25611,plain,(
    ! [E_719,D_721] :
      ( r2_hidden(k4_tarski('#skF_3'(E_719,'#skF_11',D_721,k1_xboole_0,k1_xboole_0),E_719),'#skF_11')
      | ~ r2_hidden(k4_tarski(D_721,E_719),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_50,c_55,c_24985,c_24985,c_25602])).

tff(c_25640,plain,(
    ! [D_730,E_731,B_732,A_733] :
      ( r2_hidden(k4_tarski(D_730,'#skF_3'(E_731,B_732,D_730,A_733,k5_relat_1(A_733,B_732))),A_733)
      | ~ r2_hidden(k4_tarski(D_730,E_731),k5_relat_1(A_733,B_732))
      | ~ v1_relat_1(k5_relat_1(A_733,B_732))
      | ~ v1_relat_1(B_732)
      | ~ v1_relat_1(A_733) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_25658,plain,(
    ! [D_730,E_731] :
      ( r2_hidden(k4_tarski(D_730,'#skF_3'(E_731,'#skF_11',D_730,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_730,E_731),k5_relat_1(k1_xboole_0,'#skF_11'))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24985,c_25640])).

tff(c_25668,plain,(
    ! [D_734,E_735] :
      ( r2_hidden(k4_tarski(D_734,'#skF_3'(E_735,'#skF_11',D_734,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_734,E_735),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_50,c_55,c_24985,c_24985,c_25658])).

tff(c_25052,plain,(
    ! [A_668,B_669,C_670] :
      ( r2_hidden('#skF_1'(A_668,B_669,C_670),A_668)
      | r2_hidden('#skF_2'(A_668,B_669,C_670),C_670)
      | k4_xboole_0(A_668,B_669) = C_670 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_25084,plain,(
    ! [A_668,C_670] :
      ( r2_hidden('#skF_2'(A_668,A_668,C_670),C_670)
      | k4_xboole_0(A_668,A_668) = C_670 ) ),
    inference(resolution,[status(thm)],[c_25052,c_16])).

tff(c_25094,plain,(
    ! [A_671,C_672] :
      ( r2_hidden('#skF_2'(A_671,A_671,C_672),C_672)
      | k4_xboole_0(A_671,A_671) = C_672 ) ),
    inference(resolution,[status(thm)],[c_25052,c_16])).

tff(c_25140,plain,(
    ! [A_678,C_679] :
      ( ~ r2_hidden('#skF_2'(A_678,A_678,C_679),k1_xboole_0)
      | k4_xboole_0(A_678,A_678) = C_679 ) ),
    inference(resolution,[status(thm)],[c_25094,c_67])).

tff(c_25156,plain,(
    ! [A_680] : k4_xboole_0(A_680,A_680) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25084,c_25140])).

tff(c_25164,plain,(
    ! [D_6,A_680] :
      ( r2_hidden(D_6,A_680)
      | ~ r2_hidden(D_6,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25156,c_6])).

tff(c_25685,plain,(
    ! [D_738,E_739,A_740] :
      ( r2_hidden(k4_tarski(D_738,'#skF_3'(E_739,'#skF_11',D_738,k1_xboole_0,k1_xboole_0)),A_740)
      | ~ r2_hidden(k4_tarski(D_738,E_739),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_25668,c_25164])).

tff(c_38,plain,(
    ! [D_100,F_104,B_61,E_101,A_9] :
      ( r2_hidden(k4_tarski(D_100,E_101),k5_relat_1(A_9,B_61))
      | ~ r2_hidden(k4_tarski(F_104,E_101),B_61)
      | ~ r2_hidden(k4_tarski(D_100,F_104),A_9)
      | ~ v1_relat_1(k5_relat_1(A_9,B_61))
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26931,plain,(
    ! [E_813,D_814,A_816,D_812,A_815] :
      ( r2_hidden(k4_tarski(D_814,'#skF_3'(E_813,'#skF_11',D_812,k1_xboole_0,k1_xboole_0)),k5_relat_1(A_815,A_816))
      | ~ r2_hidden(k4_tarski(D_814,D_812),A_815)
      | ~ v1_relat_1(k5_relat_1(A_815,A_816))
      | ~ v1_relat_1(A_816)
      | ~ v1_relat_1(A_815)
      | ~ r2_hidden(k4_tarski(D_812,E_813),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_25685,c_38])).

tff(c_26943,plain,(
    ! [D_814,E_813,D_812] :
      ( r2_hidden(k4_tarski(D_814,'#skF_3'(E_813,'#skF_11',D_812,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_814,D_812),k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,'#skF_11'))
      | ~ v1_relat_1('#skF_11')
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_812,E_813),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24985,c_26931])).

tff(c_27741,plain,(
    ! [D_842,E_843,D_844] :
      ( r2_hidden(k4_tarski(D_842,'#skF_3'(E_843,'#skF_11',D_844,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_842,D_844),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_844,E_843),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_50,c_55,c_24985,c_26943])).

tff(c_27756,plain,(
    ! [D_100,D_842,E_843,D_844,A_9] :
      ( r2_hidden(k4_tarski(D_100,'#skF_3'(E_843,'#skF_11',D_844,k1_xboole_0,k1_xboole_0)),k5_relat_1(A_9,k1_xboole_0))
      | ~ r2_hidden(k4_tarski(D_100,D_842),A_9)
      | ~ v1_relat_1(k5_relat_1(A_9,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_9)
      | ~ r2_hidden(k4_tarski(D_842,D_844),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_844,E_843),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_27741,c_38])).

tff(c_42172,plain,(
    ! [D_1107,A_1109,D_1106,E_1110,D_1108] :
      ( r2_hidden(k4_tarski(D_1108,'#skF_3'(E_1110,'#skF_11',D_1106,k1_xboole_0,k1_xboole_0)),k5_relat_1(A_1109,k1_xboole_0))
      | ~ r2_hidden(k4_tarski(D_1108,D_1107),A_1109)
      | ~ v1_relat_1(k5_relat_1(A_1109,k1_xboole_0))
      | ~ v1_relat_1(A_1109)
      | ~ r2_hidden(k4_tarski(D_1107,D_1106),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_1106,E_1110),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_27756])).

tff(c_42198,plain,(
    ! [E_719,D_721,E_1110,D_1106] :
      ( r2_hidden(k4_tarski('#skF_3'(E_719,'#skF_11',D_721,k1_xboole_0,k1_xboole_0),'#skF_3'(E_1110,'#skF_11',D_1106,k1_xboole_0,k1_xboole_0)),k5_relat_1('#skF_11',k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1('#skF_11',k1_xboole_0))
      | ~ v1_relat_1('#skF_11')
      | ~ r2_hidden(k4_tarski(E_719,D_1106),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_1106,E_1110),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_721,E_719),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_25611,c_42172])).

tff(c_42222,plain,(
    ! [E_719,D_721,E_1110,D_1106] :
      ( r2_hidden(k4_tarski('#skF_3'(E_719,'#skF_11',D_721,k1_xboole_0,k1_xboole_0),'#skF_3'(E_1110,'#skF_11',D_1106,k1_xboole_0,k1_xboole_0)),k5_relat_1('#skF_11',k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1('#skF_11',k1_xboole_0))
      | ~ r2_hidden(k4_tarski(E_719,D_1106),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_1106,E_1110),k1_xboole_0)
      | ~ r2_hidden(k4_tarski(D_721,E_719),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42198])).

tff(c_46094,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_11',k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_42222])).

tff(c_46097,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_44,c_46094])).

tff(c_46101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_55,c_46097])).

tff(c_46103,plain,(
    v1_relat_1(k5_relat_1('#skF_11',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_42222])).

tff(c_25153,plain,(
    ! [A_668] : k4_xboole_0(A_668,A_668) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25084,c_25140])).

tff(c_25607,plain,(
    ! [A_722,B_2,A_1,E_719,D_721] :
      ( r2_hidden(k4_tarski('#skF_3'(E_719,k4_xboole_0(A_1,B_2),D_721,A_722,k5_relat_1(A_722,k4_xboole_0(A_1,B_2))),E_719),A_1)
      | ~ r2_hidden(k4_tarski(D_721,E_719),k5_relat_1(A_722,k4_xboole_0(A_1,B_2)))
      | ~ v1_relat_1(k5_relat_1(A_722,k4_xboole_0(A_1,B_2)))
      | ~ v1_relat_1(k4_xboole_0(A_1,B_2))
      | ~ v1_relat_1(A_722) ) ),
    inference(resolution,[status(thm)],[c_25584,c_6])).

tff(c_46917,plain,(
    ! [D_1213,B_1211,E_1214,A_1212,A_1210] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(E_1214,k4_xboole_0(A_1212,B_1211),D_1213,A_1210,k5_relat_1(A_1210,k4_xboole_0(A_1212,B_1211))),E_1214),B_1211)
      | ~ r2_hidden(k4_tarski(D_1213,E_1214),k5_relat_1(A_1210,k4_xboole_0(A_1212,B_1211)))
      | ~ v1_relat_1(k5_relat_1(A_1210,k4_xboole_0(A_1212,B_1211)))
      | ~ v1_relat_1(k4_xboole_0(A_1212,B_1211))
      | ~ v1_relat_1(A_1210) ) ),
    inference(resolution,[status(thm)],[c_25584,c_4])).

tff(c_46921,plain,(
    ! [D_721,E_719,A_722,A_1] :
      ( ~ r2_hidden(k4_tarski(D_721,E_719),k5_relat_1(A_722,k4_xboole_0(A_1,A_1)))
      | ~ v1_relat_1(k5_relat_1(A_722,k4_xboole_0(A_1,A_1)))
      | ~ v1_relat_1(k4_xboole_0(A_1,A_1))
      | ~ v1_relat_1(A_722) ) ),
    inference(resolution,[status(thm)],[c_25607,c_46917])).

tff(c_47144,plain,(
    ! [D_1215,E_1216,A_1217] :
      ( ~ r2_hidden(k4_tarski(D_1215,E_1216),k5_relat_1(A_1217,k1_xboole_0))
      | ~ v1_relat_1(k5_relat_1(A_1217,k1_xboole_0))
      | ~ v1_relat_1(A_1217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_25153,c_25153,c_25153,c_46921])).

tff(c_47229,plain,(
    ! [A_1218] :
      ( ~ v1_relat_1(A_1218)
      | k5_relat_1(A_1218,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_1218,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_46,c_47144])).

tff(c_47232,plain,
    ( ~ v1_relat_1('#skF_11')
    | k5_relat_1('#skF_11',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46103,c_47229])).

tff(c_47239,plain,(
    k5_relat_1('#skF_11',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_47232])).

tff(c_47241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24984,c_47239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:06:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.70/7.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.70/7.21  
% 16.70/7.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.70/7.22  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > #nlpp > k1_xboole_0 > #skF_9 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_3 > #skF_8
% 16.70/7.22  
% 16.70/7.22  %Foreground sorts:
% 16.70/7.22  
% 16.70/7.22  
% 16.70/7.22  %Background operators:
% 16.70/7.22  
% 16.70/7.22  
% 16.70/7.22  %Foreground operators:
% 16.70/7.22  tff('#skF_9', type, '#skF_9': $i > $i).
% 16.70/7.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 16.70/7.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.70/7.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.70/7.22  tff('#skF_11', type, '#skF_11': $i).
% 16.70/7.22  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 16.70/7.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.70/7.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.70/7.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.70/7.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 16.70/7.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 16.70/7.22  tff('#skF_10', type, '#skF_10': $i > $i).
% 16.70/7.22  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 16.70/7.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.70/7.22  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 16.70/7.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 16.70/7.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.70/7.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.70/7.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.70/7.22  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 16.70/7.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.70/7.22  
% 16.83/7.24  tff(f_81, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 16.83/7.24  tff(f_36, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 16.83/7.24  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 16.83/7.24  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 16.83/7.24  tff(f_74, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 16.83/7.24  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 16.83/7.24  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 16.83/7.24  tff(f_38, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 16.83/7.24  tff(c_48, plain, (k5_relat_1('#skF_11', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.83/7.24  tff(c_73, plain, (k5_relat_1(k1_xboole_0, '#skF_11')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 16.83/7.24  tff(c_50, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.83/7.24  tff(c_20, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 16.83/7.24  tff(c_51, plain, (![A_113]: (v1_relat_1(A_113) | ~v1_xboole_0(A_113))), inference(cnfTransformation, [status(thm)], [f_42])).
% 16.83/7.24  tff(c_55, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_51])).
% 16.83/7.24  tff(c_44, plain, (![A_108, B_109]: (v1_relat_1(k5_relat_1(A_108, B_109)) | ~v1_relat_1(B_109) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_66])).
% 16.83/7.24  tff(c_46, plain, (![A_110]: (k1_xboole_0=A_110 | r2_hidden(k4_tarski('#skF_9'(A_110), '#skF_10'(A_110)), A_110) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_74])).
% 16.83/7.24  tff(c_42, plain, (![D_100, E_101, B_61, A_9]: (r2_hidden(k4_tarski(D_100, '#skF_3'(E_101, B_61, D_100, A_9, k5_relat_1(A_9, B_61))), A_9) | ~r2_hidden(k4_tarski(D_100, E_101), k5_relat_1(A_9, B_61)) | ~v1_relat_1(k5_relat_1(A_9, B_61)) | ~v1_relat_1(B_61) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.83/7.24  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.83/7.24  tff(c_192, plain, (![A_143, B_144, C_145]: (~r2_hidden('#skF_1'(A_143, B_144, C_145), B_144) | r2_hidden('#skF_2'(A_143, B_144, C_145), C_145) | k4_xboole_0(A_143, B_144)=C_145)), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.83/7.24  tff(c_199, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k4_xboole_0(A_1, A_1)=C_3)), inference(resolution, [status(thm)], [c_18, c_192])).
% 16.83/7.24  tff(c_201, plain, (![A_146, C_147]: (r2_hidden('#skF_2'(A_146, A_146, C_147), C_147) | k4_xboole_0(A_146, A_146)=C_147)), inference(resolution, [status(thm)], [c_18, c_192])).
% 16.83/7.24  tff(c_22, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.83/7.24  tff(c_64, plain, (![D_117, B_118, A_119]: (~r2_hidden(D_117, B_118) | ~r2_hidden(D_117, k4_xboole_0(A_119, B_118)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.83/7.24  tff(c_67, plain, (![D_117, A_7]: (~r2_hidden(D_117, A_7) | ~r2_hidden(D_117, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_64])).
% 16.83/7.24  tff(c_225, plain, (![A_148, C_149]: (~r2_hidden('#skF_2'(A_148, A_148, C_149), k1_xboole_0) | k4_xboole_0(A_148, A_148)=C_149)), inference(resolution, [status(thm)], [c_201, c_67])).
% 16.83/7.24  tff(c_236, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(resolution, [status(thm)], [c_199, c_225])).
% 16.83/7.24  tff(c_925, plain, (![E_206, B_207, D_208, A_209]: (r2_hidden(k4_tarski('#skF_3'(E_206, B_207, D_208, A_209, k5_relat_1(A_209, B_207)), E_206), B_207) | ~r2_hidden(k4_tarski(D_208, E_206), k5_relat_1(A_209, B_207)) | ~v1_relat_1(k5_relat_1(A_209, B_207)) | ~v1_relat_1(B_207) | ~v1_relat_1(A_209))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.83/7.24  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.83/7.24  tff(c_949, plain, (![E_206, A_209, B_2, A_1, D_208]: (r2_hidden(k4_tarski('#skF_3'(E_206, k4_xboole_0(A_1, B_2), D_208, A_209, k5_relat_1(A_209, k4_xboole_0(A_1, B_2))), E_206), A_1) | ~r2_hidden(k4_tarski(D_208, E_206), k5_relat_1(A_209, k4_xboole_0(A_1, B_2))) | ~v1_relat_1(k5_relat_1(A_209, k4_xboole_0(A_1, B_2))) | ~v1_relat_1(k4_xboole_0(A_1, B_2)) | ~v1_relat_1(A_209))), inference(resolution, [status(thm)], [c_925, c_6])).
% 16.83/7.24  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.83/7.24  tff(c_24111, plain, (![A_634, E_631, A_633, D_630, B_632]: (~r2_hidden(k4_tarski('#skF_3'(E_631, k4_xboole_0(A_633, B_632), D_630, A_634, k5_relat_1(A_634, k4_xboole_0(A_633, B_632))), E_631), B_632) | ~r2_hidden(k4_tarski(D_630, E_631), k5_relat_1(A_634, k4_xboole_0(A_633, B_632))) | ~v1_relat_1(k5_relat_1(A_634, k4_xboole_0(A_633, B_632))) | ~v1_relat_1(k4_xboole_0(A_633, B_632)) | ~v1_relat_1(A_634))), inference(resolution, [status(thm)], [c_925, c_4])).
% 16.83/7.24  tff(c_24115, plain, (![D_208, E_206, A_209, A_1]: (~r2_hidden(k4_tarski(D_208, E_206), k5_relat_1(A_209, k4_xboole_0(A_1, A_1))) | ~v1_relat_1(k5_relat_1(A_209, k4_xboole_0(A_1, A_1))) | ~v1_relat_1(k4_xboole_0(A_1, A_1)) | ~v1_relat_1(A_209))), inference(resolution, [status(thm)], [c_949, c_24111])).
% 16.83/7.24  tff(c_24317, plain, (![D_635, E_636, A_637]: (~r2_hidden(k4_tarski(D_635, E_636), k5_relat_1(A_637, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_637, k1_xboole_0)) | ~v1_relat_1(A_637))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_236, c_236, c_236, c_24115])).
% 16.83/7.24  tff(c_24376, plain, (![A_638]: (~v1_relat_1(A_638) | k5_relat_1(A_638, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_638, k1_xboole_0)))), inference(resolution, [status(thm)], [c_46, c_24317])).
% 16.83/7.24  tff(c_24380, plain, (![A_108]: (k5_relat_1(A_108, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_108))), inference(resolution, [status(thm)], [c_44, c_24376])).
% 16.83/7.24  tff(c_24384, plain, (![A_639]: (k5_relat_1(A_639, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_639))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_24380])).
% 16.83/7.24  tff(c_24396, plain, (k5_relat_1('#skF_11', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_24384])).
% 16.83/7.24  tff(c_24258, plain, (![D_208, E_206, A_209]: (~r2_hidden(k4_tarski(D_208, E_206), k5_relat_1(A_209, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_209, k1_xboole_0)) | ~v1_relat_1(A_209))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_236, c_236, c_236, c_24115])).
% 16.83/7.24  tff(c_24400, plain, (![D_208, E_206]: (~r2_hidden(k4_tarski(D_208, E_206), k1_xboole_0) | ~v1_relat_1(k5_relat_1('#skF_11', k1_xboole_0)) | ~v1_relat_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_24396, c_24258])).
% 16.83/7.24  tff(c_24457, plain, (![D_640, E_641]: (~r2_hidden(k4_tarski(D_640, E_641), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_55, c_24396, c_24400])).
% 16.83/7.24  tff(c_24489, plain, (![D_100, E_101, B_61]: (~r2_hidden(k4_tarski(D_100, E_101), k5_relat_1(k1_xboole_0, B_61)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_61)) | ~v1_relat_1(B_61) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_42, c_24457])).
% 16.83/7.24  tff(c_24574, plain, (![D_644, E_645, B_646]: (~r2_hidden(k4_tarski(D_644, E_645), k5_relat_1(k1_xboole_0, B_646)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_646)) | ~v1_relat_1(B_646))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_24489])).
% 16.83/7.24  tff(c_24954, plain, (![B_652]: (~v1_relat_1(B_652) | k5_relat_1(k1_xboole_0, B_652)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_652)))), inference(resolution, [status(thm)], [c_46, c_24574])).
% 16.83/7.24  tff(c_24961, plain, (![B_109]: (k5_relat_1(k1_xboole_0, B_109)=k1_xboole_0 | ~v1_relat_1(B_109) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_24954])).
% 16.83/7.24  tff(c_24967, plain, (![B_653]: (k5_relat_1(k1_xboole_0, B_653)=k1_xboole_0 | ~v1_relat_1(B_653))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_24961])).
% 16.83/7.24  tff(c_24976, plain, (k5_relat_1(k1_xboole_0, '#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_24967])).
% 16.83/7.24  tff(c_24983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_24976])).
% 16.83/7.24  tff(c_24984, plain, (k5_relat_1('#skF_11', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 16.83/7.24  tff(c_24985, plain, (k5_relat_1(k1_xboole_0, '#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 16.83/7.24  tff(c_25584, plain, (![E_719, B_720, D_721, A_722]: (r2_hidden(k4_tarski('#skF_3'(E_719, B_720, D_721, A_722, k5_relat_1(A_722, B_720)), E_719), B_720) | ~r2_hidden(k4_tarski(D_721, E_719), k5_relat_1(A_722, B_720)) | ~v1_relat_1(k5_relat_1(A_722, B_720)) | ~v1_relat_1(B_720) | ~v1_relat_1(A_722))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.83/7.24  tff(c_25602, plain, (![E_719, D_721]: (r2_hidden(k4_tarski('#skF_3'(E_719, '#skF_11', D_721, k1_xboole_0, k1_xboole_0), E_719), '#skF_11') | ~r2_hidden(k4_tarski(D_721, E_719), k5_relat_1(k1_xboole_0, '#skF_11')) | ~v1_relat_1(k5_relat_1(k1_xboole_0, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24985, c_25584])).
% 16.83/7.24  tff(c_25611, plain, (![E_719, D_721]: (r2_hidden(k4_tarski('#skF_3'(E_719, '#skF_11', D_721, k1_xboole_0, k1_xboole_0), E_719), '#skF_11') | ~r2_hidden(k4_tarski(D_721, E_719), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_50, c_55, c_24985, c_24985, c_25602])).
% 16.83/7.24  tff(c_25640, plain, (![D_730, E_731, B_732, A_733]: (r2_hidden(k4_tarski(D_730, '#skF_3'(E_731, B_732, D_730, A_733, k5_relat_1(A_733, B_732))), A_733) | ~r2_hidden(k4_tarski(D_730, E_731), k5_relat_1(A_733, B_732)) | ~v1_relat_1(k5_relat_1(A_733, B_732)) | ~v1_relat_1(B_732) | ~v1_relat_1(A_733))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.83/7.24  tff(c_25658, plain, (![D_730, E_731]: (r2_hidden(k4_tarski(D_730, '#skF_3'(E_731, '#skF_11', D_730, k1_xboole_0, k1_xboole_0)), k1_xboole_0) | ~r2_hidden(k4_tarski(D_730, E_731), k5_relat_1(k1_xboole_0, '#skF_11')) | ~v1_relat_1(k5_relat_1(k1_xboole_0, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24985, c_25640])).
% 16.83/7.24  tff(c_25668, plain, (![D_734, E_735]: (r2_hidden(k4_tarski(D_734, '#skF_3'(E_735, '#skF_11', D_734, k1_xboole_0, k1_xboole_0)), k1_xboole_0) | ~r2_hidden(k4_tarski(D_734, E_735), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_50, c_55, c_24985, c_24985, c_25658])).
% 16.83/7.24  tff(c_25052, plain, (![A_668, B_669, C_670]: (r2_hidden('#skF_1'(A_668, B_669, C_670), A_668) | r2_hidden('#skF_2'(A_668, B_669, C_670), C_670) | k4_xboole_0(A_668, B_669)=C_670)), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.83/7.24  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.83/7.24  tff(c_25084, plain, (![A_668, C_670]: (r2_hidden('#skF_2'(A_668, A_668, C_670), C_670) | k4_xboole_0(A_668, A_668)=C_670)), inference(resolution, [status(thm)], [c_25052, c_16])).
% 16.83/7.24  tff(c_25094, plain, (![A_671, C_672]: (r2_hidden('#skF_2'(A_671, A_671, C_672), C_672) | k4_xboole_0(A_671, A_671)=C_672)), inference(resolution, [status(thm)], [c_25052, c_16])).
% 16.83/7.24  tff(c_25140, plain, (![A_678, C_679]: (~r2_hidden('#skF_2'(A_678, A_678, C_679), k1_xboole_0) | k4_xboole_0(A_678, A_678)=C_679)), inference(resolution, [status(thm)], [c_25094, c_67])).
% 16.83/7.24  tff(c_25156, plain, (![A_680]: (k4_xboole_0(A_680, A_680)=k1_xboole_0)), inference(resolution, [status(thm)], [c_25084, c_25140])).
% 16.83/7.24  tff(c_25164, plain, (![D_6, A_680]: (r2_hidden(D_6, A_680) | ~r2_hidden(D_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_25156, c_6])).
% 16.83/7.24  tff(c_25685, plain, (![D_738, E_739, A_740]: (r2_hidden(k4_tarski(D_738, '#skF_3'(E_739, '#skF_11', D_738, k1_xboole_0, k1_xboole_0)), A_740) | ~r2_hidden(k4_tarski(D_738, E_739), k1_xboole_0))), inference(resolution, [status(thm)], [c_25668, c_25164])).
% 16.83/7.24  tff(c_38, plain, (![D_100, F_104, B_61, E_101, A_9]: (r2_hidden(k4_tarski(D_100, E_101), k5_relat_1(A_9, B_61)) | ~r2_hidden(k4_tarski(F_104, E_101), B_61) | ~r2_hidden(k4_tarski(D_100, F_104), A_9) | ~v1_relat_1(k5_relat_1(A_9, B_61)) | ~v1_relat_1(B_61) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.83/7.24  tff(c_26931, plain, (![E_813, D_814, A_816, D_812, A_815]: (r2_hidden(k4_tarski(D_814, '#skF_3'(E_813, '#skF_11', D_812, k1_xboole_0, k1_xboole_0)), k5_relat_1(A_815, A_816)) | ~r2_hidden(k4_tarski(D_814, D_812), A_815) | ~v1_relat_1(k5_relat_1(A_815, A_816)) | ~v1_relat_1(A_816) | ~v1_relat_1(A_815) | ~r2_hidden(k4_tarski(D_812, E_813), k1_xboole_0))), inference(resolution, [status(thm)], [c_25685, c_38])).
% 16.83/7.24  tff(c_26943, plain, (![D_814, E_813, D_812]: (r2_hidden(k4_tarski(D_814, '#skF_3'(E_813, '#skF_11', D_812, k1_xboole_0, k1_xboole_0)), k1_xboole_0) | ~r2_hidden(k4_tarski(D_814, D_812), k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, '#skF_11')) | ~v1_relat_1('#skF_11') | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(k4_tarski(D_812, E_813), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24985, c_26931])).
% 16.83/7.24  tff(c_27741, plain, (![D_842, E_843, D_844]: (r2_hidden(k4_tarski(D_842, '#skF_3'(E_843, '#skF_11', D_844, k1_xboole_0, k1_xboole_0)), k1_xboole_0) | ~r2_hidden(k4_tarski(D_842, D_844), k1_xboole_0) | ~r2_hidden(k4_tarski(D_844, E_843), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_50, c_55, c_24985, c_26943])).
% 16.83/7.24  tff(c_27756, plain, (![D_100, D_842, E_843, D_844, A_9]: (r2_hidden(k4_tarski(D_100, '#skF_3'(E_843, '#skF_11', D_844, k1_xboole_0, k1_xboole_0)), k5_relat_1(A_9, k1_xboole_0)) | ~r2_hidden(k4_tarski(D_100, D_842), A_9) | ~v1_relat_1(k5_relat_1(A_9, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_9) | ~r2_hidden(k4_tarski(D_842, D_844), k1_xboole_0) | ~r2_hidden(k4_tarski(D_844, E_843), k1_xboole_0))), inference(resolution, [status(thm)], [c_27741, c_38])).
% 16.83/7.24  tff(c_42172, plain, (![D_1107, A_1109, D_1106, E_1110, D_1108]: (r2_hidden(k4_tarski(D_1108, '#skF_3'(E_1110, '#skF_11', D_1106, k1_xboole_0, k1_xboole_0)), k5_relat_1(A_1109, k1_xboole_0)) | ~r2_hidden(k4_tarski(D_1108, D_1107), A_1109) | ~v1_relat_1(k5_relat_1(A_1109, k1_xboole_0)) | ~v1_relat_1(A_1109) | ~r2_hidden(k4_tarski(D_1107, D_1106), k1_xboole_0) | ~r2_hidden(k4_tarski(D_1106, E_1110), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_27756])).
% 16.83/7.24  tff(c_42198, plain, (![E_719, D_721, E_1110, D_1106]: (r2_hidden(k4_tarski('#skF_3'(E_719, '#skF_11', D_721, k1_xboole_0, k1_xboole_0), '#skF_3'(E_1110, '#skF_11', D_1106, k1_xboole_0, k1_xboole_0)), k5_relat_1('#skF_11', k1_xboole_0)) | ~v1_relat_1(k5_relat_1('#skF_11', k1_xboole_0)) | ~v1_relat_1('#skF_11') | ~r2_hidden(k4_tarski(E_719, D_1106), k1_xboole_0) | ~r2_hidden(k4_tarski(D_1106, E_1110), k1_xboole_0) | ~r2_hidden(k4_tarski(D_721, E_719), k1_xboole_0))), inference(resolution, [status(thm)], [c_25611, c_42172])).
% 16.83/7.24  tff(c_42222, plain, (![E_719, D_721, E_1110, D_1106]: (r2_hidden(k4_tarski('#skF_3'(E_719, '#skF_11', D_721, k1_xboole_0, k1_xboole_0), '#skF_3'(E_1110, '#skF_11', D_1106, k1_xboole_0, k1_xboole_0)), k5_relat_1('#skF_11', k1_xboole_0)) | ~v1_relat_1(k5_relat_1('#skF_11', k1_xboole_0)) | ~r2_hidden(k4_tarski(E_719, D_1106), k1_xboole_0) | ~r2_hidden(k4_tarski(D_1106, E_1110), k1_xboole_0) | ~r2_hidden(k4_tarski(D_721, E_719), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42198])).
% 16.83/7.24  tff(c_46094, plain, (~v1_relat_1(k5_relat_1('#skF_11', k1_xboole_0))), inference(splitLeft, [status(thm)], [c_42222])).
% 16.83/7.24  tff(c_46097, plain, (~v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_44, c_46094])).
% 16.83/7.24  tff(c_46101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_55, c_46097])).
% 16.83/7.24  tff(c_46103, plain, (v1_relat_1(k5_relat_1('#skF_11', k1_xboole_0))), inference(splitRight, [status(thm)], [c_42222])).
% 16.83/7.24  tff(c_25153, plain, (![A_668]: (k4_xboole_0(A_668, A_668)=k1_xboole_0)), inference(resolution, [status(thm)], [c_25084, c_25140])).
% 16.83/7.24  tff(c_25607, plain, (![A_722, B_2, A_1, E_719, D_721]: (r2_hidden(k4_tarski('#skF_3'(E_719, k4_xboole_0(A_1, B_2), D_721, A_722, k5_relat_1(A_722, k4_xboole_0(A_1, B_2))), E_719), A_1) | ~r2_hidden(k4_tarski(D_721, E_719), k5_relat_1(A_722, k4_xboole_0(A_1, B_2))) | ~v1_relat_1(k5_relat_1(A_722, k4_xboole_0(A_1, B_2))) | ~v1_relat_1(k4_xboole_0(A_1, B_2)) | ~v1_relat_1(A_722))), inference(resolution, [status(thm)], [c_25584, c_6])).
% 16.83/7.24  tff(c_46917, plain, (![D_1213, B_1211, E_1214, A_1212, A_1210]: (~r2_hidden(k4_tarski('#skF_3'(E_1214, k4_xboole_0(A_1212, B_1211), D_1213, A_1210, k5_relat_1(A_1210, k4_xboole_0(A_1212, B_1211))), E_1214), B_1211) | ~r2_hidden(k4_tarski(D_1213, E_1214), k5_relat_1(A_1210, k4_xboole_0(A_1212, B_1211))) | ~v1_relat_1(k5_relat_1(A_1210, k4_xboole_0(A_1212, B_1211))) | ~v1_relat_1(k4_xboole_0(A_1212, B_1211)) | ~v1_relat_1(A_1210))), inference(resolution, [status(thm)], [c_25584, c_4])).
% 16.83/7.24  tff(c_46921, plain, (![D_721, E_719, A_722, A_1]: (~r2_hidden(k4_tarski(D_721, E_719), k5_relat_1(A_722, k4_xboole_0(A_1, A_1))) | ~v1_relat_1(k5_relat_1(A_722, k4_xboole_0(A_1, A_1))) | ~v1_relat_1(k4_xboole_0(A_1, A_1)) | ~v1_relat_1(A_722))), inference(resolution, [status(thm)], [c_25607, c_46917])).
% 16.83/7.24  tff(c_47144, plain, (![D_1215, E_1216, A_1217]: (~r2_hidden(k4_tarski(D_1215, E_1216), k5_relat_1(A_1217, k1_xboole_0)) | ~v1_relat_1(k5_relat_1(A_1217, k1_xboole_0)) | ~v1_relat_1(A_1217))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_25153, c_25153, c_25153, c_46921])).
% 16.83/7.24  tff(c_47229, plain, (![A_1218]: (~v1_relat_1(A_1218) | k5_relat_1(A_1218, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_1218, k1_xboole_0)))), inference(resolution, [status(thm)], [c_46, c_47144])).
% 16.83/7.24  tff(c_47232, plain, (~v1_relat_1('#skF_11') | k5_relat_1('#skF_11', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_46103, c_47229])).
% 16.83/7.24  tff(c_47239, plain, (k5_relat_1('#skF_11', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_47232])).
% 16.83/7.24  tff(c_47241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24984, c_47239])).
% 16.83/7.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.83/7.24  
% 16.83/7.24  Inference rules
% 16.83/7.24  ----------------------
% 16.83/7.24  #Ref     : 0
% 16.83/7.24  #Sup     : 11825
% 16.83/7.24  #Fact    : 0
% 16.83/7.24  #Define  : 0
% 16.83/7.24  #Split   : 4
% 16.83/7.24  #Chain   : 0
% 16.83/7.24  #Close   : 0
% 16.83/7.24  
% 16.83/7.24  Ordering : KBO
% 16.83/7.24  
% 16.83/7.24  Simplification rules
% 16.83/7.24  ----------------------
% 16.83/7.24  #Subsume      : 4443
% 16.83/7.24  #Demod        : 11591
% 16.83/7.24  #Tautology    : 3530
% 16.83/7.24  #SimpNegUnit  : 9
% 16.83/7.24  #BackRed      : 65
% 16.83/7.24  
% 16.83/7.24  #Partial instantiations: 0
% 16.83/7.24  #Strategies tried      : 1
% 16.83/7.24  
% 16.83/7.24  Timing (in seconds)
% 16.83/7.24  ----------------------
% 16.83/7.24  Preprocessing        : 0.28
% 16.83/7.24  Parsing              : 0.14
% 16.83/7.24  CNF conversion       : 0.03
% 16.83/7.24  Main loop            : 6.09
% 16.83/7.24  Inferencing          : 1.48
% 16.83/7.24  Reduction            : 2.67
% 16.83/7.24  Demodulation         : 2.34
% 16.83/7.24  BG Simplification    : 0.14
% 16.83/7.24  Subsumption          : 1.52
% 16.83/7.24  Abstraction          : 0.29
% 16.83/7.24  MUC search           : 0.00
% 16.88/7.24  Cooper               : 0.00
% 16.88/7.24  Total                : 6.41
% 16.88/7.24  Index Insertion      : 0.00
% 16.88/7.24  Index Deletion       : 0.00
% 16.88/7.24  Index Matching       : 0.00
% 16.88/7.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
