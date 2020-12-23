%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:13 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 407 expanded)
%              Number of leaves         :   29 ( 143 expanded)
%              Depth                    :    9
%              Number of atoms          :  247 (1159 expanded)
%              Number of equality atoms :   86 ( 389 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    r2_hidden('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_zfmisc_1(k2_zfmisc_1(A_8,B_9),C_10) = k3_zfmisc_1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_436,plain,(
    ! [A_92,C_93,B_94] :
      ( r2_hidden(k2_mcart_1(A_92),C_93)
      | ~ r2_hidden(A_92,k2_zfmisc_1(B_94,C_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_454,plain,(
    ! [A_105,C_106,A_107,B_108] :
      ( r2_hidden(k2_mcart_1(A_105),C_106)
      | ~ r2_hidden(A_105,k3_zfmisc_1(A_107,B_108,C_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_436])).

tff(c_457,plain,(
    r2_hidden(k2_mcart_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_454])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_449,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( k7_mcart_1(A_101,B_102,C_103,D_104) = k2_mcart_1(D_104)
      | ~ m1_subset_1(D_104,k3_zfmisc_1(A_101,B_102,C_103))
      | k1_xboole_0 = C_103
      | k1_xboole_0 = B_102
      | k1_xboole_0 = A_101 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_453,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_449])).

tff(c_529,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_453])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_6')
    | ~ r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_5')
    | ~ r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_52,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_67,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( k7_mcart_1(A_49,B_50,C_51,D_52) = k2_mcart_1(D_52)
      | ~ m1_subset_1(D_52,k3_zfmisc_1(A_49,B_50,C_51))
      | k1_xboole_0 = C_51
      | k1_xboole_0 = B_50
      | k1_xboole_0 = A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_71,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_67])).

tff(c_169,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_173,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_2])).

tff(c_56,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden(k1_mcart_1(A_39),B_40)
      | ~ r2_hidden(A_39,k2_zfmisc_1(B_40,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_138,plain,(
    ! [A_68,A_69,B_70,C_71] :
      ( r2_hidden(k1_mcart_1(A_68),k2_zfmisc_1(A_69,B_70))
      | ~ r2_hidden(A_68,k3_zfmisc_1(A_69,B_70,C_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_56])).

tff(c_148,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_22,c_138])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( r2_hidden(k1_mcart_1(A_11),B_12)
      | ~ r2_hidden(A_11,k2_zfmisc_1(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_159,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_148,c_12])).

tff(c_4,plain,(
    ! [C_5,A_2,B_3] :
      ( r2_hidden(C_5,A_2)
      | ~ r2_hidden(C_5,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_202,plain,(
    ! [A_77] :
      ( r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')),A_77)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_77)) ) ),
    inference(resolution,[status(thm)],[c_159,c_4])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_250,plain,(
    ! [A_79] :
      ( ~ r1_tarski(A_79,k1_mcart_1(k1_mcart_1('#skF_7')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_79)) ) ),
    inference(resolution,[status(thm)],[c_202,c_6])).

tff(c_254,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_173,c_250])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_254])).

tff(c_260,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_130,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( k5_mcart_1(A_64,B_65,C_66,D_67) = k1_mcart_1(k1_mcart_1(D_67))
      | ~ m1_subset_1(D_67,k3_zfmisc_1(A_64,B_65,C_66))
      | k1_xboole_0 = C_66
      | k1_xboole_0 = B_65
      | k1_xboole_0 = A_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_137,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_130])).

tff(c_278,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_137])).

tff(c_279,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_285,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_2])).

tff(c_10,plain,(
    ! [A_11,C_13,B_12] :
      ( r2_hidden(k2_mcart_1(A_11),C_13)
      | ~ r2_hidden(A_11,k2_zfmisc_1(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_160,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_148,c_10])).

tff(c_321,plain,(
    ! [A_86] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')),A_86)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_86)) ) ),
    inference(resolution,[status(thm)],[c_160,c_4])).

tff(c_352,plain,(
    ! [A_89] :
      ( ~ r1_tarski(A_89,k2_mcart_1(k1_mcart_1('#skF_7')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_89)) ) ),
    inference(resolution,[status(thm)],[c_321,c_6])).

tff(c_356,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_285,c_352])).

tff(c_360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_356])).

tff(c_361,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_411,plain,(
    k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_414,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_159])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_414])).

tff(c_417,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_53,plain,(
    ! [A_36,C_37,B_38] :
      ( r2_hidden(k2_mcart_1(A_36),C_37)
      | ~ r2_hidden(A_36,k2_zfmisc_1(B_38,C_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_63,plain,(
    ! [A_45,C_46,A_47,B_48] :
      ( r2_hidden(k2_mcart_1(A_45),C_46)
      | ~ r2_hidden(A_45,k3_zfmisc_1(A_47,B_48,C_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_53])).

tff(c_66,plain,(
    r2_hidden(k2_mcart_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_63])).

tff(c_79,plain,(
    ! [A_53] :
      ( r2_hidden(k2_mcart_1('#skF_7'),A_53)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_53)) ) ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_100,plain,(
    ! [A_55] :
      ( ~ r1_tarski(A_55,k2_mcart_1('#skF_7'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_55)) ) ),
    inference(resolution,[status(thm)],[c_79,c_6])).

tff(c_105,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_100])).

tff(c_423,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_105])).

tff(c_428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_423])).

tff(c_430,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_442,plain,(
    ! [C_98,A_99,B_100] :
      ( r2_hidden(C_98,A_99)
      | ~ r2_hidden(C_98,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_492,plain,(
    ! [A_112] :
      ( r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),A_112)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_112)) ) ),
    inference(resolution,[status(thm)],[c_430,c_442])).

tff(c_512,plain,(
    ! [A_113] :
      ( ~ r1_tarski(A_113,k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_113)) ) ),
    inference(resolution,[status(thm)],[c_492,c_6])).

tff(c_517,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_512])).

tff(c_530,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_529,c_517])).

tff(c_537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_530])).

tff(c_538,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_453])).

tff(c_540,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_538])).

tff(c_429,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_5')
    | ~ r2_hidden(k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_435,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_541,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_435])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_541])).

tff(c_545,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_538])).

tff(c_547,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_545])).

tff(c_561,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_2])).

tff(c_439,plain,(
    ! [A_95,B_96,C_97] :
      ( r2_hidden(k1_mcart_1(A_95),B_96)
      | ~ r2_hidden(A_95,k2_zfmisc_1(B_96,C_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_579,plain,(
    ! [A_127,A_128,B_129,C_130] :
      ( r2_hidden(k1_mcart_1(A_127),k2_zfmisc_1(A_128,B_129))
      | ~ r2_hidden(A_127,k3_zfmisc_1(A_128,B_129,C_130)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_439])).

tff(c_590,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_22,c_579])).

tff(c_602,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_590,c_10])).

tff(c_642,plain,(
    ! [A_132] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')),A_132)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_132)) ) ),
    inference(resolution,[status(thm)],[c_602,c_4])).

tff(c_690,plain,(
    ! [A_138] :
      ( ~ r1_tarski(A_138,k2_mcart_1(k1_mcart_1('#skF_7')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_138)) ) ),
    inference(resolution,[status(thm)],[c_642,c_6])).

tff(c_694,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_561,c_690])).

tff(c_698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_694])).

tff(c_699,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_545])).

tff(c_466,plain,(
    ! [A_110] :
      ( r2_hidden(k2_mcart_1('#skF_7'),A_110)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_110)) ) ),
    inference(resolution,[status(thm)],[c_457,c_4])).

tff(c_486,plain,(
    ! [A_111] :
      ( ~ r1_tarski(A_111,k2_mcart_1('#skF_7'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_111)) ) ),
    inference(resolution,[status(thm)],[c_466,c_6])).

tff(c_491,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_486])).

tff(c_705,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_491])).

tff(c_710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_705])).

tff(c_711,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_811,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( k7_mcart_1(A_157,B_158,C_159,D_160) = k2_mcart_1(D_160)
      | ~ m1_subset_1(D_160,k3_zfmisc_1(A_157,B_158,C_159))
      | k1_xboole_0 = C_159
      | k1_xboole_0 = B_158
      | k1_xboole_0 = A_157 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_815,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_811])).

tff(c_828,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_815])).

tff(c_723,plain,(
    ! [C_145,A_146,B_147] :
      ( r2_hidden(C_145,A_146)
      | ~ r2_hidden(C_145,B_147)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_771,plain,(
    ! [A_155] :
      ( r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),A_155)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_155)) ) ),
    inference(resolution,[status(thm)],[c_430,c_723])).

tff(c_816,plain,(
    ! [A_161] :
      ( ~ r1_tarski(A_161,k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_161)) ) ),
    inference(resolution,[status(thm)],[c_771,c_6])).

tff(c_821,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_816])).

tff(c_829,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_821])).

tff(c_835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_829])).

tff(c_837,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_815])).

tff(c_851,plain,(
    ! [A_165,B_166,C_167,D_168] :
      ( k5_mcart_1(A_165,B_166,C_167,D_168) = k1_mcart_1(k1_mcart_1(D_168))
      | ~ m1_subset_1(D_168,k3_zfmisc_1(A_165,B_166,C_167))
      | k1_xboole_0 = C_167
      | k1_xboole_0 = B_166
      | k1_xboole_0 = A_165 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_854,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_851])).

tff(c_857,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_837,c_854])).

tff(c_882,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_857])).

tff(c_888,plain,(
    ! [A_1] : r1_tarski('#skF_2',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_882,c_2])).

tff(c_717,plain,(
    ! [A_139,B_140,C_141] :
      ( r2_hidden(k1_mcart_1(A_139),B_140)
      | ~ r2_hidden(A_139,k2_zfmisc_1(B_140,C_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_916,plain,(
    ! [A_180,A_181,B_182,C_183] :
      ( r2_hidden(k1_mcart_1(A_180),k2_zfmisc_1(A_181,B_182))
      | ~ r2_hidden(A_180,k3_zfmisc_1(A_181,B_182,C_183)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_717])).

tff(c_930,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_22,c_916])).

tff(c_941,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_930,c_10])).

tff(c_958,plain,(
    ! [A_184] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')),A_184)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_184)) ) ),
    inference(resolution,[status(thm)],[c_941,c_4])).

tff(c_1007,plain,(
    ! [A_186] :
      ( ~ r1_tarski(A_186,k2_mcart_1(k1_mcart_1('#skF_7')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_186)) ) ),
    inference(resolution,[status(thm)],[c_958,c_6])).

tff(c_1011,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_888,c_1007])).

tff(c_1015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1011])).

tff(c_1017,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_857])).

tff(c_1060,plain,(
    ! [A_191,B_192,C_193,D_194] :
      ( k6_mcart_1(A_191,B_192,C_193,D_194) = k2_mcart_1(k1_mcart_1(D_194))
      | ~ m1_subset_1(D_194,k3_zfmisc_1(A_191,B_192,C_193))
      | k1_xboole_0 = C_193
      | k1_xboole_0 = B_192
      | k1_xboole_0 = A_191 ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1066,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_24,c_1060])).

tff(c_1069,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_837,c_1017,c_1066])).

tff(c_1094,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1069])).

tff(c_720,plain,(
    ! [A_142,C_143,B_144] :
      ( r2_hidden(k2_mcart_1(A_142),C_143)
      | ~ r2_hidden(A_142,k2_zfmisc_1(B_144,C_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_733,plain,(
    ! [A_148,C_149,A_150,B_151] :
      ( r2_hidden(k2_mcart_1(A_148),C_149)
      | ~ r2_hidden(A_148,k3_zfmisc_1(A_150,B_151,C_149)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_720])).

tff(c_736,plain,(
    r2_hidden(k2_mcart_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_733])).

tff(c_745,plain,(
    ! [A_153] :
      ( r2_hidden(k2_mcart_1('#skF_7'),A_153)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_153)) ) ),
    inference(resolution,[status(thm)],[c_736,c_4])).

tff(c_765,plain,(
    ! [A_154] :
      ( ~ r1_tarski(A_154,k2_mcart_1('#skF_7'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_154)) ) ),
    inference(resolution,[status(thm)],[c_745,c_6])).

tff(c_770,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2,c_765])).

tff(c_1101,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1094,c_770])).

tff(c_1105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1101])).

tff(c_1106,plain,(
    k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_1069])).

tff(c_1024,plain,(
    ! [A_187,A_188,B_189,C_190] :
      ( r2_hidden(k1_mcart_1(A_187),k2_zfmisc_1(A_188,B_189))
      | ~ r2_hidden(A_187,k3_zfmisc_1(A_188,B_189,C_190)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_717])).

tff(c_1038,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_22,c_1024])).

tff(c_1049,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_1038,c_10])).

tff(c_1110,plain,(
    r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1106,c_1049])).

tff(c_1112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_711,c_1110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.51  
% 3.36/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.51  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.36/1.51  
% 3.36/1.51  %Foreground sorts:
% 3.36/1.51  
% 3.36/1.51  
% 3.36/1.51  %Background operators:
% 3.36/1.51  
% 3.36/1.51  
% 3.36/1.51  %Foreground operators:
% 3.36/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.36/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.36/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.36/1.51  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.36/1.51  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.36/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.51  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.36/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.51  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.36/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.36/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.51  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.36/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.51  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.36/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.51  
% 3.36/1.53  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 3.36/1.53  tff(f_41, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.36/1.53  tff(f_47, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.36/1.53  tff(f_67, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.36/1.53  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.36/1.53  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.36/1.53  tff(f_39, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.36/1.53  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.36/1.53  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.36/1.53  tff(c_22, plain, (r2_hidden('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.36/1.53  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_zfmisc_1(k2_zfmisc_1(A_8, B_9), C_10)=k3_zfmisc_1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.36/1.53  tff(c_436, plain, (![A_92, C_93, B_94]: (r2_hidden(k2_mcart_1(A_92), C_93) | ~r2_hidden(A_92, k2_zfmisc_1(B_94, C_93)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.53  tff(c_454, plain, (![A_105, C_106, A_107, B_108]: (r2_hidden(k2_mcart_1(A_105), C_106) | ~r2_hidden(A_105, k3_zfmisc_1(A_107, B_108, C_106)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_436])).
% 3.36/1.53  tff(c_457, plain, (r2_hidden(k2_mcart_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_22, c_454])).
% 3.36/1.53  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.36/1.53  tff(c_24, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.36/1.53  tff(c_449, plain, (![A_101, B_102, C_103, D_104]: (k7_mcart_1(A_101, B_102, C_103, D_104)=k2_mcart_1(D_104) | ~m1_subset_1(D_104, k3_zfmisc_1(A_101, B_102, C_103)) | k1_xboole_0=C_103 | k1_xboole_0=B_102 | k1_xboole_0=A_101)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.36/1.53  tff(c_453, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_24, c_449])).
% 3.36/1.53  tff(c_529, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_453])).
% 3.36/1.53  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.36/1.53  tff(c_20, plain, (~r2_hidden(k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_6') | ~r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_5') | ~r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.36/1.53  tff(c_52, plain, (~r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_4')), inference(splitLeft, [status(thm)], [c_20])).
% 3.36/1.53  tff(c_67, plain, (![A_49, B_50, C_51, D_52]: (k7_mcart_1(A_49, B_50, C_51, D_52)=k2_mcart_1(D_52) | ~m1_subset_1(D_52, k3_zfmisc_1(A_49, B_50, C_51)) | k1_xboole_0=C_51 | k1_xboole_0=B_50 | k1_xboole_0=A_49)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.36/1.53  tff(c_71, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_24, c_67])).
% 3.36/1.53  tff(c_169, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_71])).
% 3.36/1.53  tff(c_173, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_2])).
% 3.36/1.53  tff(c_56, plain, (![A_39, B_40, C_41]: (r2_hidden(k1_mcart_1(A_39), B_40) | ~r2_hidden(A_39, k2_zfmisc_1(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.53  tff(c_138, plain, (![A_68, A_69, B_70, C_71]: (r2_hidden(k1_mcart_1(A_68), k2_zfmisc_1(A_69, B_70)) | ~r2_hidden(A_68, k3_zfmisc_1(A_69, B_70, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_56])).
% 3.36/1.53  tff(c_148, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_138])).
% 3.36/1.53  tff(c_12, plain, (![A_11, B_12, C_13]: (r2_hidden(k1_mcart_1(A_11), B_12) | ~r2_hidden(A_11, k2_zfmisc_1(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.53  tff(c_159, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')), '#skF_4')), inference(resolution, [status(thm)], [c_148, c_12])).
% 3.36/1.53  tff(c_4, plain, (![C_5, A_2, B_3]: (r2_hidden(C_5, A_2) | ~r2_hidden(C_5, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.36/1.53  tff(c_202, plain, (![A_77]: (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')), A_77) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_77)))), inference(resolution, [status(thm)], [c_159, c_4])).
% 3.36/1.53  tff(c_6, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.36/1.53  tff(c_250, plain, (![A_79]: (~r1_tarski(A_79, k1_mcart_1(k1_mcart_1('#skF_7'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_79)))), inference(resolution, [status(thm)], [c_202, c_6])).
% 3.36/1.53  tff(c_254, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_173, c_250])).
% 3.36/1.53  tff(c_258, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_254])).
% 3.36/1.53  tff(c_260, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_71])).
% 3.36/1.53  tff(c_130, plain, (![A_64, B_65, C_66, D_67]: (k5_mcart_1(A_64, B_65, C_66, D_67)=k1_mcart_1(k1_mcart_1(D_67)) | ~m1_subset_1(D_67, k3_zfmisc_1(A_64, B_65, C_66)) | k1_xboole_0=C_66 | k1_xboole_0=B_65 | k1_xboole_0=A_64)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.36/1.53  tff(c_137, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_24, c_130])).
% 3.36/1.53  tff(c_278, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_260, c_137])).
% 3.36/1.53  tff(c_279, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_278])).
% 3.36/1.53  tff(c_285, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_2])).
% 3.36/1.53  tff(c_10, plain, (![A_11, C_13, B_12]: (r2_hidden(k2_mcart_1(A_11), C_13) | ~r2_hidden(A_11, k2_zfmisc_1(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.53  tff(c_160, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')), '#skF_5')), inference(resolution, [status(thm)], [c_148, c_10])).
% 3.36/1.53  tff(c_321, plain, (![A_86]: (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')), A_86) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_86)))), inference(resolution, [status(thm)], [c_160, c_4])).
% 3.36/1.53  tff(c_352, plain, (![A_89]: (~r1_tarski(A_89, k2_mcart_1(k1_mcart_1('#skF_7'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_89)))), inference(resolution, [status(thm)], [c_321, c_6])).
% 3.36/1.53  tff(c_356, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_285, c_352])).
% 3.36/1.53  tff(c_360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_356])).
% 3.36/1.53  tff(c_361, plain, (k1_xboole_0='#skF_3' | k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')), inference(splitRight, [status(thm)], [c_278])).
% 3.36/1.53  tff(c_411, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')), inference(splitLeft, [status(thm)], [c_361])).
% 3.36/1.53  tff(c_414, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_411, c_159])).
% 3.36/1.53  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_414])).
% 3.36/1.53  tff(c_417, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_361])).
% 3.36/1.53  tff(c_53, plain, (![A_36, C_37, B_38]: (r2_hidden(k2_mcart_1(A_36), C_37) | ~r2_hidden(A_36, k2_zfmisc_1(B_38, C_37)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.53  tff(c_63, plain, (![A_45, C_46, A_47, B_48]: (r2_hidden(k2_mcart_1(A_45), C_46) | ~r2_hidden(A_45, k3_zfmisc_1(A_47, B_48, C_46)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_53])).
% 3.36/1.53  tff(c_66, plain, (r2_hidden(k2_mcart_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_22, c_63])).
% 3.36/1.53  tff(c_79, plain, (![A_53]: (r2_hidden(k2_mcart_1('#skF_7'), A_53) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_53)))), inference(resolution, [status(thm)], [c_66, c_4])).
% 3.36/1.53  tff(c_100, plain, (![A_55]: (~r1_tarski(A_55, k2_mcart_1('#skF_7')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_55)))), inference(resolution, [status(thm)], [c_79, c_6])).
% 3.36/1.53  tff(c_105, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_100])).
% 3.36/1.53  tff(c_423, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_417, c_105])).
% 3.36/1.53  tff(c_428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_423])).
% 3.36/1.53  tff(c_430, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_4')), inference(splitRight, [status(thm)], [c_20])).
% 3.36/1.53  tff(c_442, plain, (![C_98, A_99, B_100]: (r2_hidden(C_98, A_99) | ~r2_hidden(C_98, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.36/1.53  tff(c_492, plain, (![A_112]: (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), A_112) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_112)))), inference(resolution, [status(thm)], [c_430, c_442])).
% 3.36/1.53  tff(c_512, plain, (![A_113]: (~r1_tarski(A_113, k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_113)))), inference(resolution, [status(thm)], [c_492, c_6])).
% 3.36/1.53  tff(c_517, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_512])).
% 3.36/1.53  tff(c_530, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_529, c_517])).
% 3.36/1.53  tff(c_537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_530])).
% 3.36/1.53  tff(c_538, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')=k2_mcart_1('#skF_7')), inference(splitRight, [status(thm)], [c_453])).
% 3.36/1.53  tff(c_540, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')=k2_mcart_1('#skF_7')), inference(splitLeft, [status(thm)], [c_538])).
% 3.36/1.53  tff(c_429, plain, (~r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_5') | ~r2_hidden(k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_20])).
% 3.36/1.53  tff(c_435, plain, (~r2_hidden(k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_429])).
% 3.36/1.53  tff(c_541, plain, (~r2_hidden(k2_mcart_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_540, c_435])).
% 3.36/1.53  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_457, c_541])).
% 3.36/1.53  tff(c_545, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_538])).
% 3.36/1.53  tff(c_547, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_545])).
% 3.36/1.53  tff(c_561, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_547, c_2])).
% 3.36/1.53  tff(c_439, plain, (![A_95, B_96, C_97]: (r2_hidden(k1_mcart_1(A_95), B_96) | ~r2_hidden(A_95, k2_zfmisc_1(B_96, C_97)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.53  tff(c_579, plain, (![A_127, A_128, B_129, C_130]: (r2_hidden(k1_mcart_1(A_127), k2_zfmisc_1(A_128, B_129)) | ~r2_hidden(A_127, k3_zfmisc_1(A_128, B_129, C_130)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_439])).
% 3.36/1.53  tff(c_590, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_579])).
% 3.36/1.53  tff(c_602, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')), '#skF_5')), inference(resolution, [status(thm)], [c_590, c_10])).
% 3.36/1.53  tff(c_642, plain, (![A_132]: (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')), A_132) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_132)))), inference(resolution, [status(thm)], [c_602, c_4])).
% 3.36/1.53  tff(c_690, plain, (![A_138]: (~r1_tarski(A_138, k2_mcart_1(k1_mcart_1('#skF_7'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_138)))), inference(resolution, [status(thm)], [c_642, c_6])).
% 3.36/1.53  tff(c_694, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_561, c_690])).
% 3.36/1.53  tff(c_698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_694])).
% 3.36/1.53  tff(c_699, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_545])).
% 3.36/1.53  tff(c_466, plain, (![A_110]: (r2_hidden(k2_mcart_1('#skF_7'), A_110) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_110)))), inference(resolution, [status(thm)], [c_457, c_4])).
% 3.36/1.53  tff(c_486, plain, (![A_111]: (~r1_tarski(A_111, k2_mcart_1('#skF_7')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_111)))), inference(resolution, [status(thm)], [c_466, c_6])).
% 3.36/1.53  tff(c_491, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_486])).
% 3.36/1.53  tff(c_705, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_699, c_491])).
% 3.36/1.53  tff(c_710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_705])).
% 3.36/1.53  tff(c_711, plain, (~r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_429])).
% 3.36/1.53  tff(c_811, plain, (![A_157, B_158, C_159, D_160]: (k7_mcart_1(A_157, B_158, C_159, D_160)=k2_mcart_1(D_160) | ~m1_subset_1(D_160, k3_zfmisc_1(A_157, B_158, C_159)) | k1_xboole_0=C_159 | k1_xboole_0=B_158 | k1_xboole_0=A_157)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.36/1.53  tff(c_815, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_24, c_811])).
% 3.36/1.53  tff(c_828, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_815])).
% 3.36/1.53  tff(c_723, plain, (![C_145, A_146, B_147]: (r2_hidden(C_145, A_146) | ~r2_hidden(C_145, B_147) | ~m1_subset_1(B_147, k1_zfmisc_1(A_146)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.36/1.53  tff(c_771, plain, (![A_155]: (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), A_155) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_155)))), inference(resolution, [status(thm)], [c_430, c_723])).
% 3.36/1.53  tff(c_816, plain, (![A_161]: (~r1_tarski(A_161, k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_161)))), inference(resolution, [status(thm)], [c_771, c_6])).
% 3.36/1.53  tff(c_821, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_816])).
% 3.36/1.53  tff(c_829, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_828, c_821])).
% 3.36/1.53  tff(c_835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_829])).
% 3.36/1.53  tff(c_837, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_815])).
% 3.36/1.53  tff(c_851, plain, (![A_165, B_166, C_167, D_168]: (k5_mcart_1(A_165, B_166, C_167, D_168)=k1_mcart_1(k1_mcart_1(D_168)) | ~m1_subset_1(D_168, k3_zfmisc_1(A_165, B_166, C_167)) | k1_xboole_0=C_167 | k1_xboole_0=B_166 | k1_xboole_0=A_165)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.36/1.53  tff(c_854, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_24, c_851])).
% 3.36/1.53  tff(c_857, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_837, c_854])).
% 3.36/1.53  tff(c_882, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_857])).
% 3.36/1.53  tff(c_888, plain, (![A_1]: (r1_tarski('#skF_2', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_882, c_2])).
% 3.36/1.53  tff(c_717, plain, (![A_139, B_140, C_141]: (r2_hidden(k1_mcart_1(A_139), B_140) | ~r2_hidden(A_139, k2_zfmisc_1(B_140, C_141)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.53  tff(c_916, plain, (![A_180, A_181, B_182, C_183]: (r2_hidden(k1_mcart_1(A_180), k2_zfmisc_1(A_181, B_182)) | ~r2_hidden(A_180, k3_zfmisc_1(A_181, B_182, C_183)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_717])).
% 3.36/1.53  tff(c_930, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_916])).
% 3.36/1.53  tff(c_941, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')), '#skF_5')), inference(resolution, [status(thm)], [c_930, c_10])).
% 3.36/1.53  tff(c_958, plain, (![A_184]: (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')), A_184) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_184)))), inference(resolution, [status(thm)], [c_941, c_4])).
% 3.36/1.53  tff(c_1007, plain, (![A_186]: (~r1_tarski(A_186, k2_mcart_1(k1_mcart_1('#skF_7'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_186)))), inference(resolution, [status(thm)], [c_958, c_6])).
% 3.36/1.53  tff(c_1011, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_888, c_1007])).
% 3.36/1.53  tff(c_1015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1011])).
% 3.36/1.53  tff(c_1017, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_857])).
% 3.36/1.53  tff(c_1060, plain, (![A_191, B_192, C_193, D_194]: (k6_mcart_1(A_191, B_192, C_193, D_194)=k2_mcart_1(k1_mcart_1(D_194)) | ~m1_subset_1(D_194, k3_zfmisc_1(A_191, B_192, C_193)) | k1_xboole_0=C_193 | k1_xboole_0=B_192 | k1_xboole_0=A_191)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.36/1.53  tff(c_1066, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_24, c_1060])).
% 3.36/1.53  tff(c_1069, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_837, c_1017, c_1066])).
% 3.36/1.53  tff(c_1094, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1069])).
% 3.36/1.53  tff(c_720, plain, (![A_142, C_143, B_144]: (r2_hidden(k2_mcart_1(A_142), C_143) | ~r2_hidden(A_142, k2_zfmisc_1(B_144, C_143)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.53  tff(c_733, plain, (![A_148, C_149, A_150, B_151]: (r2_hidden(k2_mcart_1(A_148), C_149) | ~r2_hidden(A_148, k3_zfmisc_1(A_150, B_151, C_149)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_720])).
% 3.36/1.53  tff(c_736, plain, (r2_hidden(k2_mcart_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_22, c_733])).
% 3.36/1.53  tff(c_745, plain, (![A_153]: (r2_hidden(k2_mcart_1('#skF_7'), A_153) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_153)))), inference(resolution, [status(thm)], [c_736, c_4])).
% 3.36/1.53  tff(c_765, plain, (![A_154]: (~r1_tarski(A_154, k2_mcart_1('#skF_7')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_154)))), inference(resolution, [status(thm)], [c_745, c_6])).
% 3.36/1.53  tff(c_770, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_765])).
% 3.36/1.53  tff(c_1101, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1094, c_770])).
% 3.36/1.53  tff(c_1105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1101])).
% 3.36/1.53  tff(c_1106, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')), inference(splitRight, [status(thm)], [c_1069])).
% 3.36/1.53  tff(c_1024, plain, (![A_187, A_188, B_189, C_190]: (r2_hidden(k1_mcart_1(A_187), k2_zfmisc_1(A_188, B_189)) | ~r2_hidden(A_187, k3_zfmisc_1(A_188, B_189, C_190)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_717])).
% 3.36/1.53  tff(c_1038, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_1024])).
% 3.36/1.53  tff(c_1049, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')), '#skF_5')), inference(resolution, [status(thm)], [c_1038, c_10])).
% 3.36/1.53  tff(c_1110, plain, (r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1106, c_1049])).
% 3.36/1.53  tff(c_1112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_711, c_1110])).
% 3.36/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.53  
% 3.36/1.53  Inference rules
% 3.36/1.53  ----------------------
% 3.36/1.53  #Ref     : 0
% 3.36/1.53  #Sup     : 238
% 3.36/1.53  #Fact    : 0
% 3.36/1.53  #Define  : 0
% 3.36/1.53  #Split   : 13
% 3.36/1.53  #Chain   : 0
% 3.36/1.53  #Close   : 0
% 3.36/1.53  
% 3.36/1.53  Ordering : KBO
% 3.36/1.53  
% 3.36/1.53  Simplification rules
% 3.36/1.53  ----------------------
% 3.36/1.53  #Subsume      : 18
% 3.36/1.53  #Demod        : 146
% 3.36/1.53  #Tautology    : 32
% 3.36/1.53  #SimpNegUnit  : 9
% 3.36/1.53  #BackRed      : 65
% 3.36/1.53  
% 3.36/1.53  #Partial instantiations: 0
% 3.36/1.53  #Strategies tried      : 1
% 3.36/1.53  
% 3.36/1.53  Timing (in seconds)
% 3.36/1.53  ----------------------
% 3.36/1.54  Preprocessing        : 0.31
% 3.36/1.54  Parsing              : 0.16
% 3.36/1.54  CNF conversion       : 0.02
% 3.36/1.54  Main loop            : 0.44
% 3.36/1.54  Inferencing          : 0.16
% 3.36/1.54  Reduction            : 0.13
% 3.36/1.54  Demodulation         : 0.09
% 3.36/1.54  BG Simplification    : 0.02
% 3.36/1.54  Subsumption          : 0.08
% 3.36/1.54  Abstraction          : 0.03
% 3.36/1.54  MUC search           : 0.00
% 3.36/1.54  Cooper               : 0.00
% 3.36/1.54  Total                : 0.80
% 3.36/1.54  Index Insertion      : 0.00
% 3.36/1.54  Index Deletion       : 0.00
% 3.36/1.54  Index Matching       : 0.00
% 3.36/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
