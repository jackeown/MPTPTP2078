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
% DateTime   : Thu Dec  3 10:10:23 EST 2020

% Result     : Theorem 17.08s
% Output     : CNFRefutation 17.56s
% Verified   : 
% Statistics : Number of formulae       :  675 (8119 expanded)
%              Number of leaves         :   46 (2468 expanded)
%              Depth                    :   18
%              Number of atoms          : 1112 (27292 expanded)
%              Number of equality atoms :  640 (9983 expanded)
%              Maximal formula depth    :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_157,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(A))
       => ! [F] :
            ( m1_subset_1(F,k1_zfmisc_1(B))
           => ! [G] :
                ( m1_subset_1(G,k1_zfmisc_1(C))
               => ! [H] :
                    ( m1_subset_1(H,k1_zfmisc_1(D))
                   => ! [I] :
                        ( m1_subset_1(I,k4_zfmisc_1(A,B,C,D))
                       => ( r2_hidden(I,k4_zfmisc_1(E,F,G,H))
                         => ( r2_hidden(k8_mcart_1(A,B,C,D,I),E)
                            & r2_hidden(k9_mcart_1(A,B,C,D,I),F)
                            & r2_hidden(k10_mcart_1(A,B,C,D,I),G)
                            & r2_hidden(k11_mcart_1(A,B,C,D,I),H) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_mcart_1)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ( k8_mcart_1(A,B,C,D,E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k9_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k10_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(E))
                & k11_mcart_1(A,B,C,D,E) = k2_mcart_1(E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,B)
     => ( ( r2_hidden(C,B)
          & A != C )
        | k3_xboole_0(k2_tarski(A,C),B) = k1_tarski(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k11_mcart_1(A,B,C,D,E),D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_mcart_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_80,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k10_mcart_1(A,B,C,D,E),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_mcart_1)).

tff(f_88,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k8_mcart_1(A,B,C,D,E),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_mcart_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_92,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k9_mcart_1(A,B,C,D,E),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_mcart_1)).

tff(c_28,plain,(
    ! [B_17,A_16] :
      ( m1_subset_1(B_17,A_16)
      | ~ v1_xboole_0(B_17)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( r2_hidden(B_17,A_16)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_66,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_4852,plain,(
    ! [C_544,D_543,A_547,E_546,B_545] :
      ( k11_mcart_1(A_547,B_545,C_544,D_543,E_546) = k2_mcart_1(E_546)
      | ~ m1_subset_1(E_546,k4_zfmisc_1(A_547,B_545,C_544,D_543))
      | k1_xboole_0 = D_543
      | k1_xboole_0 = C_544
      | k1_xboole_0 = B_545
      | k1_xboole_0 = A_547 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4901,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_4852])).

tff(c_4909,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4901])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_367,plain,(
    ! [C_123,B_124] :
      ( k3_xboole_0(k2_tarski(C_123,C_123),B_124) = k1_tarski(C_123)
      | ~ r2_hidden(C_123,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_384,plain,(
    ! [C_125] :
      ( k1_tarski(C_125) = k1_xboole_0
      | ~ r2_hidden(C_125,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_8])).

tff(c_394,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_384])).

tff(c_395,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_4919,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4909,c_395])).

tff(c_4926,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4909,c_4909,c_8])).

tff(c_74,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_205,plain,(
    ! [A_101,B_102] :
      ( r1_tarski(A_101,B_102)
      | ~ m1_subset_1(A_101,k1_zfmisc_1(B_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_230,plain,(
    r1_tarski('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_205])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_243,plain,(
    k3_xboole_0('#skF_6','#skF_2') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_230,c_6])).

tff(c_4991,plain,(
    '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4926,c_243])).

tff(c_62,plain,
    ( ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9')
    | ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7')
    | ~ r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_235,plain,(
    ~ r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_281,plain,
    ( ~ m1_subset_1(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_235])).

tff(c_323,plain,(
    ~ m1_subset_1(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_327,plain,
    ( ~ v1_xboole_0(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_323])).

tff(c_396,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_5029,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4991,c_396])).

tff(c_5039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4919,c_5029])).

tff(c_5040,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_4901])).

tff(c_5200,plain,(
    k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_5040])).

tff(c_38,plain,(
    ! [A_25,E_29,C_27,D_28,B_26] :
      ( m1_subset_1(k11_mcart_1(A_25,B_26,C_27,D_28,E_29),D_28)
      | ~ m1_subset_1(E_29,k4_zfmisc_1(A_25,B_26,C_27,D_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5204,plain,
    ( m1_subset_1(k2_mcart_1('#skF_10'),'#skF_5')
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5200,c_38])).

tff(c_5208,plain,(
    m1_subset_1(k2_mcart_1('#skF_10'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5204])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( v1_xboole_0(B_17)
      | ~ m1_subset_1(B_17,A_16)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5213,plain,
    ( v1_xboole_0(k2_mcart_1('#skF_10'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5208,c_30])).

tff(c_5214,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5213])).

tff(c_64,plain,(
    r2_hidden('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_64,c_2])).

tff(c_287,plain,(
    ! [B_109,A_110] :
      ( m1_subset_1(B_109,A_110)
      | ~ r2_hidden(B_109,A_110)
      | v1_xboole_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_293,plain,
    ( m1_subset_1('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9'))
    | v1_xboole_0(k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_64,c_287])).

tff(c_300,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_293])).

tff(c_4899,plain,
    ( k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_300,c_4852])).

tff(c_5964,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4899])).

tff(c_5993,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5964,c_395])).

tff(c_6003,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_396,c_5993])).

tff(c_6004,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9'
    | k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_4899])).

tff(c_6006,plain,(
    k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_6004])).

tff(c_4766,plain,(
    ! [B_526,C_525,E_527,D_523,A_524] :
      ( m1_subset_1(k11_mcart_1(A_524,B_526,C_525,D_523,E_527),D_523)
      | ~ m1_subset_1(E_527,k4_zfmisc_1(A_524,B_526,C_525,D_523)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6020,plain,(
    ! [E_654,B_652,C_653,A_651,D_650] :
      ( v1_xboole_0(k11_mcart_1(A_651,B_652,C_653,D_650,E_654))
      | ~ v1_xboole_0(D_650)
      | ~ m1_subset_1(E_654,k4_zfmisc_1(A_651,B_652,C_653,D_650)) ) ),
    inference(resolution,[status(thm)],[c_4766,c_30])).

tff(c_6039,plain,
    ( v1_xboole_0(k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10'))
    | ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_300,c_6020])).

tff(c_6068,plain,
    ( v1_xboole_0(k2_mcart_1('#skF_10'))
    | ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6006,c_6039])).

tff(c_6075,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_6068])).

tff(c_6005,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4899])).

tff(c_5041,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4901])).

tff(c_5101,plain,(
    ! [C_572,D_571,B_573,E_574,A_575] :
      ( k2_mcart_1(k1_mcart_1(E_574)) = k10_mcart_1(A_575,B_573,C_572,D_571,E_574)
      | ~ m1_subset_1(E_574,k4_zfmisc_1(A_575,B_573,C_572,D_571))
      | k1_xboole_0 = D_571
      | k1_xboole_0 = C_572
      | k1_xboole_0 = B_573
      | k1_xboole_0 = A_575 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_5127,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_5101])).

tff(c_5152,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_5041,c_5127])).

tff(c_5308,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5152])).

tff(c_333,plain,(
    ! [A_119,B_120] :
      ( k4_xboole_0(k1_tarski(A_119),B_120) = k1_tarski(A_119)
      | r2_hidden(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | k4_xboole_0(k1_tarski(A_9),B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_342,plain,(
    ! [A_119,B_120] :
      ( r2_hidden(A_119,B_120)
      | k1_tarski(A_119) != k1_xboole_0
      | r2_hidden(A_119,B_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_12])).

tff(c_424,plain,(
    ! [A_128,B_129] :
      ( k1_tarski(A_128) != k1_xboole_0
      | r2_hidden(A_128,B_129) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_342])).

tff(c_444,plain,(
    ! [B_129,A_128] :
      ( ~ v1_xboole_0(B_129)
      | k1_tarski(A_128) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_424,c_2])).

tff(c_471,plain,(
    ! [A_128] : k1_tarski(A_128) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_444])).

tff(c_374,plain,(
    ! [C_123] :
      ( k1_tarski(C_123) = k1_xboole_0
      | ~ r2_hidden(C_123,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_8])).

tff(c_472,plain,(
    ! [C_123] : ~ r2_hidden(C_123,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_471,c_374])).

tff(c_5330,plain,(
    ! [C_123] : ~ r2_hidden(C_123,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5308,c_472])).

tff(c_50,plain,(
    ! [A_40,C_42,D_43] : k4_zfmisc_1(A_40,k1_xboole_0,C_42,D_43) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_5336,plain,(
    ! [A_40,C_42,D_43] : k4_zfmisc_1(A_40,'#skF_3',C_42,D_43) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5308,c_5308,c_50])).

tff(c_5339,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5308,c_5308,c_8])).

tff(c_72,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_229,plain,(
    r1_tarski('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_205])).

tff(c_247,plain,(
    k3_xboole_0('#skF_7','#skF_3') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_229,c_6])).

tff(c_5399,plain,(
    '#skF_7' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5339,c_247])).

tff(c_5440,plain,(
    r2_hidden('#skF_10',k4_zfmisc_1('#skF_6','#skF_3','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5399,c_64])).

tff(c_5545,plain,(
    r2_hidden('#skF_10','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5336,c_5440])).

tff(c_5549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5330,c_5545])).

tff(c_5550,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_5152])).

tff(c_5552,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_5550])).

tff(c_5148,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_300,c_5101])).

tff(c_6076,plain,
    ( k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5552,c_5148])).

tff(c_6077,plain,
    ( k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_6005,c_6076])).

tff(c_6078,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_6077])).

tff(c_6108,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6078,c_395])).

tff(c_6112,plain,(
    ! [A_40,C_42,D_43] : k4_zfmisc_1(A_40,'#skF_7',C_42,D_43) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6078,c_6078,c_50])).

tff(c_6326,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6112,c_99])).

tff(c_6330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6108,c_6326])).

tff(c_6332,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6077])).

tff(c_4779,plain,(
    ! [A_532,D_530,B_529,C_528,E_531] :
      ( m1_subset_1(k10_mcart_1(A_532,B_529,C_528,D_530,E_531),C_528)
      | ~ m1_subset_1(E_531,k4_zfmisc_1(A_532,B_529,C_528,D_530)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4799,plain,(
    ! [C_539,A_540,D_538,E_541,B_542] :
      ( v1_xboole_0(k10_mcart_1(A_540,B_542,C_539,D_538,E_541))
      | ~ v1_xboole_0(C_539)
      | ~ m1_subset_1(E_541,k4_zfmisc_1(A_540,B_542,C_539,D_538)) ) ),
    inference(resolution,[status(thm)],[c_4779,c_30])).

tff(c_4846,plain,
    ( v1_xboole_0(k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_300,c_4799])).

tff(c_4907,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4846])).

tff(c_4848,plain,
    ( v1_xboole_0(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_4799])).

tff(c_4908,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4848])).

tff(c_5551,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5152])).

tff(c_5553,plain,(
    ! [C_621,B_622,E_623,D_620,A_624] :
      ( k9_mcart_1(A_624,B_622,C_621,D_620,E_623) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_623)))
      | ~ m1_subset_1(E_623,k4_zfmisc_1(A_624,B_622,C_621,D_620))
      | k1_xboole_0 = D_620
      | k1_xboole_0 = C_621
      | k1_xboole_0 = B_622
      | k1_xboole_0 = A_624 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_5572,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_5553])).

tff(c_5592,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_5041,c_5551,c_5572])).

tff(c_5602,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5592])).

tff(c_5627,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5602,c_395])).

tff(c_5637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4908,c_5627])).

tff(c_5638,plain,
    ( k1_xboole_0 = '#skF_5'
    | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_5592])).

tff(c_5684,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_5638])).

tff(c_5588,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_300,c_5553])).

tff(c_6476,plain,
    ( k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5684,c_5588])).

tff(c_6477,plain,
    ( k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_6005,c_6332,c_6476])).

tff(c_6478,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_6477])).

tff(c_6513,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6478,c_395])).

tff(c_6523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4907,c_6513])).

tff(c_6525,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_6477])).

tff(c_5231,plain,(
    ! [E_595,B_594,D_592,C_593,A_596] :
      ( k8_mcart_1(A_596,B_594,C_593,D_592,E_595) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_595)))
      | ~ m1_subset_1(E_595,k4_zfmisc_1(A_596,B_594,C_593,D_592))
      | k1_xboole_0 = D_592
      | k1_xboole_0 = C_593
      | k1_xboole_0 = B_594
      | k1_xboole_0 = A_596 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_5250,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_5231])).

tff(c_5270,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_5041,c_5250])).

tff(c_5640,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_5551,c_5270])).

tff(c_5641,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5640])).

tff(c_5666,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5641,c_395])).

tff(c_5676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4908,c_5666])).

tff(c_5677,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_5640])).

tff(c_5679,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_5677])).

tff(c_5266,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_300,c_5231])).

tff(c_6888,plain,
    ( k8_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5679,c_5266])).

tff(c_6889,plain,
    ( k8_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_6005,c_6332,c_6525,c_6888])).

tff(c_6890,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_6889])).

tff(c_6937,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6890,c_395])).

tff(c_6947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6075,c_6937])).

tff(c_6948,plain,(
    k8_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_6889])).

tff(c_40,plain,(
    ! [D_33,A_30,C_32,B_31,E_34] :
      ( m1_subset_1(k8_mcart_1(A_30,B_31,C_32,D_33,E_34),A_30)
      | ~ m1_subset_1(E_34,k4_zfmisc_1(A_30,B_31,C_32,D_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_7150,plain,
    ( m1_subset_1(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6')
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6948,c_40])).

tff(c_7154,plain,(
    m1_subset_1(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_7150])).

tff(c_7156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_323,c_7154])).

tff(c_7158,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_6068])).

tff(c_10,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7174,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_7158,c_10])).

tff(c_46,plain,(
    ! [A_40,B_41,C_42] : k4_zfmisc_1(A_40,B_41,C_42,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_7210,plain,(
    ! [A_40,B_41,C_42] : k4_zfmisc_1(A_40,B_41,C_42,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7174,c_7174,c_46])).

tff(c_7497,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7210,c_99])).

tff(c_7501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7158,c_7497])).

tff(c_7502,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_5677])).

tff(c_7530,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7502,c_395])).

tff(c_7540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5214,c_7530])).

tff(c_7542,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_5213])).

tff(c_7549,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_7542,c_10])).

tff(c_7660,plain,(
    ! [A_813] : k3_xboole_0(A_813,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7549,c_7549,c_8])).

tff(c_68,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_228,plain,(
    r1_tarski('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_205])).

tff(c_239,plain,(
    k3_xboole_0('#skF_9','#skF_5') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_228,c_6])).

tff(c_7676,plain,(
    '#skF_5' = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_7660,c_239])).

tff(c_7711,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7676,c_7542])).

tff(c_7574,plain,(
    ! [A_40,B_41,C_42] : k4_zfmisc_1(A_40,B_41,C_42,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7549,c_7549,c_46])).

tff(c_8111,plain,(
    ! [A_40,B_41,C_42] : k4_zfmisc_1(A_40,B_41,C_42,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7676,c_7676,c_7574])).

tff(c_8114,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8111,c_99])).

tff(c_8118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7711,c_8114])).

tff(c_8120,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_4848])).

tff(c_8124,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8120,c_10])).

tff(c_8141,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8124,c_8124,c_8])).

tff(c_70,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_227,plain,(
    r1_tarski('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_205])).

tff(c_234,plain,(
    k3_xboole_0('#skF_8','#skF_4') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_227,c_6])).

tff(c_8207,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8141,c_234])).

tff(c_8245,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8207,c_4907])).

tff(c_8253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8120,c_8245])).

tff(c_8255,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_4846])).

tff(c_8260,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_8255,c_10])).

tff(c_48,plain,(
    ! [A_40,B_41,D_43] : k4_zfmisc_1(A_40,B_41,k1_xboole_0,D_43) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8275,plain,(
    ! [A_40,B_41,D_43] : k4_zfmisc_1(A_40,B_41,'#skF_8',D_43) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8260,c_8260,c_48])).

tff(c_8888,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8275,c_99])).

tff(c_8892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8255,c_8888])).

tff(c_8893,plain,(
    ! [B_129] : ~ v1_xboole_0(B_129) ),
    inference(splitRight,[status(thm)],[c_444])).

tff(c_8902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8893,c_395])).

tff(c_8904,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_8939,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_8904,c_10])).

tff(c_52,plain,(
    ! [B_41,C_42,D_43] : k4_zfmisc_1(k1_xboole_0,B_41,C_42,D_43) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_8946,plain,(
    ! [B_41,C_42,D_43] : k4_zfmisc_1('#skF_6',B_41,C_42,D_43) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8939,c_8939,c_52])).

tff(c_9009,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8946,c_99])).

tff(c_9013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8904,c_9009])).

tff(c_9015,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_9014,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(k1_tarski(A_9),B_10) = k1_xboole_0
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_9075,plain,(
    ! [B_917] :
      ( k4_xboole_0(k1_xboole_0,B_917) = k1_xboole_0
      | ~ r2_hidden('#skF_1'(k1_xboole_0),B_917) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9014,c_14])).

tff(c_9083,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_9075])).

tff(c_9087,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_9015,c_9083])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( ~ r2_hidden(A_14,B_15)
      | k4_xboole_0(k1_tarski(A_14),B_15) != k1_tarski(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_9048,plain,(
    ! [B_15] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0),B_15)
      | k4_xboole_0(k1_xboole_0,B_15) != k1_tarski('#skF_1'(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9014,c_20])).

tff(c_9092,plain,(
    ! [B_918] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0),B_918)
      | k4_xboole_0(k1_xboole_0,B_918) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9014,c_9048])).

tff(c_9100,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_9092])).

tff(c_9104,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9087,c_9100])).

tff(c_9106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9015,c_9104])).

tff(c_9107,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_9112,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9107,c_10])).

tff(c_9137,plain,(
    ! [B_41,C_42,D_43] : k4_zfmisc_1('#skF_6',B_41,C_42,D_43) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9112,c_9112,c_52])).

tff(c_9212,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9137,c_99])).

tff(c_9216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9107,c_9212])).

tff(c_9217,plain,
    ( ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7')
    | ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_27691,plain,(
    ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_9217])).

tff(c_27762,plain,
    ( ~ m1_subset_1(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_27691])).

tff(c_27774,plain,(
    ~ m1_subset_1(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_27762])).

tff(c_27778,plain,
    ( ~ v1_xboole_0(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'))
    | ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_28,c_27774])).

tff(c_27810,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_27778])).

tff(c_9367,plain,(
    ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_9217])).

tff(c_9373,plain,
    ( ~ m1_subset_1(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9')
    | v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_9367])).

tff(c_9409,plain,(
    ~ m1_subset_1(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_9373])).

tff(c_9414,plain,
    ( ~ v1_xboole_0(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'))
    | ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_28,c_9409])).

tff(c_9415,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_9414])).

tff(c_12110,plain,(
    ! [E_1202,D_1203,A_1200,C_1201,B_1204] :
      ( m1_subset_1(k9_mcart_1(A_1200,B_1204,C_1201,D_1203,E_1202),B_1204)
      | ~ m1_subset_1(E_1202,k4_zfmisc_1(A_1200,B_1204,C_1201,D_1203)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_12140,plain,(
    ! [C_1216,B_1217,A_1218,E_1219,D_1215] :
      ( v1_xboole_0(k9_mcart_1(A_1218,B_1217,C_1216,D_1215,E_1219))
      | ~ v1_xboole_0(B_1217)
      | ~ m1_subset_1(E_1219,k4_zfmisc_1(A_1218,B_1217,C_1216,D_1215)) ) ),
    inference(resolution,[status(thm)],[c_12110,c_30])).

tff(c_12189,plain,
    ( v1_xboole_0(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_12140])).

tff(c_12194,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_12189])).

tff(c_9256,plain,(
    ! [B_934,A_935] :
      ( m1_subset_1(B_934,A_935)
      | ~ r2_hidden(B_934,A_935)
      | v1_xboole_0(A_935) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_9265,plain,
    ( m1_subset_1('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9'))
    | v1_xboole_0(k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_64,c_9256])).

tff(c_9275,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_9265])).

tff(c_12187,plain,
    ( v1_xboole_0(k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_9275,c_12140])).

tff(c_12193,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_12187])).

tff(c_12195,plain,(
    ! [C_1221,B_1222,A_1224,D_1220,E_1223] :
      ( k11_mcart_1(A_1224,B_1222,C_1221,D_1220,E_1223) = k2_mcart_1(E_1223)
      | ~ m1_subset_1(E_1223,k4_zfmisc_1(A_1224,B_1222,C_1221,D_1220))
      | k1_xboole_0 = D_1220
      | k1_xboole_0 = C_1221
      | k1_xboole_0 = B_1222
      | k1_xboole_0 = A_1224 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_12244,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_12195])).

tff(c_12294,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_12244])).

tff(c_9317,plain,(
    ! [A_946,B_947] :
      ( k4_xboole_0(k1_tarski(A_946),B_947) = k1_tarski(A_946)
      | r2_hidden(A_946,B_947) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_9323,plain,(
    ! [A_946,B_947] :
      ( r2_hidden(A_946,B_947)
      | k1_tarski(A_946) != k1_xboole_0
      | r2_hidden(A_946,B_947) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9317,c_12])).

tff(c_9358,plain,(
    ! [A_952,B_953] :
      ( k1_tarski(A_952) != k1_xboole_0
      | r2_hidden(A_952,B_953) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_9323])).

tff(c_9366,plain,(
    ! [B_953,A_952] :
      ( ~ v1_xboole_0(B_953)
      | k1_tarski(A_952) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9358,c_2])).

tff(c_9368,plain,(
    ! [A_952] : k1_tarski(A_952) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9366])).

tff(c_9374,plain,(
    ! [C_955,B_956] :
      ( k3_xboole_0(k2_tarski(C_955,C_955),B_956) = k1_tarski(C_955)
      | ~ r2_hidden(C_955,B_956) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_9381,plain,(
    ! [C_955] :
      ( k1_tarski(C_955) = k1_xboole_0
      | ~ r2_hidden(C_955,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9374,c_8])).

tff(c_9393,plain,(
    ! [C_957] : ~ r2_hidden(C_957,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_9368,c_9381])).

tff(c_9403,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_9393])).

tff(c_12305,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12294,c_9403])).

tff(c_12314,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12294,c_12294,c_8])).

tff(c_9231,plain,(
    k3_xboole_0('#skF_6','#skF_2') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_230,c_6])).

tff(c_12379,plain,(
    '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12314,c_9231])).

tff(c_9218,plain,(
    r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_9243,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_9218,c_2])).

tff(c_12419,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12379,c_9243])).

tff(c_12427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12305,c_12419])).

tff(c_12428,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_12244])).

tff(c_12430,plain,(
    k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_12428])).

tff(c_12446,plain,(
    ~ m1_subset_1(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12430,c_9409])).

tff(c_12242,plain,
    ( k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9275,c_12195])).

tff(c_13212,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_12242])).

tff(c_13239,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13212,c_9403])).

tff(c_13251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9243,c_13239])).

tff(c_13252,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9'
    | k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_12242])).

tff(c_13254,plain,(
    k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_13252])).

tff(c_13258,plain,
    ( m1_subset_1(k2_mcart_1('#skF_10'),'#skF_9')
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13254,c_38])).

tff(c_13262,plain,(
    m1_subset_1(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9275,c_13258])).

tff(c_13264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12446,c_13262])).

tff(c_13265,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_13252])).

tff(c_13267,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_13265])).

tff(c_13348,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13267,c_9403])).

tff(c_13360,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12193,c_13348])).

tff(c_13361,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_13265])).

tff(c_13363,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_13361])).

tff(c_13395,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13363,c_9403])).

tff(c_13407,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9415,c_13395])).

tff(c_13408,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_13361])).

tff(c_13439,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13408,c_9403])).

tff(c_13446,plain,(
    ! [A_40,B_41,D_43] : k4_zfmisc_1(A_40,B_41,'#skF_8',D_43) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13408,c_13408,c_48])).

tff(c_13701,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13446,c_99])).

tff(c_13705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13439,c_13701])).

tff(c_13706,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12428])).

tff(c_13708,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_13706])).

tff(c_13720,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13708,c_9403])).

tff(c_13732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12194,c_13720])).

tff(c_13733,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_13706])).

tff(c_13735,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_13733])).

tff(c_13848,plain,(
    ! [A_1353] : k3_xboole_0(A_1353,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13735,c_13735,c_8])).

tff(c_9222,plain,(
    k3_xboole_0('#skF_9','#skF_5') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_228,c_6])).

tff(c_13864,plain,(
    '#skF_5' = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_13848,c_9222])).

tff(c_13748,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13735,c_9403])).

tff(c_13894,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13864,c_13748])).

tff(c_13911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9415,c_13894])).

tff(c_13912,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_13733])).

tff(c_9390,plain,(
    ! [C_955] : ~ r2_hidden(C_955,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_9368,c_9381])).

tff(c_13986,plain,(
    ! [C_955] : ~ r2_hidden(C_955,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13912,c_9390])).

tff(c_13992,plain,(
    ! [A_40,B_41,D_43] : k4_zfmisc_1(A_40,B_41,'#skF_4',D_43) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13912,c_13912,c_48])).

tff(c_13994,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13912,c_13912,c_8])).

tff(c_14055,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13994,c_234])).

tff(c_14096,plain,(
    r2_hidden('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_4','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14055,c_64])).

tff(c_14197,plain,(
    r2_hidden('#skF_10','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13992,c_14096])).

tff(c_14201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13986,c_14197])).

tff(c_14203,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_12189])).

tff(c_14207,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14203,c_10])).

tff(c_14223,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14207,c_14207,c_8])).

tff(c_9235,plain,(
    k3_xboole_0('#skF_7','#skF_3') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_229,c_6])).

tff(c_14289,plain,(
    '#skF_7' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14223,c_9235])).

tff(c_14327,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14289,c_12193])).

tff(c_14335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14203,c_14327])).

tff(c_14337,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_12187])).

tff(c_14342,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_14337,c_10])).

tff(c_14355,plain,(
    ! [A_40,C_42,D_43] : k4_zfmisc_1(A_40,'#skF_7',C_42,D_43) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14342,c_14342,c_50])).

tff(c_14861,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14355,c_99])).

tff(c_14865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14337,c_14861])).

tff(c_14867,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_9414])).

tff(c_14871,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_14867,c_10])).

tff(c_14908,plain,(
    ! [A_40,B_41,C_42] : k4_zfmisc_1(A_40,B_41,C_42,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14871,c_14871,c_46])).

tff(c_14971,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14908,c_99])).

tff(c_14975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14867,c_14971])).

tff(c_14976,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_9373])).

tff(c_14981,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_14976,c_10])).

tff(c_15018,plain,(
    ! [A_40,B_41,C_42] : k4_zfmisc_1(A_40,B_41,C_42,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14981,c_14981,c_46])).

tff(c_15088,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15018,c_99])).

tff(c_15092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14976,c_15088])).

tff(c_15093,plain,(
    ! [B_953] : ~ v1_xboole_0(B_953) ),
    inference(splitRight,[status(thm)],[c_9366])).

tff(c_15108,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_15093,c_4])).

tff(c_15152,plain,(
    ! [C_1446,B_1447] :
      ( k3_xboole_0(k2_tarski(C_1446,C_1446),B_1447) = k1_tarski(C_1446)
      | ~ r2_hidden(C_1446,B_1447) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_15169,plain,(
    ! [C_1448] :
      ( k1_tarski(C_1448) = k1_xboole_0
      | ~ r2_hidden(C_1448,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15152,c_8])).

tff(c_15183,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_15108,c_15169])).

tff(c_9351,plain,(
    ! [A_946,B_947] :
      ( k1_tarski(A_946) != k1_xboole_0
      | r2_hidden(A_946,B_947) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_9323])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( m1_subset_1(B_17,A_16)
      | ~ r2_hidden(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_15128,plain,(
    ! [B_1444,A_1445] :
      ( m1_subset_1(B_1444,A_1445)
      | ~ r2_hidden(B_1444,A_1445) ) ),
    inference(negUnitSimplification,[status(thm)],[c_15093,c_24])).

tff(c_15210,plain,(
    ! [A_1450,B_1451] :
      ( m1_subset_1(A_1450,B_1451)
      | k1_tarski(A_1450) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9351,c_15128])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_15225,plain,(
    ! [A_1452,B_1453] :
      ( r1_tarski(A_1452,B_1453)
      | k1_tarski(A_1452) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_15210,c_32])).

tff(c_15230,plain,(
    ! [A_1454,B_1455] :
      ( k3_xboole_0(A_1454,B_1455) = A_1454
      | k1_tarski(A_1454) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_15225,c_6])).

tff(c_15284,plain,(
    ! [A_1456] :
      ( k1_xboole_0 = A_1456
      | k1_tarski(A_1456) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15230,c_8])).

tff(c_15288,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_15183,c_15284])).

tff(c_15322,plain,(
    k1_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15288,c_15183])).

tff(c_15372,plain,(
    ! [B_1460] :
      ( k4_xboole_0(k1_xboole_0,B_1460) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,B_1460) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15322,c_14])).

tff(c_15383,plain,(
    ! [B_947] :
      ( k4_xboole_0(k1_xboole_0,B_947) = k1_xboole_0
      | k1_tarski(k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9351,c_15372])).

tff(c_15388,plain,(
    ! [B_947] : k4_xboole_0(k1_xboole_0,B_947) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15322,c_15383])).

tff(c_15339,plain,(
    ! [B_15] :
      ( ~ r2_hidden(k1_xboole_0,B_15)
      | k4_xboole_0(k1_xboole_0,B_15) != k1_tarski(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15322,c_20])).

tff(c_15353,plain,(
    ! [B_15] :
      ( ~ r2_hidden(k1_xboole_0,B_15)
      | k4_xboole_0(k1_xboole_0,B_15) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15322,c_15339])).

tff(c_15424,plain,(
    ! [B_15] : ~ r2_hidden(k1_xboole_0,B_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15388,c_15353])).

tff(c_15329,plain,(
    r2_hidden(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_15288,c_15108])).

tff(c_15426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15424,c_15329])).

tff(c_15428,plain,(
    r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_9217])).

tff(c_15438,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_15428,c_2])).

tff(c_24715,plain,(
    ! [C_2382,A_2381,E_2384,B_2383,D_2380] :
      ( m1_subset_1(k11_mcart_1(A_2381,B_2383,C_2382,D_2380,E_2384),D_2380)
      | ~ m1_subset_1(E_2384,k4_zfmisc_1(A_2381,B_2383,C_2382,D_2380)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24757,plain,(
    ! [C_2399,A_2397,D_2396,E_2395,B_2398] :
      ( v1_xboole_0(k11_mcart_1(A_2397,B_2398,C_2399,D_2396,E_2395))
      | ~ v1_xboole_0(D_2396)
      | ~ m1_subset_1(E_2395,k4_zfmisc_1(A_2397,B_2398,C_2399,D_2396)) ) ),
    inference(resolution,[status(thm)],[c_24715,c_30])).

tff(c_24806,plain,
    ( v1_xboole_0(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_24757])).

tff(c_24810,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_24806])).

tff(c_15427,plain,
    ( ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_9217])).

tff(c_15502,plain,(
    ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_15427])).

tff(c_15509,plain,
    ( ~ m1_subset_1(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_15502])).

tff(c_15536,plain,(
    ~ m1_subset_1(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_15509])).

tff(c_15540,plain,
    ( ~ v1_xboole_0(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_15536])).

tff(c_15541,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_15540])).

tff(c_18985,plain,(
    ! [A_1832,C_1829,B_1830,D_1828,E_1831] :
      ( k11_mcart_1(A_1832,B_1830,C_1829,D_1828,E_1831) = k2_mcart_1(E_1831)
      | ~ m1_subset_1(E_1831,k4_zfmisc_1(A_1832,B_1830,C_1829,D_1828))
      | k1_xboole_0 = D_1828
      | k1_xboole_0 = C_1829
      | k1_xboole_0 = B_1830
      | k1_xboole_0 = A_1832 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_19032,plain,
    ( k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9275,c_18985])).

tff(c_19691,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_19032])).

tff(c_15429,plain,(
    ! [A_952] : k1_tarski(A_952) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_9366])).

tff(c_15439,plain,(
    ! [C_1467,B_1468] :
      ( k3_xboole_0(k2_tarski(C_1467,C_1467),B_1468) = k1_tarski(C_1467)
      | ~ r2_hidden(C_1467,B_1468) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_15446,plain,(
    ! [C_1467] :
      ( k1_tarski(C_1467) = k1_xboole_0
      | ~ r2_hidden(C_1467,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_15439,c_8])).

tff(c_15486,plain,(
    ! [C_1472] : ~ r2_hidden(C_1472,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_15429,c_15446])).

tff(c_15496,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_15486])).

tff(c_19714,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19691,c_15496])).

tff(c_19726,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9243,c_19714])).

tff(c_19728,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_19032])).

tff(c_19034,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_18985])).

tff(c_19082,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_19034])).

tff(c_19097,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19082,c_15496])).

tff(c_19106,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19082,c_19082,c_8])).

tff(c_19171,plain,(
    '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19106,c_9231])).

tff(c_19211,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19171,c_9243])).

tff(c_19219,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19097,c_19211])).

tff(c_19221,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_19034])).

tff(c_19268,plain,(
    ! [E_1860,D_1857,B_1859,A_1861,C_1858] :
      ( k2_mcart_1(k1_mcart_1(E_1860)) = k10_mcart_1(A_1861,B_1859,C_1858,D_1857,E_1860)
      | ~ m1_subset_1(E_1860,k4_zfmisc_1(A_1861,B_1859,C_1858,D_1857))
      | k1_xboole_0 = D_1857
      | k1_xboole_0 = C_1858
      | k1_xboole_0 = B_1859
      | k1_xboole_0 = A_1861 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_19294,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_19268])).

tff(c_19319,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_19221,c_19294])).

tff(c_19357,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_19319])).

tff(c_19377,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19357,c_15496])).

tff(c_19386,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19357,c_19357,c_8])).

tff(c_19445,plain,(
    '#skF_7' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19386,c_9235])).

tff(c_19483,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19445,c_15541])).

tff(c_19493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19377,c_19483])).

tff(c_19494,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_19319])).

tff(c_19496,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_19494])).

tff(c_19315,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9275,c_19268])).

tff(c_20405,plain,
    ( k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19496,c_19315])).

tff(c_20406,plain,
    ( k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_19728,c_20405])).

tff(c_20407,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_20406])).

tff(c_20439,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20407,c_15496])).

tff(c_20451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15541,c_20439])).

tff(c_20453,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_20406])).

tff(c_18852,plain,(
    ! [B_1799,C_1798,D_1800,E_1801,A_1802] :
      ( m1_subset_1(k10_mcart_1(A_1802,B_1799,C_1798,D_1800,E_1801),C_1798)
      | ~ m1_subset_1(E_1801,k4_zfmisc_1(A_1802,B_1799,C_1798,D_1800)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20279,plain,(
    ! [A_1942,B_1940,E_1941,D_1943,C_1939] :
      ( v1_xboole_0(k10_mcart_1(A_1942,B_1940,C_1939,D_1943,E_1941))
      | ~ v1_xboole_0(C_1939)
      | ~ m1_subset_1(E_1941,k4_zfmisc_1(A_1942,B_1940,C_1939,D_1943)) ) ),
    inference(resolution,[status(thm)],[c_18852,c_30])).

tff(c_20326,plain,
    ( v1_xboole_0(k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_9275,c_20279])).

tff(c_20332,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_20326])).

tff(c_19495,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_19319])).

tff(c_19774,plain,(
    ! [D_1903,E_1906,C_1904,A_1907,B_1905] :
      ( k8_mcart_1(A_1907,B_1905,C_1904,D_1903,E_1906) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_1906)))
      | ~ m1_subset_1(E_1906,k4_zfmisc_1(A_1907,B_1905,C_1904,D_1903))
      | k1_xboole_0 = D_1903
      | k1_xboole_0 = C_1904
      | k1_xboole_0 = B_1905
      | k1_xboole_0 = A_1907 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_19793,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_19774])).

tff(c_19815,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_19221,c_19495,c_19793])).

tff(c_19821,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_19815])).

tff(c_19847,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19821,c_15496])).

tff(c_19854,plain,(
    ! [A_40,B_41,D_43] : k4_zfmisc_1(A_40,B_41,'#skF_4',D_43) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19821,c_19821,c_48])).

tff(c_196,plain,
    ( v1_xboole_0('#skF_10')
    | ~ v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_30])).

tff(c_9305,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_20076,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19854,c_9305])).

tff(c_20080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19847,c_20076])).

tff(c_20081,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_19815])).

tff(c_20083,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_20081])).

tff(c_19788,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9275,c_19774])).

tff(c_19811,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_19728,c_19788])).

tff(c_20605,plain,
    ( k8_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20083,c_19811])).

tff(c_20606,plain,
    ( k8_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_20453,c_20605])).

tff(c_20607,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_20606])).

tff(c_20644,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20607,c_15496])).

tff(c_20656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20332,c_20644])).

tff(c_20658,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_20606])).

tff(c_18842,plain,(
    ! [A_1794,C_1795,B_1796,E_1797,D_1793] :
      ( m1_subset_1(k11_mcart_1(A_1794,B_1796,C_1795,D_1793,E_1797),D_1793)
      | ~ m1_subset_1(E_1797,k4_zfmisc_1(A_1794,B_1796,C_1795,D_1793)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18872,plain,(
    ! [C_1810,B_1812,A_1809,D_1811,E_1808] :
      ( v1_xboole_0(k11_mcart_1(A_1809,B_1812,C_1810,D_1811,E_1808))
      | ~ v1_xboole_0(D_1811)
      | ~ m1_subset_1(E_1808,k4_zfmisc_1(A_1809,B_1812,C_1810,D_1811)) ) ),
    inference(resolution,[status(thm)],[c_18842,c_30])).

tff(c_18921,plain,
    ( v1_xboole_0(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_18872])).

tff(c_18925,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_18921])).

tff(c_20082,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_19815])).

tff(c_20183,plain,(
    ! [B_1936,A_1938,E_1937,C_1935,D_1934] :
      ( k9_mcart_1(A_1938,B_1936,C_1935,D_1934,E_1937) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_1937)))
      | ~ m1_subset_1(E_1937,k4_zfmisc_1(A_1938,B_1936,C_1935,D_1934))
      | k1_xboole_0 = D_1934
      | k1_xboole_0 = C_1935
      | k1_xboole_0 = B_1936
      | k1_xboole_0 = A_1938 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_20202,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_20183])).

tff(c_20224,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_19221,c_19495,c_20082,c_20202])).

tff(c_20230,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_20224])).

tff(c_20260,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20230,c_15496])).

tff(c_20272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18925,c_20260])).

tff(c_20273,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_20224])).

tff(c_20197,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9275,c_20183])).

tff(c_20220,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_19728,c_20197])).

tff(c_20824,plain,
    ( k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20273,c_20220])).

tff(c_20825,plain,
    ( k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_20453,c_20658,c_20824])).

tff(c_20826,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_20825])).

tff(c_20870,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20826,c_15496])).

tff(c_20882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15438,c_20870])).

tff(c_20883,plain,(
    k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_20825])).

tff(c_42,plain,(
    ! [A_35,B_36,C_37,D_38,E_39] :
      ( m1_subset_1(k9_mcart_1(A_35,B_36,C_37,D_38,E_39),B_36)
      | ~ m1_subset_1(E_39,k4_zfmisc_1(A_35,B_36,C_37,D_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_21226,plain,
    ( m1_subset_1(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7')
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20883,c_42])).

tff(c_21230,plain,(
    m1_subset_1(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9275,c_21226])).

tff(c_21232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15536,c_21230])).

tff(c_21234,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_20326])).

tff(c_21250,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_21234,c_10])).

tff(c_21288,plain,(
    ! [A_40,B_41,D_43] : k4_zfmisc_1(A_40,B_41,'#skF_8',D_43) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21250,c_21250,c_48])).

tff(c_21588,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21288,c_99])).

tff(c_21592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21234,c_21588])).

tff(c_21594,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_18921])).

tff(c_21598,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_21594,c_10])).

tff(c_21696,plain,(
    ! [A_2085] : k3_xboole_0(A_2085,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21598,c_21598,c_8])).

tff(c_21712,plain,(
    '#skF_5' = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_21696,c_9222])).

tff(c_21742,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21712,c_21594])).

tff(c_21756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15438,c_21742])).

tff(c_21758,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_15540])).

tff(c_21762,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_21758,c_10])).

tff(c_21770,plain,(
    ! [A_40,C_42,D_43] : k4_zfmisc_1(A_40,'#skF_7',C_42,D_43) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21762,c_21762,c_50])).

tff(c_21860,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21770,c_99])).

tff(c_21864,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21758,c_21860])).

tff(c_21865,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_15509])).

tff(c_21870,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_21865,c_10])).

tff(c_21888,plain,(
    ! [A_40,C_42,D_43] : k4_zfmisc_1(A_40,'#skF_7',C_42,D_43) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21870,c_21870,c_50])).

tff(c_21974,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21888,c_99])).

tff(c_21978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21865,c_21974])).

tff(c_21979,plain,(
    ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_15427])).

tff(c_21994,plain,
    ( ~ m1_subset_1(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_26,c_21979])).

tff(c_22006,plain,(
    ~ m1_subset_1(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_21994])).

tff(c_21980,plain,(
    r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_15427])).

tff(c_21988,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_21980,c_2])).

tff(c_24848,plain,(
    ! [B_2410,A_2412,D_2408,C_2409,E_2411] :
      ( k11_mcart_1(A_2412,B_2410,C_2409,D_2408,E_2411) = k2_mcart_1(E_2411)
      | ~ m1_subset_1(E_2411,k4_zfmisc_1(A_2412,B_2410,C_2409,D_2408))
      | k1_xboole_0 = D_2408
      | k1_xboole_0 = C_2409
      | k1_xboole_0 = B_2410
      | k1_xboole_0 = A_2412 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_24895,plain,
    ( k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9275,c_24848])).

tff(c_25672,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_24895])).

tff(c_25695,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25672,c_15496])).

tff(c_25707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9243,c_25695])).

tff(c_25709,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_24895])).

tff(c_24897,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_24848])).

tff(c_24939,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24897])).

tff(c_24952,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24939,c_15496])).

tff(c_24961,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24939,c_24939,c_8])).

tff(c_25026,plain,(
    '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24961,c_9231])).

tff(c_25066,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25026,c_9243])).

tff(c_25074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24952,c_25066])).

tff(c_25076,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24897])).

tff(c_25121,plain,(
    ! [A_2440,E_2439,C_2437,D_2436,B_2438] :
      ( k2_mcart_1(k1_mcart_1(E_2439)) = k10_mcart_1(A_2440,B_2438,C_2437,D_2436,E_2439)
      | ~ m1_subset_1(E_2439,k4_zfmisc_1(A_2440,B_2438,C_2437,D_2436))
      | k1_xboole_0 = D_2436
      | k1_xboole_0 = C_2437
      | k1_xboole_0 = B_2438
      | k1_xboole_0 = A_2440 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_25147,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_25121])).

tff(c_25172,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_25076,c_25147])).

tff(c_25224,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_25172])).

tff(c_25243,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25224,c_15496])).

tff(c_25252,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25224,c_25224,c_8])).

tff(c_25311,plain,(
    '#skF_7' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25252,c_9235])).

tff(c_25350,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25311,c_21988])).

tff(c_25359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25243,c_25350])).

tff(c_25360,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_25172])).

tff(c_25378,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_25360])).

tff(c_25168,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9275,c_25121])).

tff(c_26005,plain,
    ( k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25378,c_25168])).

tff(c_26006,plain,
    ( k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_25709,c_26005])).

tff(c_26007,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_26006])).

tff(c_26034,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26007,c_15496])).

tff(c_26046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21988,c_26034])).

tff(c_26048,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_26006])).

tff(c_22010,plain,
    ( ~ v1_xboole_0(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_28,c_22006])).

tff(c_22032,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_22010])).

tff(c_25361,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_25172])).

tff(c_25772,plain,(
    ! [D_2495,B_2497,E_2498,A_2499,C_2496] :
      ( k9_mcart_1(A_2499,B_2497,C_2496,D_2495,E_2498) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_2498)))
      | ~ m1_subset_1(E_2498,k4_zfmisc_1(A_2499,B_2497,C_2496,D_2495))
      | k1_xboole_0 = D_2495
      | k1_xboole_0 = C_2496
      | k1_xboole_0 = B_2497
      | k1_xboole_0 = A_2499 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_25791,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_25772])).

tff(c_25813,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_25076,c_25361,c_25791])).

tff(c_25819,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_25813])).

tff(c_25845,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25819,c_15496])).

tff(c_25854,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25819,c_25819,c_8])).

tff(c_25952,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25854,c_234])).

tff(c_25991,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25952,c_22032])).

tff(c_26001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25845,c_25991])).

tff(c_26003,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_25813])).

tff(c_26131,plain,(
    ! [B_2524,E_2525,A_2526,C_2523,D_2522] :
      ( k8_mcart_1(A_2526,B_2524,C_2523,D_2522,E_2525) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_2525)))
      | ~ m1_subset_1(E_2525,k4_zfmisc_1(A_2526,B_2524,C_2523,D_2522))
      | k1_xboole_0 = D_2522
      | k1_xboole_0 = C_2523
      | k1_xboole_0 = B_2524
      | k1_xboole_0 = A_2526 ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_26150,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_26131])).

tff(c_26172,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_25076,c_25361,c_26003,c_26150])).

tff(c_26178,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_26172])).

tff(c_26209,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26178,c_15496])).

tff(c_26221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24810,c_26209])).

tff(c_26222,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_26172])).

tff(c_26145,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9275,c_26131])).

tff(c_26168,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_25709,c_26048,c_26145])).

tff(c_26228,plain,
    ( k8_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26222,c_26168])).

tff(c_26229,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_26228])).

tff(c_26261,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26229,c_15496])).

tff(c_26273,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22032,c_26261])).

tff(c_26275,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_26228])).

tff(c_26002,plain,
    ( k1_xboole_0 = '#skF_5'
    | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_25813])).

tff(c_26004,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_26002])).

tff(c_25786,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_9275,c_25772])).

tff(c_25809,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_25709,c_25786])).

tff(c_26358,plain,
    ( k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26004,c_25809])).

tff(c_26359,plain,
    ( k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_26048,c_26275,c_26358])).

tff(c_26360,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_26359])).

tff(c_26394,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26360,c_15496])).

tff(c_26406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15438,c_26394])).

tff(c_26408,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_26359])).

tff(c_26047,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9'
    | k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_26006])).

tff(c_26560,plain,(
    k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_26408,c_26275,c_26047])).

tff(c_36,plain,(
    ! [C_22,D_23,A_20,B_21,E_24] :
      ( m1_subset_1(k10_mcart_1(A_20,B_21,C_22,D_23,E_24),C_22)
      | ~ m1_subset_1(E_24,k4_zfmisc_1(A_20,B_21,C_22,D_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26564,plain,
    ( m1_subset_1(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26560,c_36])).

tff(c_26568,plain,(
    m1_subset_1(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9275,c_26564])).

tff(c_26570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22006,c_26568])).

tff(c_26571,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_25360])).

tff(c_26573,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26571])).

tff(c_26594,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26573,c_15496])).

tff(c_26603,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26573,c_26573,c_8])).

tff(c_26684,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26603,c_234])).

tff(c_26722,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26684,c_22032])).

tff(c_26732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26594,c_26722])).

tff(c_26733,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_26571])).

tff(c_26802,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26733,c_15496])).

tff(c_26814,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24810,c_26802])).

tff(c_26816,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_24806])).

tff(c_26820,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_26816,c_10])).

tff(c_26865,plain,(
    ! [A_2572] : k3_xboole_0(A_2572,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26820,c_26820,c_8])).

tff(c_26881,plain,(
    '#skF_5' = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_26865,c_9222])).

tff(c_26954,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26881,c_26816])).

tff(c_26970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15438,c_26954])).

tff(c_26972,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_22010])).

tff(c_26976,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_26972,c_10])).

tff(c_26985,plain,(
    ! [A_40,B_41,D_43] : k4_zfmisc_1(A_40,B_41,'#skF_8',D_43) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26976,c_26976,c_48])).

tff(c_27074,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26985,c_99])).

tff(c_27078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26972,c_27074])).

tff(c_27079,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_21994])).

tff(c_27084,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_27079,c_10])).

tff(c_27098,plain,(
    ! [A_40,B_41,D_43] : k4_zfmisc_1(A_40,B_41,'#skF_8',D_43) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27084,c_27084,c_48])).

tff(c_27221,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27098,c_99])).

tff(c_27225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27079,c_27221])).

tff(c_27226,plain,(
    ! [B_953] : ~ v1_xboole_0(B_953) ),
    inference(splitRight,[status(thm)],[c_9366])).

tff(c_27233,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_27226,c_4])).

tff(c_27336,plain,(
    ! [C_2625,B_2626] :
      ( k3_xboole_0(k2_tarski(C_2625,C_2625),B_2626) = k1_tarski(C_2625)
      | ~ r2_hidden(C_2625,B_2626) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_27360,plain,(
    ! [C_2627] :
      ( k1_tarski(C_2627) = k1_xboole_0
      | ~ r2_hidden(C_2627,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27336,c_8])).

tff(c_27374,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27233,c_27360])).

tff(c_27249,plain,(
    ! [B_2616,A_2617] :
      ( m1_subset_1(B_2616,A_2617)
      | ~ r2_hidden(B_2616,A_2617) ) ),
    inference(negUnitSimplification,[status(thm)],[c_27226,c_24])).

tff(c_27277,plain,(
    ! [A_2618,B_2619] :
      ( m1_subset_1(A_2618,B_2619)
      | k1_tarski(A_2618) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_9351,c_27249])).

tff(c_27283,plain,(
    ! [A_2620,B_2621] :
      ( r1_tarski(A_2620,B_2621)
      | k1_tarski(A_2620) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_27277,c_32])).

tff(c_27288,plain,(
    ! [A_2622,B_2623] :
      ( k3_xboole_0(A_2622,B_2623) = A_2622
      | k1_tarski(A_2622) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_27283,c_6])).

tff(c_27306,plain,(
    ! [A_2622] :
      ( k1_xboole_0 = A_2622
      | k1_tarski(A_2622) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27288,c_8])).

tff(c_27394,plain,(
    '#skF_1'(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_27374,c_27306])).

tff(c_27398,plain,(
    k1_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27394,c_27374])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(k1_tarski(A_14),B_15) = k1_tarski(A_14)
      | r2_hidden(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_27419,plain,(
    ! [B_15] :
      ( k4_xboole_0(k1_xboole_0,B_15) = k1_tarski(k1_xboole_0)
      | r2_hidden(k1_xboole_0,B_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27398,c_22])).

tff(c_27431,plain,(
    ! [B_15] :
      ( k4_xboole_0(k1_xboole_0,B_15) = k1_xboole_0
      | r2_hidden(k1_xboole_0,B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27398,c_27419])).

tff(c_27490,plain,(
    ! [B_2631] :
      ( k4_xboole_0(k1_xboole_0,B_2631) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,B_2631) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27398,c_14])).

tff(c_27509,plain,(
    ! [B_15] : k4_xboole_0(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27431,c_27490])).

tff(c_27422,plain,(
    ! [B_10] :
      ( r2_hidden(k1_xboole_0,B_10)
      | k4_xboole_0(k1_xboole_0,B_10) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27398,c_12])).

tff(c_27517,plain,(
    ! [B_10] : r2_hidden(k1_xboole_0,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27509,c_27422])).

tff(c_27416,plain,(
    ! [B_15] :
      ( ~ r2_hidden(k1_xboole_0,B_15)
      | k4_xboole_0(k1_xboole_0,B_15) != k1_tarski(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27398,c_20])).

tff(c_27430,plain,(
    ! [B_15] :
      ( ~ r2_hidden(k1_xboole_0,B_15)
      | k4_xboole_0(k1_xboole_0,B_15) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27398,c_27416])).

tff(c_27624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27509,c_27517,c_27430])).

tff(c_27626,plain,(
    v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_27625,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_27630,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_27625,c_10])).

tff(c_27638,plain,(
    ! [A_8] :
      ( A_8 = '#skF_10'
      | ~ v1_xboole_0(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27630,c_10])).

tff(c_27668,plain,(
    k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_27626,c_27638])).

tff(c_44,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( k4_zfmisc_1(A_40,B_41,C_42,D_43) != k1_xboole_0
      | k1_xboole_0 = D_43
      | k1_xboole_0 = C_42
      | k1_xboole_0 = B_41
      | k1_xboole_0 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_27923,plain,(
    ! [A_2679,B_2680,C_2681,D_2682] :
      ( k4_zfmisc_1(A_2679,B_2680,C_2681,D_2682) != '#skF_10'
      | D_2682 = '#skF_10'
      | C_2681 = '#skF_10'
      | B_2680 = '#skF_10'
      | A_2679 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27630,c_27630,c_27630,c_27630,c_27630,c_44])).

tff(c_27939,plain,
    ( '#skF_10' = '#skF_5'
    | '#skF_10' = '#skF_4'
    | '#skF_10' = '#skF_3'
    | '#skF_10' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_27668,c_27923])).

tff(c_27948,plain,(
    '#skF_10' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_27939])).

tff(c_27966,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27948,c_27625])).

tff(c_27637,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27630,c_27630,c_8])).

tff(c_27964,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27948,c_27948,c_27637])).

tff(c_28024,plain,(
    '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27964,c_9231])).

tff(c_28053,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28024,c_9243])).

tff(c_28059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_27966,c_28053])).

tff(c_28060,plain,
    ( '#skF_10' = '#skF_3'
    | '#skF_10' = '#skF_4'
    | '#skF_10' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_27939])).

tff(c_28062,plain,(
    '#skF_10' = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_28060])).

tff(c_28139,plain,(
    ! [A_2700] : k3_xboole_0(A_2700,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28062,c_28062,c_27637])).

tff(c_28151,plain,(
    '#skF_5' = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_28139,c_9222])).

tff(c_28081,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28062,c_27625])).

tff(c_28176,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28151,c_28081])).

tff(c_28185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_27810,c_28176])).

tff(c_28186,plain,
    ( '#skF_10' = '#skF_4'
    | '#skF_10' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28060])).

tff(c_28198,plain,(
    '#skF_10' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_28186])).

tff(c_28218,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28198,c_27625])).

tff(c_27634,plain,(
    ! [A_40,C_42,D_43] : k4_zfmisc_1(A_40,'#skF_10',C_42,D_43) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27630,c_27630,c_50])).

tff(c_28212,plain,(
    ! [A_40,C_42,D_43] : k4_zfmisc_1(A_40,'#skF_3',C_42,D_43) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28198,c_28198,c_27634])).

tff(c_28216,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28198,c_28198,c_27637])).

tff(c_28276,plain,(
    '#skF_7' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28216,c_9235])).

tff(c_28312,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_6','#skF_3','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28276,c_99])).

tff(c_28350,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28212,c_28312])).

tff(c_28353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28218,c_28350])).

tff(c_28354,plain,(
    '#skF_10' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_28186])).

tff(c_27784,plain,(
    ! [A_2663,B_2664] :
      ( r2_hidden(A_2663,B_2664)
      | k4_xboole_0(k1_tarski(A_2663),B_2664) != '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27630,c_12])).

tff(c_27787,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | k1_tarski(A_14) != '#skF_10'
      | r2_hidden(A_14,B_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_27784])).

tff(c_27888,plain,(
    ! [A_2675,B_2676] :
      ( k1_tarski(A_2675) != '#skF_10'
      | r2_hidden(A_2675,B_2676) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_27787])).

tff(c_27905,plain,(
    ! [B_2676,A_2675] :
      ( ~ v1_xboole_0(B_2676)
      | k1_tarski(A_2675) != '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_27888,c_2])).

tff(c_27906,plain,(
    ! [A_2675] : k1_tarski(A_2675) != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_27905])).

tff(c_27811,plain,(
    ! [C_2667,B_2668] :
      ( k3_xboole_0(k2_tarski(C_2667,C_2667),B_2668) = k1_tarski(C_2667)
      | ~ r2_hidden(C_2667,B_2668) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_27825,plain,(
    ! [C_2667] :
      ( k1_tarski(C_2667) = '#skF_10'
      | ~ r2_hidden(C_2667,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27637,c_27811])).

tff(c_27907,plain,(
    ! [C_2667] : ~ r2_hidden(C_2667,'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_27906,c_27825])).

tff(c_28360,plain,(
    ! [C_2667] : ~ r2_hidden(C_2667,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28354,c_27907])).

tff(c_27635,plain,(
    ! [A_40,B_41,D_43] : k4_zfmisc_1(A_40,B_41,'#skF_10',D_43) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27630,c_27630,c_48])).

tff(c_28372,plain,(
    ! [A_40,B_41,D_43] : k4_zfmisc_1(A_40,B_41,'#skF_4',D_43) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28354,c_28354,c_27635])).

tff(c_28374,plain,(
    ! [A_7] : k3_xboole_0(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28354,c_28354,c_27637])).

tff(c_28439,plain,(
    '#skF_8' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28374,c_234])).

tff(c_28379,plain,(
    r2_hidden('#skF_4',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28354,c_64])).

tff(c_28468,plain,(
    r2_hidden('#skF_4',k4_zfmisc_1('#skF_6','#skF_7','#skF_4','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28439,c_28379])).

tff(c_28537,plain,(
    r2_hidden('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28372,c_28468])).

tff(c_28541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28360,c_28537])).

tff(c_28542,plain,(
    ! [B_2676] : ~ v1_xboole_0(B_2676) ),
    inference(splitRight,[status(thm)],[c_27905])).

tff(c_28551,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28542,c_27625])).

tff(c_28553,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_27778])).

tff(c_28557,plain,(
    '#skF_10' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_28553,c_27638])).

tff(c_27636,plain,(
    ! [A_40,B_41,C_42] : k4_zfmisc_1(A_40,B_41,C_42,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_27630,c_27630,c_46])).

tff(c_28567,plain,(
    ! [A_40,B_41,C_42] : k4_zfmisc_1(A_40,B_41,C_42,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28557,c_28557,c_27636])).

tff(c_28707,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28567,c_99])).

tff(c_28710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28553,c_28707])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:13:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.08/8.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.36/8.17  
% 17.36/8.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.36/8.17  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4
% 17.36/8.17  
% 17.36/8.17  %Foreground sorts:
% 17.36/8.17  
% 17.36/8.17  
% 17.36/8.17  %Background operators:
% 17.36/8.17  
% 17.36/8.17  
% 17.36/8.17  %Foreground operators:
% 17.36/8.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.36/8.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.36/8.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.36/8.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.36/8.17  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 17.36/8.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 17.36/8.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.36/8.17  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 17.36/8.17  tff('#skF_7', type, '#skF_7': $i).
% 17.36/8.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.36/8.17  tff('#skF_10', type, '#skF_10': $i).
% 17.36/8.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.36/8.17  tff('#skF_5', type, '#skF_5': $i).
% 17.36/8.17  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 17.36/8.17  tff('#skF_6', type, '#skF_6': $i).
% 17.36/8.17  tff('#skF_2', type, '#skF_2': $i).
% 17.36/8.17  tff('#skF_3', type, '#skF_3': $i).
% 17.36/8.17  tff('#skF_9', type, '#skF_9': $i).
% 17.36/8.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.36/8.17  tff('#skF_8', type, '#skF_8': $i).
% 17.36/8.17  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 17.36/8.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.36/8.17  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 17.36/8.17  tff('#skF_4', type, '#skF_4': $i).
% 17.36/8.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.36/8.17  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 17.36/8.17  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 17.36/8.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.36/8.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.36/8.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.36/8.17  
% 17.56/8.22  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 17.56/8.22  tff(f_157, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(A)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(B)) => (![G]: (m1_subset_1(G, k1_zfmisc_1(C)) => (![H]: (m1_subset_1(H, k1_zfmisc_1(D)) => (![I]: (m1_subset_1(I, k4_zfmisc_1(A, B, C, D)) => (r2_hidden(I, k4_zfmisc_1(E, F, G, H)) => (((r2_hidden(k8_mcart_1(A, B, C, D, I), E) & r2_hidden(k9_mcart_1(A, B, C, D, I), F)) & r2_hidden(k10_mcart_1(A, B, C, D, I), G)) & r2_hidden(k11_mcart_1(A, B, C, D, I), H))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_mcart_1)).
% 17.56/8.22  tff(f_132, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 17.56/8.22  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 17.56/8.22  tff(f_54, axiom, (![A, B, C]: (r2_hidden(A, B) => ((r2_hidden(C, B) & ~(A = C)) | (k3_xboole_0(k2_tarski(A, C), B) = k1_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_zfmisc_1)).
% 17.56/8.22  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 17.56/8.22  tff(f_76, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 17.56/8.22  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 17.56/8.22  tff(f_84, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k11_mcart_1(A, B, C, D, E), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_mcart_1)).
% 17.56/8.22  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 17.56/8.22  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 17.56/8.22  tff(f_107, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 17.56/8.22  tff(f_80, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k10_mcart_1(A, B, C, D, E), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_mcart_1)).
% 17.56/8.22  tff(f_88, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k8_mcart_1(A, B, C, D, E), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_mcart_1)).
% 17.56/8.22  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 17.56/8.22  tff(f_92, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k9_mcart_1(A, B, C, D, E), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_mcart_1)).
% 17.56/8.22  tff(c_28, plain, (![B_17, A_16]: (m1_subset_1(B_17, A_16) | ~v1_xboole_0(B_17) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.56/8.22  tff(c_26, plain, (![B_17, A_16]: (r2_hidden(B_17, A_16) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.56/8.22  tff(c_66, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.56/8.22  tff(c_4852, plain, (![C_544, D_543, A_547, E_546, B_545]: (k11_mcart_1(A_547, B_545, C_544, D_543, E_546)=k2_mcart_1(E_546) | ~m1_subset_1(E_546, k4_zfmisc_1(A_547, B_545, C_544, D_543)) | k1_xboole_0=D_543 | k1_xboole_0=C_544 | k1_xboole_0=B_545 | k1_xboole_0=A_547)), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.56/8.22  tff(c_4901, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_66, c_4852])).
% 17.56/8.22  tff(c_4909, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4901])).
% 17.56/8.22  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.56/8.22  tff(c_367, plain, (![C_123, B_124]: (k3_xboole_0(k2_tarski(C_123, C_123), B_124)=k1_tarski(C_123) | ~r2_hidden(C_123, B_124))), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.56/8.22  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.56/8.22  tff(c_384, plain, (![C_125]: (k1_tarski(C_125)=k1_xboole_0 | ~r2_hidden(C_125, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_367, c_8])).
% 17.56/8.22  tff(c_394, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_384])).
% 17.56/8.22  tff(c_395, plain, (v1_xboole_0(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_394])).
% 17.56/8.22  tff(c_4919, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4909, c_395])).
% 17.56/8.22  tff(c_4926, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4909, c_4909, c_8])).
% 17.56/8.22  tff(c_74, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.56/8.22  tff(c_205, plain, (![A_101, B_102]: (r1_tarski(A_101, B_102) | ~m1_subset_1(A_101, k1_zfmisc_1(B_102)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 17.56/8.22  tff(c_230, plain, (r1_tarski('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_74, c_205])).
% 17.56/8.22  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.56/8.22  tff(c_243, plain, (k3_xboole_0('#skF_6', '#skF_2')='#skF_6'), inference(resolution, [status(thm)], [c_230, c_6])).
% 17.56/8.22  tff(c_4991, plain, ('#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4926, c_243])).
% 17.56/8.22  tff(c_62, plain, (~r2_hidden(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9') | ~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8') | ~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7') | ~r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.56/8.22  tff(c_235, plain, (~r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(splitLeft, [status(thm)], [c_62])).
% 17.56/8.22  tff(c_281, plain, (~m1_subset_1(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_26, c_235])).
% 17.56/8.22  tff(c_323, plain, (~m1_subset_1(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(splitLeft, [status(thm)], [c_281])).
% 17.56/8.22  tff(c_327, plain, (~v1_xboole_0(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_28, c_323])).
% 17.56/8.22  tff(c_396, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_327])).
% 17.56/8.22  tff(c_5029, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4991, c_396])).
% 17.56/8.22  tff(c_5039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4919, c_5029])).
% 17.56/8.22  tff(c_5040, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_4901])).
% 17.56/8.22  tff(c_5200, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_5040])).
% 17.56/8.22  tff(c_38, plain, (![A_25, E_29, C_27, D_28, B_26]: (m1_subset_1(k11_mcart_1(A_25, B_26, C_27, D_28, E_29), D_28) | ~m1_subset_1(E_29, k4_zfmisc_1(A_25, B_26, C_27, D_28)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 17.56/8.22  tff(c_5204, plain, (m1_subset_1(k2_mcart_1('#skF_10'), '#skF_5') | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5200, c_38])).
% 17.56/8.22  tff(c_5208, plain, (m1_subset_1(k2_mcart_1('#skF_10'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5204])).
% 17.56/8.22  tff(c_30, plain, (![B_17, A_16]: (v1_xboole_0(B_17) | ~m1_subset_1(B_17, A_16) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.56/8.22  tff(c_5213, plain, (v1_xboole_0(k2_mcart_1('#skF_10')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_5208, c_30])).
% 17.56/8.22  tff(c_5214, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_5213])).
% 17.56/8.22  tff(c_64, plain, (r2_hidden('#skF_10', k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.56/8.22  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 17.56/8.22  tff(c_99, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_64, c_2])).
% 17.56/8.22  tff(c_287, plain, (![B_109, A_110]: (m1_subset_1(B_109, A_110) | ~r2_hidden(B_109, A_110) | v1_xboole_0(A_110))), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.56/8.22  tff(c_293, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')) | v1_xboole_0(k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_64, c_287])).
% 17.56/8.22  tff(c_300, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_99, c_293])).
% 17.56/8.22  tff(c_4899, plain, (k11_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_300, c_4852])).
% 17.56/8.22  tff(c_5964, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_4899])).
% 17.56/8.22  tff(c_5993, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5964, c_395])).
% 17.56/8.22  tff(c_6003, plain, $false, inference(negUnitSimplification, [status(thm)], [c_396, c_5993])).
% 17.56/8.22  tff(c_6004, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9' | k11_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_4899])).
% 17.56/8.22  tff(c_6006, plain, (k11_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_6004])).
% 17.56/8.22  tff(c_4766, plain, (![B_526, C_525, E_527, D_523, A_524]: (m1_subset_1(k11_mcart_1(A_524, B_526, C_525, D_523, E_527), D_523) | ~m1_subset_1(E_527, k4_zfmisc_1(A_524, B_526, C_525, D_523)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 17.56/8.22  tff(c_6020, plain, (![E_654, B_652, C_653, A_651, D_650]: (v1_xboole_0(k11_mcart_1(A_651, B_652, C_653, D_650, E_654)) | ~v1_xboole_0(D_650) | ~m1_subset_1(E_654, k4_zfmisc_1(A_651, B_652, C_653, D_650)))), inference(resolution, [status(thm)], [c_4766, c_30])).
% 17.56/8.22  tff(c_6039, plain, (v1_xboole_0(k11_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')) | ~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_300, c_6020])).
% 17.56/8.22  tff(c_6068, plain, (v1_xboole_0(k2_mcart_1('#skF_10')) | ~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6006, c_6039])).
% 17.56/8.22  tff(c_6075, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_6068])).
% 17.56/8.22  tff(c_6005, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_4899])).
% 17.56/8.22  tff(c_5041, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_4901])).
% 17.56/8.22  tff(c_5101, plain, (![C_572, D_571, B_573, E_574, A_575]: (k2_mcart_1(k1_mcart_1(E_574))=k10_mcart_1(A_575, B_573, C_572, D_571, E_574) | ~m1_subset_1(E_574, k4_zfmisc_1(A_575, B_573, C_572, D_571)) | k1_xboole_0=D_571 | k1_xboole_0=C_572 | k1_xboole_0=B_573 | k1_xboole_0=A_575)), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.56/8.22  tff(c_5127, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_66, c_5101])).
% 17.56/8.22  tff(c_5152, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_5041, c_5127])).
% 17.56/8.22  tff(c_5308, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5152])).
% 17.56/8.22  tff(c_333, plain, (![A_119, B_120]: (k4_xboole_0(k1_tarski(A_119), B_120)=k1_tarski(A_119) | r2_hidden(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.56/8.22  tff(c_12, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | k4_xboole_0(k1_tarski(A_9), B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.56/8.22  tff(c_342, plain, (![A_119, B_120]: (r2_hidden(A_119, B_120) | k1_tarski(A_119)!=k1_xboole_0 | r2_hidden(A_119, B_120))), inference(superposition, [status(thm), theory('equality')], [c_333, c_12])).
% 17.56/8.22  tff(c_424, plain, (![A_128, B_129]: (k1_tarski(A_128)!=k1_xboole_0 | r2_hidden(A_128, B_129))), inference(factorization, [status(thm), theory('equality')], [c_342])).
% 17.56/8.22  tff(c_444, plain, (![B_129, A_128]: (~v1_xboole_0(B_129) | k1_tarski(A_128)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_424, c_2])).
% 17.56/8.22  tff(c_471, plain, (![A_128]: (k1_tarski(A_128)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_444])).
% 17.56/8.22  tff(c_374, plain, (![C_123]: (k1_tarski(C_123)=k1_xboole_0 | ~r2_hidden(C_123, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_367, c_8])).
% 17.56/8.22  tff(c_472, plain, (![C_123]: (~r2_hidden(C_123, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_471, c_374])).
% 17.56/8.22  tff(c_5330, plain, (![C_123]: (~r2_hidden(C_123, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5308, c_472])).
% 17.56/8.22  tff(c_50, plain, (![A_40, C_42, D_43]: (k4_zfmisc_1(A_40, k1_xboole_0, C_42, D_43)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_107])).
% 17.56/8.22  tff(c_5336, plain, (![A_40, C_42, D_43]: (k4_zfmisc_1(A_40, '#skF_3', C_42, D_43)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5308, c_5308, c_50])).
% 17.56/8.22  tff(c_5339, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5308, c_5308, c_8])).
% 17.56/8.22  tff(c_72, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.56/8.22  tff(c_229, plain, (r1_tarski('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_72, c_205])).
% 17.56/8.22  tff(c_247, plain, (k3_xboole_0('#skF_7', '#skF_3')='#skF_7'), inference(resolution, [status(thm)], [c_229, c_6])).
% 17.56/8.22  tff(c_5399, plain, ('#skF_7'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5339, c_247])).
% 17.56/8.22  tff(c_5440, plain, (r2_hidden('#skF_10', k4_zfmisc_1('#skF_6', '#skF_3', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_5399, c_64])).
% 17.56/8.22  tff(c_5545, plain, (r2_hidden('#skF_10', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5336, c_5440])).
% 17.56/8.22  tff(c_5549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5330, c_5545])).
% 17.56/8.22  tff(c_5550, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_5152])).
% 17.56/8.22  tff(c_5552, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitLeft, [status(thm)], [c_5550])).
% 17.56/8.22  tff(c_5148, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_300, c_5101])).
% 17.56/8.22  tff(c_6076, plain, (k10_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5552, c_5148])).
% 17.56/8.22  tff(c_6077, plain, (k10_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_6005, c_6076])).
% 17.56/8.22  tff(c_6078, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_6077])).
% 17.56/8.22  tff(c_6108, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6078, c_395])).
% 17.56/8.22  tff(c_6112, plain, (![A_40, C_42, D_43]: (k4_zfmisc_1(A_40, '#skF_7', C_42, D_43)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6078, c_6078, c_50])).
% 17.56/8.22  tff(c_6326, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6112, c_99])).
% 17.56/8.22  tff(c_6330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6108, c_6326])).
% 17.56/8.22  tff(c_6332, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_6077])).
% 17.56/8.22  tff(c_4779, plain, (![A_532, D_530, B_529, C_528, E_531]: (m1_subset_1(k10_mcart_1(A_532, B_529, C_528, D_530, E_531), C_528) | ~m1_subset_1(E_531, k4_zfmisc_1(A_532, B_529, C_528, D_530)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 17.56/8.22  tff(c_4799, plain, (![C_539, A_540, D_538, E_541, B_542]: (v1_xboole_0(k10_mcart_1(A_540, B_542, C_539, D_538, E_541)) | ~v1_xboole_0(C_539) | ~m1_subset_1(E_541, k4_zfmisc_1(A_540, B_542, C_539, D_538)))), inference(resolution, [status(thm)], [c_4779, c_30])).
% 17.56/8.22  tff(c_4846, plain, (v1_xboole_0(k10_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')) | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_300, c_4799])).
% 17.56/8.22  tff(c_4907, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_4846])).
% 17.56/8.22  tff(c_4848, plain, (v1_xboole_0(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_66, c_4799])).
% 17.56/8.22  tff(c_4908, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_4848])).
% 17.56/8.22  tff(c_5551, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_5152])).
% 17.56/8.22  tff(c_5553, plain, (![C_621, B_622, E_623, D_620, A_624]: (k9_mcart_1(A_624, B_622, C_621, D_620, E_623)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_623))) | ~m1_subset_1(E_623, k4_zfmisc_1(A_624, B_622, C_621, D_620)) | k1_xboole_0=D_620 | k1_xboole_0=C_621 | k1_xboole_0=B_622 | k1_xboole_0=A_624)), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.56/8.22  tff(c_5572, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_66, c_5553])).
% 17.56/8.22  tff(c_5592, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_5041, c_5551, c_5572])).
% 17.56/8.22  tff(c_5602, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_5592])).
% 17.56/8.22  tff(c_5627, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5602, c_395])).
% 17.56/8.22  tff(c_5637, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4908, c_5627])).
% 17.56/8.22  tff(c_5638, plain, (k1_xboole_0='#skF_5' | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_5592])).
% 17.56/8.22  tff(c_5684, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitLeft, [status(thm)], [c_5638])).
% 17.56/8.22  tff(c_5588, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_300, c_5553])).
% 17.56/8.22  tff(c_6476, plain, (k9_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5684, c_5588])).
% 17.56/8.22  tff(c_6477, plain, (k9_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_6005, c_6332, c_6476])).
% 17.56/8.22  tff(c_6478, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_6477])).
% 17.56/8.22  tff(c_6513, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6478, c_395])).
% 17.56/8.22  tff(c_6523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4907, c_6513])).
% 17.56/8.22  tff(c_6525, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_6477])).
% 17.56/8.22  tff(c_5231, plain, (![E_595, B_594, D_592, C_593, A_596]: (k8_mcart_1(A_596, B_594, C_593, D_592, E_595)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_595))) | ~m1_subset_1(E_595, k4_zfmisc_1(A_596, B_594, C_593, D_592)) | k1_xboole_0=D_592 | k1_xboole_0=C_593 | k1_xboole_0=B_594 | k1_xboole_0=A_596)), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.56/8.22  tff(c_5250, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_66, c_5231])).
% 17.56/8.22  tff(c_5270, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_5041, c_5250])).
% 17.56/8.22  tff(c_5640, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_5551, c_5270])).
% 17.56/8.22  tff(c_5641, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_5640])).
% 17.56/8.22  tff(c_5666, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5641, c_395])).
% 17.56/8.22  tff(c_5676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4908, c_5666])).
% 17.56/8.22  tff(c_5677, plain, (k1_xboole_0='#skF_5' | k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_5640])).
% 17.56/8.22  tff(c_5679, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitLeft, [status(thm)], [c_5677])).
% 17.56/8.22  tff(c_5266, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_300, c_5231])).
% 17.56/8.22  tff(c_6888, plain, (k8_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5679, c_5266])).
% 17.56/8.22  tff(c_6889, plain, (k8_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_6005, c_6332, c_6525, c_6888])).
% 17.56/8.22  tff(c_6890, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_6889])).
% 17.56/8.22  tff(c_6937, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_6890, c_395])).
% 17.56/8.22  tff(c_6947, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6075, c_6937])).
% 17.56/8.22  tff(c_6948, plain, (k8_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_6889])).
% 17.56/8.22  tff(c_40, plain, (![D_33, A_30, C_32, B_31, E_34]: (m1_subset_1(k8_mcart_1(A_30, B_31, C_32, D_33, E_34), A_30) | ~m1_subset_1(E_34, k4_zfmisc_1(A_30, B_31, C_32, D_33)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 17.56/8.22  tff(c_7150, plain, (m1_subset_1(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6') | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_6948, c_40])).
% 17.56/8.22  tff(c_7154, plain, (m1_subset_1(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_7150])).
% 17.56/8.22  tff(c_7156, plain, $false, inference(negUnitSimplification, [status(thm)], [c_323, c_7154])).
% 17.56/8.22  tff(c_7158, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_6068])).
% 17.56/8.22  tff(c_10, plain, (![A_8]: (k1_xboole_0=A_8 | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 17.56/8.22  tff(c_7174, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_7158, c_10])).
% 17.56/8.22  tff(c_46, plain, (![A_40, B_41, C_42]: (k4_zfmisc_1(A_40, B_41, C_42, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_107])).
% 17.56/8.22  tff(c_7210, plain, (![A_40, B_41, C_42]: (k4_zfmisc_1(A_40, B_41, C_42, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_7174, c_7174, c_46])).
% 17.56/8.22  tff(c_7497, plain, (~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_7210, c_99])).
% 17.56/8.22  tff(c_7501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7158, c_7497])).
% 17.56/8.22  tff(c_7502, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_5677])).
% 17.56/8.22  tff(c_7530, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7502, c_395])).
% 17.56/8.22  tff(c_7540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5214, c_7530])).
% 17.56/8.22  tff(c_7542, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_5213])).
% 17.56/8.22  tff(c_7549, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_7542, c_10])).
% 17.56/8.22  tff(c_7660, plain, (![A_813]: (k3_xboole_0(A_813, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7549, c_7549, c_8])).
% 17.56/8.22  tff(c_68, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.56/8.22  tff(c_228, plain, (r1_tarski('#skF_9', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_205])).
% 17.56/8.22  tff(c_239, plain, (k3_xboole_0('#skF_9', '#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_228, c_6])).
% 17.56/8.22  tff(c_7676, plain, ('#skF_5'='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_7660, c_239])).
% 17.56/8.22  tff(c_7711, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_7676, c_7542])).
% 17.56/8.22  tff(c_7574, plain, (![A_40, B_41, C_42]: (k4_zfmisc_1(A_40, B_41, C_42, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7549, c_7549, c_46])).
% 17.56/8.22  tff(c_8111, plain, (![A_40, B_41, C_42]: (k4_zfmisc_1(A_40, B_41, C_42, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_7676, c_7676, c_7574])).
% 17.56/8.22  tff(c_8114, plain, (~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_8111, c_99])).
% 17.56/8.22  tff(c_8118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7711, c_8114])).
% 17.56/8.22  tff(c_8120, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_4848])).
% 17.56/8.22  tff(c_8124, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8120, c_10])).
% 17.56/8.22  tff(c_8141, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8124, c_8124, c_8])).
% 17.56/8.22  tff(c_70, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 17.56/8.22  tff(c_227, plain, (r1_tarski('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_205])).
% 17.56/8.22  tff(c_234, plain, (k3_xboole_0('#skF_8', '#skF_4')='#skF_8'), inference(resolution, [status(thm)], [c_227, c_6])).
% 17.56/8.22  tff(c_8207, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8141, c_234])).
% 17.56/8.22  tff(c_8245, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8207, c_4907])).
% 17.56/8.22  tff(c_8253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8120, c_8245])).
% 17.56/8.22  tff(c_8255, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_4846])).
% 17.56/8.22  tff(c_8260, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_8255, c_10])).
% 17.56/8.22  tff(c_48, plain, (![A_40, B_41, D_43]: (k4_zfmisc_1(A_40, B_41, k1_xboole_0, D_43)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_107])).
% 17.56/8.22  tff(c_8275, plain, (![A_40, B_41, D_43]: (k4_zfmisc_1(A_40, B_41, '#skF_8', D_43)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8260, c_8260, c_48])).
% 17.56/8.22  tff(c_8888, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8275, c_99])).
% 17.56/8.22  tff(c_8892, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8255, c_8888])).
% 17.56/8.22  tff(c_8893, plain, (![B_129]: (~v1_xboole_0(B_129))), inference(splitRight, [status(thm)], [c_444])).
% 17.56/8.22  tff(c_8902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8893, c_395])).
% 17.56/8.22  tff(c_8904, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_327])).
% 17.56/8.22  tff(c_8939, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_8904, c_10])).
% 17.56/8.22  tff(c_52, plain, (![B_41, C_42, D_43]: (k4_zfmisc_1(k1_xboole_0, B_41, C_42, D_43)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_107])).
% 17.56/8.22  tff(c_8946, plain, (![B_41, C_42, D_43]: (k4_zfmisc_1('#skF_6', B_41, C_42, D_43)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8939, c_8939, c_52])).
% 17.56/8.22  tff(c_9009, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_8946, c_99])).
% 17.56/8.22  tff(c_9013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8904, c_9009])).
% 17.56/8.22  tff(c_9015, plain, (~v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_394])).
% 17.56/8.22  tff(c_9014, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_394])).
% 17.56/8.22  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(k1_tarski(A_9), B_10)=k1_xboole_0 | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 17.56/8.22  tff(c_9075, plain, (![B_917]: (k4_xboole_0(k1_xboole_0, B_917)=k1_xboole_0 | ~r2_hidden('#skF_1'(k1_xboole_0), B_917))), inference(superposition, [status(thm), theory('equality')], [c_9014, c_14])).
% 17.56/8.22  tff(c_9083, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_9075])).
% 17.56/8.22  tff(c_9087, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_9015, c_9083])).
% 17.56/8.22  tff(c_20, plain, (![A_14, B_15]: (~r2_hidden(A_14, B_15) | k4_xboole_0(k1_tarski(A_14), B_15)!=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.56/8.22  tff(c_9048, plain, (![B_15]: (~r2_hidden('#skF_1'(k1_xboole_0), B_15) | k4_xboole_0(k1_xboole_0, B_15)!=k1_tarski('#skF_1'(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_9014, c_20])).
% 17.56/8.22  tff(c_9092, plain, (![B_918]: (~r2_hidden('#skF_1'(k1_xboole_0), B_918) | k4_xboole_0(k1_xboole_0, B_918)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9014, c_9048])).
% 17.56/8.22  tff(c_9100, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0 | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_9092])).
% 17.56/8.22  tff(c_9104, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_9087, c_9100])).
% 17.56/8.22  tff(c_9106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9015, c_9104])).
% 17.56/8.22  tff(c_9107, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_281])).
% 17.56/8.22  tff(c_9112, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_9107, c_10])).
% 17.56/8.22  tff(c_9137, plain, (![B_41, C_42, D_43]: (k4_zfmisc_1('#skF_6', B_41, C_42, D_43)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9112, c_9112, c_52])).
% 17.56/8.22  tff(c_9212, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_9137, c_99])).
% 17.56/8.22  tff(c_9216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9107, c_9212])).
% 17.56/8.22  tff(c_9217, plain, (~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7') | ~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8') | ~r2_hidden(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_62])).
% 17.56/8.22  tff(c_27691, plain, (~r2_hidden(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_9217])).
% 17.56/8.22  tff(c_27762, plain, (~m1_subset_1(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_26, c_27691])).
% 17.56/8.22  tff(c_27774, plain, (~m1_subset_1(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_27762])).
% 17.56/8.22  tff(c_27778, plain, (~v1_xboole_0(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')) | ~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_28, c_27774])).
% 17.56/8.22  tff(c_27810, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_27778])).
% 17.56/8.22  tff(c_9367, plain, (~r2_hidden(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_9217])).
% 17.56/8.22  tff(c_9373, plain, (~m1_subset_1(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9') | v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_26, c_9367])).
% 17.56/8.22  tff(c_9409, plain, (~m1_subset_1(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_9373])).
% 17.56/8.22  tff(c_9414, plain, (~v1_xboole_0(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')) | ~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_28, c_9409])).
% 17.56/8.22  tff(c_9415, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_9414])).
% 17.56/8.22  tff(c_12110, plain, (![E_1202, D_1203, A_1200, C_1201, B_1204]: (m1_subset_1(k9_mcart_1(A_1200, B_1204, C_1201, D_1203, E_1202), B_1204) | ~m1_subset_1(E_1202, k4_zfmisc_1(A_1200, B_1204, C_1201, D_1203)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.56/8.22  tff(c_12140, plain, (![C_1216, B_1217, A_1218, E_1219, D_1215]: (v1_xboole_0(k9_mcart_1(A_1218, B_1217, C_1216, D_1215, E_1219)) | ~v1_xboole_0(B_1217) | ~m1_subset_1(E_1219, k4_zfmisc_1(A_1218, B_1217, C_1216, D_1215)))), inference(resolution, [status(thm)], [c_12110, c_30])).
% 17.56/8.22  tff(c_12189, plain, (v1_xboole_0(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_66, c_12140])).
% 17.56/8.22  tff(c_12194, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_12189])).
% 17.56/8.22  tff(c_9256, plain, (![B_934, A_935]: (m1_subset_1(B_934, A_935) | ~r2_hidden(B_934, A_935) | v1_xboole_0(A_935))), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.56/8.22  tff(c_9265, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')) | v1_xboole_0(k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_64, c_9256])).
% 17.56/8.22  tff(c_9275, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_99, c_9265])).
% 17.56/8.22  tff(c_12187, plain, (v1_xboole_0(k9_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')) | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_9275, c_12140])).
% 17.56/8.22  tff(c_12193, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_12187])).
% 17.56/8.22  tff(c_12195, plain, (![C_1221, B_1222, A_1224, D_1220, E_1223]: (k11_mcart_1(A_1224, B_1222, C_1221, D_1220, E_1223)=k2_mcart_1(E_1223) | ~m1_subset_1(E_1223, k4_zfmisc_1(A_1224, B_1222, C_1221, D_1220)) | k1_xboole_0=D_1220 | k1_xboole_0=C_1221 | k1_xboole_0=B_1222 | k1_xboole_0=A_1224)), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.56/8.22  tff(c_12244, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_66, c_12195])).
% 17.56/8.22  tff(c_12294, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_12244])).
% 17.56/8.22  tff(c_9317, plain, (![A_946, B_947]: (k4_xboole_0(k1_tarski(A_946), B_947)=k1_tarski(A_946) | r2_hidden(A_946, B_947))), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.56/8.22  tff(c_9323, plain, (![A_946, B_947]: (r2_hidden(A_946, B_947) | k1_tarski(A_946)!=k1_xboole_0 | r2_hidden(A_946, B_947))), inference(superposition, [status(thm), theory('equality')], [c_9317, c_12])).
% 17.56/8.22  tff(c_9358, plain, (![A_952, B_953]: (k1_tarski(A_952)!=k1_xboole_0 | r2_hidden(A_952, B_953))), inference(factorization, [status(thm), theory('equality')], [c_9323])).
% 17.56/8.22  tff(c_9366, plain, (![B_953, A_952]: (~v1_xboole_0(B_953) | k1_tarski(A_952)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_9358, c_2])).
% 17.56/8.22  tff(c_9368, plain, (![A_952]: (k1_tarski(A_952)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_9366])).
% 17.56/8.22  tff(c_9374, plain, (![C_955, B_956]: (k3_xboole_0(k2_tarski(C_955, C_955), B_956)=k1_tarski(C_955) | ~r2_hidden(C_955, B_956))), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.56/8.22  tff(c_9381, plain, (![C_955]: (k1_tarski(C_955)=k1_xboole_0 | ~r2_hidden(C_955, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9374, c_8])).
% 17.56/8.22  tff(c_9393, plain, (![C_957]: (~r2_hidden(C_957, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_9368, c_9381])).
% 17.56/8.22  tff(c_9403, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_9393])).
% 17.56/8.22  tff(c_12305, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12294, c_9403])).
% 17.56/8.22  tff(c_12314, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12294, c_12294, c_8])).
% 17.56/8.22  tff(c_9231, plain, (k3_xboole_0('#skF_6', '#skF_2')='#skF_6'), inference(resolution, [status(thm)], [c_230, c_6])).
% 17.56/8.22  tff(c_12379, plain, ('#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12314, c_9231])).
% 17.56/8.22  tff(c_9218, plain, (r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(splitRight, [status(thm)], [c_62])).
% 17.56/8.22  tff(c_9243, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_9218, c_2])).
% 17.56/8.22  tff(c_12419, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_12379, c_9243])).
% 17.56/8.22  tff(c_12427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12305, c_12419])).
% 17.56/8.22  tff(c_12428, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_12244])).
% 17.56/8.22  tff(c_12430, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_12428])).
% 17.56/8.22  tff(c_12446, plain, (~m1_subset_1(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12430, c_9409])).
% 17.56/8.22  tff(c_12242, plain, (k11_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_9275, c_12195])).
% 17.56/8.22  tff(c_13212, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_12242])).
% 17.56/8.22  tff(c_13239, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_13212, c_9403])).
% 17.56/8.22  tff(c_13251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9243, c_13239])).
% 17.56/8.22  tff(c_13252, plain, (k1_xboole_0='#skF_7' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9' | k11_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_12242])).
% 17.56/8.22  tff(c_13254, plain, (k11_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_13252])).
% 17.56/8.22  tff(c_13258, plain, (m1_subset_1(k2_mcart_1('#skF_10'), '#skF_9') | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_13254, c_38])).
% 17.56/8.22  tff(c_13262, plain, (m1_subset_1(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_9275, c_13258])).
% 17.56/8.22  tff(c_13264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12446, c_13262])).
% 17.56/8.22  tff(c_13265, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_13252])).
% 17.56/8.22  tff(c_13267, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_13265])).
% 17.56/8.22  tff(c_13348, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13267, c_9403])).
% 17.56/8.22  tff(c_13360, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12193, c_13348])).
% 17.56/8.22  tff(c_13361, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_13265])).
% 17.56/8.22  tff(c_13363, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_13361])).
% 17.56/8.22  tff(c_13395, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_13363, c_9403])).
% 17.56/8.22  tff(c_13407, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9415, c_13395])).
% 17.56/8.22  tff(c_13408, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_13361])).
% 17.56/8.22  tff(c_13439, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_13408, c_9403])).
% 17.56/8.22  tff(c_13446, plain, (![A_40, B_41, D_43]: (k4_zfmisc_1(A_40, B_41, '#skF_8', D_43)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_13408, c_13408, c_48])).
% 17.56/8.22  tff(c_13701, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_13446, c_99])).
% 17.56/8.22  tff(c_13705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13439, c_13701])).
% 17.56/8.22  tff(c_13706, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_12428])).
% 17.56/8.22  tff(c_13708, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_13706])).
% 17.56/8.22  tff(c_13720, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13708, c_9403])).
% 17.56/8.22  tff(c_13732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12194, c_13720])).
% 17.56/8.22  tff(c_13733, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_13706])).
% 17.56/8.22  tff(c_13735, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_13733])).
% 17.56/8.22  tff(c_13848, plain, (![A_1353]: (k3_xboole_0(A_1353, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13735, c_13735, c_8])).
% 17.56/8.22  tff(c_9222, plain, (k3_xboole_0('#skF_9', '#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_228, c_6])).
% 17.56/8.22  tff(c_13864, plain, ('#skF_5'='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_13848, c_9222])).
% 17.56/8.22  tff(c_13748, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13735, c_9403])).
% 17.56/8.22  tff(c_13894, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_13864, c_13748])).
% 17.56/8.22  tff(c_13911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9415, c_13894])).
% 17.56/8.22  tff(c_13912, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_13733])).
% 17.56/8.22  tff(c_9390, plain, (![C_955]: (~r2_hidden(C_955, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_9368, c_9381])).
% 17.56/8.22  tff(c_13986, plain, (![C_955]: (~r2_hidden(C_955, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13912, c_9390])).
% 17.56/8.22  tff(c_13992, plain, (![A_40, B_41, D_43]: (k4_zfmisc_1(A_40, B_41, '#skF_4', D_43)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13912, c_13912, c_48])).
% 17.56/8.22  tff(c_13994, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13912, c_13912, c_8])).
% 17.56/8.22  tff(c_14055, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13994, c_234])).
% 17.56/8.22  tff(c_14096, plain, (r2_hidden('#skF_10', k4_zfmisc_1('#skF_6', '#skF_7', '#skF_4', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_14055, c_64])).
% 17.56/8.22  tff(c_14197, plain, (r2_hidden('#skF_10', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13992, c_14096])).
% 17.56/8.22  tff(c_14201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13986, c_14197])).
% 17.56/8.22  tff(c_14203, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_12189])).
% 17.56/8.22  tff(c_14207, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_14203, c_10])).
% 17.56/8.22  tff(c_14223, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14207, c_14207, c_8])).
% 17.56/8.22  tff(c_9235, plain, (k3_xboole_0('#skF_7', '#skF_3')='#skF_7'), inference(resolution, [status(thm)], [c_229, c_6])).
% 17.56/8.22  tff(c_14289, plain, ('#skF_7'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14223, c_9235])).
% 17.56/8.22  tff(c_14327, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14289, c_12193])).
% 17.56/8.22  tff(c_14335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14203, c_14327])).
% 17.56/8.22  tff(c_14337, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_12187])).
% 17.56/8.22  tff(c_14342, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_14337, c_10])).
% 17.56/8.22  tff(c_14355, plain, (![A_40, C_42, D_43]: (k4_zfmisc_1(A_40, '#skF_7', C_42, D_43)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14342, c_14342, c_50])).
% 17.56/8.22  tff(c_14861, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_14355, c_99])).
% 17.56/8.22  tff(c_14865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14337, c_14861])).
% 17.56/8.22  tff(c_14867, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_9414])).
% 17.56/8.22  tff(c_14871, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_14867, c_10])).
% 17.56/8.22  tff(c_14908, plain, (![A_40, B_41, C_42]: (k4_zfmisc_1(A_40, B_41, C_42, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14871, c_14871, c_46])).
% 17.56/8.22  tff(c_14971, plain, (~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14908, c_99])).
% 17.56/8.22  tff(c_14975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14867, c_14971])).
% 17.56/8.22  tff(c_14976, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_9373])).
% 17.56/8.22  tff(c_14981, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_14976, c_10])).
% 17.56/8.22  tff(c_15018, plain, (![A_40, B_41, C_42]: (k4_zfmisc_1(A_40, B_41, C_42, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_14981, c_14981, c_46])).
% 17.56/8.22  tff(c_15088, plain, (~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_15018, c_99])).
% 17.56/8.22  tff(c_15092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14976, c_15088])).
% 17.56/8.22  tff(c_15093, plain, (![B_953]: (~v1_xboole_0(B_953))), inference(splitRight, [status(thm)], [c_9366])).
% 17.56/8.22  tff(c_15108, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_15093, c_4])).
% 17.56/8.22  tff(c_15152, plain, (![C_1446, B_1447]: (k3_xboole_0(k2_tarski(C_1446, C_1446), B_1447)=k1_tarski(C_1446) | ~r2_hidden(C_1446, B_1447))), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.56/8.22  tff(c_15169, plain, (![C_1448]: (k1_tarski(C_1448)=k1_xboole_0 | ~r2_hidden(C_1448, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_15152, c_8])).
% 17.56/8.22  tff(c_15183, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_15108, c_15169])).
% 17.56/8.22  tff(c_9351, plain, (![A_946, B_947]: (k1_tarski(A_946)!=k1_xboole_0 | r2_hidden(A_946, B_947))), inference(factorization, [status(thm), theory('equality')], [c_9323])).
% 17.56/8.22  tff(c_24, plain, (![B_17, A_16]: (m1_subset_1(B_17, A_16) | ~r2_hidden(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 17.56/8.22  tff(c_15128, plain, (![B_1444, A_1445]: (m1_subset_1(B_1444, A_1445) | ~r2_hidden(B_1444, A_1445))), inference(negUnitSimplification, [status(thm)], [c_15093, c_24])).
% 17.56/8.22  tff(c_15210, plain, (![A_1450, B_1451]: (m1_subset_1(A_1450, B_1451) | k1_tarski(A_1450)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_9351, c_15128])).
% 17.56/8.22  tff(c_32, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 17.56/8.22  tff(c_15225, plain, (![A_1452, B_1453]: (r1_tarski(A_1452, B_1453) | k1_tarski(A_1452)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_15210, c_32])).
% 17.56/8.22  tff(c_15230, plain, (![A_1454, B_1455]: (k3_xboole_0(A_1454, B_1455)=A_1454 | k1_tarski(A_1454)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_15225, c_6])).
% 17.56/8.22  tff(c_15284, plain, (![A_1456]: (k1_xboole_0=A_1456 | k1_tarski(A_1456)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15230, c_8])).
% 17.56/8.22  tff(c_15288, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_15183, c_15284])).
% 17.56/8.22  tff(c_15322, plain, (k1_tarski(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_15288, c_15183])).
% 17.56/8.22  tff(c_15372, plain, (![B_1460]: (k4_xboole_0(k1_xboole_0, B_1460)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, B_1460))), inference(superposition, [status(thm), theory('equality')], [c_15322, c_14])).
% 17.56/8.22  tff(c_15383, plain, (![B_947]: (k4_xboole_0(k1_xboole_0, B_947)=k1_xboole_0 | k1_tarski(k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_9351, c_15372])).
% 17.56/8.22  tff(c_15388, plain, (![B_947]: (k4_xboole_0(k1_xboole_0, B_947)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_15322, c_15383])).
% 17.56/8.22  tff(c_15339, plain, (![B_15]: (~r2_hidden(k1_xboole_0, B_15) | k4_xboole_0(k1_xboole_0, B_15)!=k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_15322, c_20])).
% 17.56/8.22  tff(c_15353, plain, (![B_15]: (~r2_hidden(k1_xboole_0, B_15) | k4_xboole_0(k1_xboole_0, B_15)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_15322, c_15339])).
% 17.56/8.22  tff(c_15424, plain, (![B_15]: (~r2_hidden(k1_xboole_0, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_15388, c_15353])).
% 17.56/8.22  tff(c_15329, plain, (r2_hidden(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_15288, c_15108])).
% 17.56/8.22  tff(c_15426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15424, c_15329])).
% 17.56/8.22  tff(c_15428, plain, (r2_hidden(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_9217])).
% 17.56/8.22  tff(c_15438, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_15428, c_2])).
% 17.56/8.22  tff(c_24715, plain, (![C_2382, A_2381, E_2384, B_2383, D_2380]: (m1_subset_1(k11_mcart_1(A_2381, B_2383, C_2382, D_2380, E_2384), D_2380) | ~m1_subset_1(E_2384, k4_zfmisc_1(A_2381, B_2383, C_2382, D_2380)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 17.56/8.22  tff(c_24757, plain, (![C_2399, A_2397, D_2396, E_2395, B_2398]: (v1_xboole_0(k11_mcart_1(A_2397, B_2398, C_2399, D_2396, E_2395)) | ~v1_xboole_0(D_2396) | ~m1_subset_1(E_2395, k4_zfmisc_1(A_2397, B_2398, C_2399, D_2396)))), inference(resolution, [status(thm)], [c_24715, c_30])).
% 17.56/8.22  tff(c_24806, plain, (v1_xboole_0(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_24757])).
% 17.56/8.22  tff(c_24810, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_24806])).
% 17.56/8.22  tff(c_15427, plain, (~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8') | ~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(splitRight, [status(thm)], [c_9217])).
% 17.56/8.22  tff(c_15502, plain, (~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(splitLeft, [status(thm)], [c_15427])).
% 17.56/8.22  tff(c_15509, plain, (~m1_subset_1(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_26, c_15502])).
% 17.56/8.22  tff(c_15536, plain, (~m1_subset_1(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(splitLeft, [status(thm)], [c_15509])).
% 17.56/8.22  tff(c_15540, plain, (~v1_xboole_0(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')) | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_28, c_15536])).
% 17.56/8.22  tff(c_15541, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_15540])).
% 17.56/8.22  tff(c_18985, plain, (![A_1832, C_1829, B_1830, D_1828, E_1831]: (k11_mcart_1(A_1832, B_1830, C_1829, D_1828, E_1831)=k2_mcart_1(E_1831) | ~m1_subset_1(E_1831, k4_zfmisc_1(A_1832, B_1830, C_1829, D_1828)) | k1_xboole_0=D_1828 | k1_xboole_0=C_1829 | k1_xboole_0=B_1830 | k1_xboole_0=A_1832)), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.56/8.22  tff(c_19032, plain, (k11_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_9275, c_18985])).
% 17.56/8.22  tff(c_19691, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_19032])).
% 17.56/8.22  tff(c_15429, plain, (![A_952]: (k1_tarski(A_952)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_9366])).
% 17.56/8.22  tff(c_15439, plain, (![C_1467, B_1468]: (k3_xboole_0(k2_tarski(C_1467, C_1467), B_1468)=k1_tarski(C_1467) | ~r2_hidden(C_1467, B_1468))), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.56/8.22  tff(c_15446, plain, (![C_1467]: (k1_tarski(C_1467)=k1_xboole_0 | ~r2_hidden(C_1467, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_15439, c_8])).
% 17.56/8.22  tff(c_15486, plain, (![C_1472]: (~r2_hidden(C_1472, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_15429, c_15446])).
% 17.56/8.22  tff(c_15496, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_15486])).
% 17.56/8.22  tff(c_19714, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_19691, c_15496])).
% 17.56/8.22  tff(c_19726, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9243, c_19714])).
% 17.56/8.22  tff(c_19728, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_19032])).
% 17.56/8.22  tff(c_19034, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_66, c_18985])).
% 17.56/8.22  tff(c_19082, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_19034])).
% 17.56/8.22  tff(c_19097, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19082, c_15496])).
% 17.56/8.22  tff(c_19106, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19082, c_19082, c_8])).
% 17.56/8.22  tff(c_19171, plain, ('#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_19106, c_9231])).
% 17.56/8.22  tff(c_19211, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19171, c_9243])).
% 17.56/8.22  tff(c_19219, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19097, c_19211])).
% 17.56/8.22  tff(c_19221, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_19034])).
% 17.56/8.22  tff(c_19268, plain, (![E_1860, D_1857, B_1859, A_1861, C_1858]: (k2_mcart_1(k1_mcart_1(E_1860))=k10_mcart_1(A_1861, B_1859, C_1858, D_1857, E_1860) | ~m1_subset_1(E_1860, k4_zfmisc_1(A_1861, B_1859, C_1858, D_1857)) | k1_xboole_0=D_1857 | k1_xboole_0=C_1858 | k1_xboole_0=B_1859 | k1_xboole_0=A_1861)), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.56/8.22  tff(c_19294, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_66, c_19268])).
% 17.56/8.22  tff(c_19319, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_19221, c_19294])).
% 17.56/8.22  tff(c_19357, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_19319])).
% 17.56/8.22  tff(c_19377, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19357, c_15496])).
% 17.56/8.22  tff(c_19386, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19357, c_19357, c_8])).
% 17.56/8.22  tff(c_19445, plain, ('#skF_7'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_19386, c_9235])).
% 17.56/8.22  tff(c_19483, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19445, c_15541])).
% 17.56/8.22  tff(c_19493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19377, c_19483])).
% 17.56/8.22  tff(c_19494, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_19319])).
% 17.56/8.22  tff(c_19496, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitLeft, [status(thm)], [c_19494])).
% 17.56/8.22  tff(c_19315, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_9275, c_19268])).
% 17.56/8.22  tff(c_20405, plain, (k10_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_19496, c_19315])).
% 17.56/8.22  tff(c_20406, plain, (k10_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_19728, c_20405])).
% 17.56/8.22  tff(c_20407, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_20406])).
% 17.56/8.22  tff(c_20439, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_20407, c_15496])).
% 17.56/8.22  tff(c_20451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15541, c_20439])).
% 17.56/8.22  tff(c_20453, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_20406])).
% 17.56/8.22  tff(c_18852, plain, (![B_1799, C_1798, D_1800, E_1801, A_1802]: (m1_subset_1(k10_mcart_1(A_1802, B_1799, C_1798, D_1800, E_1801), C_1798) | ~m1_subset_1(E_1801, k4_zfmisc_1(A_1802, B_1799, C_1798, D_1800)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 17.56/8.22  tff(c_20279, plain, (![A_1942, B_1940, E_1941, D_1943, C_1939]: (v1_xboole_0(k10_mcart_1(A_1942, B_1940, C_1939, D_1943, E_1941)) | ~v1_xboole_0(C_1939) | ~m1_subset_1(E_1941, k4_zfmisc_1(A_1942, B_1940, C_1939, D_1943)))), inference(resolution, [status(thm)], [c_18852, c_30])).
% 17.56/8.22  tff(c_20326, plain, (v1_xboole_0(k10_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')) | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_9275, c_20279])).
% 17.56/8.22  tff(c_20332, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_20326])).
% 17.56/8.22  tff(c_19495, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_19319])).
% 17.56/8.22  tff(c_19774, plain, (![D_1903, E_1906, C_1904, A_1907, B_1905]: (k8_mcart_1(A_1907, B_1905, C_1904, D_1903, E_1906)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_1906))) | ~m1_subset_1(E_1906, k4_zfmisc_1(A_1907, B_1905, C_1904, D_1903)) | k1_xboole_0=D_1903 | k1_xboole_0=C_1904 | k1_xboole_0=B_1905 | k1_xboole_0=A_1907)), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.56/8.22  tff(c_19793, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_66, c_19774])).
% 17.56/8.22  tff(c_19815, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_19221, c_19495, c_19793])).
% 17.56/8.22  tff(c_19821, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_19815])).
% 17.56/8.22  tff(c_19847, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19821, c_15496])).
% 17.56/8.22  tff(c_19854, plain, (![A_40, B_41, D_43]: (k4_zfmisc_1(A_40, B_41, '#skF_4', D_43)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19821, c_19821, c_48])).
% 17.56/8.22  tff(c_196, plain, (v1_xboole_0('#skF_10') | ~v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_30])).
% 17.56/8.22  tff(c_9305, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_196])).
% 17.56/8.22  tff(c_20076, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19854, c_9305])).
% 17.56/8.22  tff(c_20080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_19847, c_20076])).
% 17.56/8.22  tff(c_20081, plain, (k1_xboole_0='#skF_5' | k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_19815])).
% 17.56/8.22  tff(c_20083, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitLeft, [status(thm)], [c_20081])).
% 17.56/8.22  tff(c_19788, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_9275, c_19774])).
% 17.56/8.22  tff(c_19811, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_19728, c_19788])).
% 17.56/8.22  tff(c_20605, plain, (k8_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_20083, c_19811])).
% 17.56/8.22  tff(c_20606, plain, (k8_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_20453, c_20605])).
% 17.56/8.22  tff(c_20607, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_20606])).
% 17.56/8.22  tff(c_20644, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20607, c_15496])).
% 17.56/8.22  tff(c_20656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20332, c_20644])).
% 17.56/8.22  tff(c_20658, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_20606])).
% 17.56/8.22  tff(c_18842, plain, (![A_1794, C_1795, B_1796, E_1797, D_1793]: (m1_subset_1(k11_mcart_1(A_1794, B_1796, C_1795, D_1793, E_1797), D_1793) | ~m1_subset_1(E_1797, k4_zfmisc_1(A_1794, B_1796, C_1795, D_1793)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 17.56/8.22  tff(c_18872, plain, (![C_1810, B_1812, A_1809, D_1811, E_1808]: (v1_xboole_0(k11_mcart_1(A_1809, B_1812, C_1810, D_1811, E_1808)) | ~v1_xboole_0(D_1811) | ~m1_subset_1(E_1808, k4_zfmisc_1(A_1809, B_1812, C_1810, D_1811)))), inference(resolution, [status(thm)], [c_18842, c_30])).
% 17.56/8.22  tff(c_18921, plain, (v1_xboole_0(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_18872])).
% 17.56/8.22  tff(c_18925, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_18921])).
% 17.56/8.22  tff(c_20082, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_19815])).
% 17.56/8.22  tff(c_20183, plain, (![B_1936, A_1938, E_1937, C_1935, D_1934]: (k9_mcart_1(A_1938, B_1936, C_1935, D_1934, E_1937)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_1937))) | ~m1_subset_1(E_1937, k4_zfmisc_1(A_1938, B_1936, C_1935, D_1934)) | k1_xboole_0=D_1934 | k1_xboole_0=C_1935 | k1_xboole_0=B_1936 | k1_xboole_0=A_1938)), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.56/8.22  tff(c_20202, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_66, c_20183])).
% 17.56/8.22  tff(c_20224, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_19221, c_19495, c_20082, c_20202])).
% 17.56/8.22  tff(c_20230, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_20224])).
% 17.56/8.22  tff(c_20260, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_20230, c_15496])).
% 17.56/8.22  tff(c_20272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18925, c_20260])).
% 17.56/8.22  tff(c_20273, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_20224])).
% 17.56/8.22  tff(c_20197, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_9275, c_20183])).
% 17.56/8.22  tff(c_20220, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_19728, c_20197])).
% 17.56/8.22  tff(c_20824, plain, (k9_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_20273, c_20220])).
% 17.56/8.22  tff(c_20825, plain, (k9_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_20453, c_20658, c_20824])).
% 17.56/8.22  tff(c_20826, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_20825])).
% 17.56/8.22  tff(c_20870, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_20826, c_15496])).
% 17.56/8.22  tff(c_20882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15438, c_20870])).
% 17.56/8.22  tff(c_20883, plain, (k9_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_20825])).
% 17.56/8.22  tff(c_42, plain, (![A_35, B_36, C_37, D_38, E_39]: (m1_subset_1(k9_mcart_1(A_35, B_36, C_37, D_38, E_39), B_36) | ~m1_subset_1(E_39, k4_zfmisc_1(A_35, B_36, C_37, D_38)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.56/8.22  tff(c_21226, plain, (m1_subset_1(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7') | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_20883, c_42])).
% 17.56/8.22  tff(c_21230, plain, (m1_subset_1(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_9275, c_21226])).
% 17.56/8.22  tff(c_21232, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15536, c_21230])).
% 17.56/8.22  tff(c_21234, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_20326])).
% 17.56/8.22  tff(c_21250, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_21234, c_10])).
% 17.56/8.22  tff(c_21288, plain, (![A_40, B_41, D_43]: (k4_zfmisc_1(A_40, B_41, '#skF_8', D_43)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_21250, c_21250, c_48])).
% 17.56/8.22  tff(c_21588, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_21288, c_99])).
% 17.56/8.22  tff(c_21592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21234, c_21588])).
% 17.56/8.22  tff(c_21594, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_18921])).
% 17.56/8.22  tff(c_21598, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_21594, c_10])).
% 17.56/8.22  tff(c_21696, plain, (![A_2085]: (k3_xboole_0(A_2085, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_21598, c_21598, c_8])).
% 17.56/8.22  tff(c_21712, plain, ('#skF_5'='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_21696, c_9222])).
% 17.56/8.22  tff(c_21742, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_21712, c_21594])).
% 17.56/8.22  tff(c_21756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15438, c_21742])).
% 17.56/8.22  tff(c_21758, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_15540])).
% 17.56/8.22  tff(c_21762, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_21758, c_10])).
% 17.56/8.22  tff(c_21770, plain, (![A_40, C_42, D_43]: (k4_zfmisc_1(A_40, '#skF_7', C_42, D_43)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_21762, c_21762, c_50])).
% 17.56/8.22  tff(c_21860, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_21770, c_99])).
% 17.56/8.22  tff(c_21864, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21758, c_21860])).
% 17.56/8.22  tff(c_21865, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_15509])).
% 17.56/8.22  tff(c_21870, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_21865, c_10])).
% 17.56/8.22  tff(c_21888, plain, (![A_40, C_42, D_43]: (k4_zfmisc_1(A_40, '#skF_7', C_42, D_43)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_21870, c_21870, c_50])).
% 17.56/8.22  tff(c_21974, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_21888, c_99])).
% 17.56/8.22  tff(c_21978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21865, c_21974])).
% 17.56/8.22  tff(c_21979, plain, (~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_15427])).
% 17.56/8.22  tff(c_21994, plain, (~m1_subset_1(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8') | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_26, c_21979])).
% 17.56/8.22  tff(c_22006, plain, (~m1_subset_1(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8')), inference(splitLeft, [status(thm)], [c_21994])).
% 17.56/8.22  tff(c_21980, plain, (r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(splitRight, [status(thm)], [c_15427])).
% 17.56/8.22  tff(c_21988, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_21980, c_2])).
% 17.56/8.22  tff(c_24848, plain, (![B_2410, A_2412, D_2408, C_2409, E_2411]: (k11_mcart_1(A_2412, B_2410, C_2409, D_2408, E_2411)=k2_mcart_1(E_2411) | ~m1_subset_1(E_2411, k4_zfmisc_1(A_2412, B_2410, C_2409, D_2408)) | k1_xboole_0=D_2408 | k1_xboole_0=C_2409 | k1_xboole_0=B_2410 | k1_xboole_0=A_2412)), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.56/8.22  tff(c_24895, plain, (k11_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_9275, c_24848])).
% 17.56/8.22  tff(c_25672, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_24895])).
% 17.56/8.22  tff(c_25695, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_25672, c_15496])).
% 17.56/8.22  tff(c_25707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9243, c_25695])).
% 17.56/8.22  tff(c_25709, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_24895])).
% 17.56/8.22  tff(c_24897, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_66, c_24848])).
% 17.56/8.22  tff(c_24939, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_24897])).
% 17.56/8.22  tff(c_24952, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24939, c_15496])).
% 17.56/8.22  tff(c_24961, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24939, c_24939, c_8])).
% 17.56/8.22  tff(c_25026, plain, ('#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24961, c_9231])).
% 17.56/8.22  tff(c_25066, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_25026, c_9243])).
% 17.56/8.22  tff(c_25074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24952, c_25066])).
% 17.56/8.22  tff(c_25076, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_24897])).
% 17.56/8.22  tff(c_25121, plain, (![A_2440, E_2439, C_2437, D_2436, B_2438]: (k2_mcart_1(k1_mcart_1(E_2439))=k10_mcart_1(A_2440, B_2438, C_2437, D_2436, E_2439) | ~m1_subset_1(E_2439, k4_zfmisc_1(A_2440, B_2438, C_2437, D_2436)) | k1_xboole_0=D_2436 | k1_xboole_0=C_2437 | k1_xboole_0=B_2438 | k1_xboole_0=A_2440)), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.56/8.22  tff(c_25147, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_66, c_25121])).
% 17.56/8.22  tff(c_25172, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_25076, c_25147])).
% 17.56/8.22  tff(c_25224, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_25172])).
% 17.56/8.22  tff(c_25243, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25224, c_15496])).
% 17.56/8.22  tff(c_25252, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25224, c_25224, c_8])).
% 17.56/8.22  tff(c_25311, plain, ('#skF_7'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_25252, c_9235])).
% 17.56/8.22  tff(c_25350, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_25311, c_21988])).
% 17.56/8.22  tff(c_25359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25243, c_25350])).
% 17.56/8.22  tff(c_25360, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_25172])).
% 17.56/8.22  tff(c_25378, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitLeft, [status(thm)], [c_25360])).
% 17.56/8.22  tff(c_25168, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_9275, c_25121])).
% 17.56/8.22  tff(c_26005, plain, (k10_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_25378, c_25168])).
% 17.56/8.22  tff(c_26006, plain, (k10_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_25709, c_26005])).
% 17.56/8.22  tff(c_26007, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_26006])).
% 17.56/8.22  tff(c_26034, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_26007, c_15496])).
% 17.56/8.22  tff(c_26046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21988, c_26034])).
% 17.56/8.22  tff(c_26048, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_26006])).
% 17.56/8.22  tff(c_22010, plain, (~v1_xboole_0(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')) | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_28, c_22006])).
% 17.56/8.22  tff(c_22032, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_22010])).
% 17.56/8.22  tff(c_25361, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_25172])).
% 17.56/8.22  tff(c_25772, plain, (![D_2495, B_2497, E_2498, A_2499, C_2496]: (k9_mcart_1(A_2499, B_2497, C_2496, D_2495, E_2498)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_2498))) | ~m1_subset_1(E_2498, k4_zfmisc_1(A_2499, B_2497, C_2496, D_2495)) | k1_xboole_0=D_2495 | k1_xboole_0=C_2496 | k1_xboole_0=B_2497 | k1_xboole_0=A_2499)), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.56/8.22  tff(c_25791, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_66, c_25772])).
% 17.56/8.22  tff(c_25813, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_25076, c_25361, c_25791])).
% 17.56/8.22  tff(c_25819, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_25813])).
% 17.56/8.22  tff(c_25845, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25819, c_15496])).
% 17.56/8.22  tff(c_25854, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25819, c_25819, c_8])).
% 17.56/8.22  tff(c_25952, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25854, c_234])).
% 17.56/8.22  tff(c_25991, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25952, c_22032])).
% 17.56/8.22  tff(c_26001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25845, c_25991])).
% 17.56/8.22  tff(c_26003, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_25813])).
% 17.56/8.22  tff(c_26131, plain, (![B_2524, E_2525, A_2526, C_2523, D_2522]: (k8_mcart_1(A_2526, B_2524, C_2523, D_2522, E_2525)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_2525))) | ~m1_subset_1(E_2525, k4_zfmisc_1(A_2526, B_2524, C_2523, D_2522)) | k1_xboole_0=D_2522 | k1_xboole_0=C_2523 | k1_xboole_0=B_2524 | k1_xboole_0=A_2526)), inference(cnfTransformation, [status(thm)], [f_132])).
% 17.56/8.22  tff(c_26150, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_66, c_26131])).
% 17.56/8.22  tff(c_26172, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_25076, c_25361, c_26003, c_26150])).
% 17.56/8.22  tff(c_26178, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_26172])).
% 17.56/8.22  tff(c_26209, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26178, c_15496])).
% 17.56/8.22  tff(c_26221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24810, c_26209])).
% 17.56/8.22  tff(c_26222, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_26172])).
% 17.56/8.22  tff(c_26145, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_9275, c_26131])).
% 17.56/8.22  tff(c_26168, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_25709, c_26048, c_26145])).
% 17.56/8.22  tff(c_26228, plain, (k8_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_26222, c_26168])).
% 17.56/8.22  tff(c_26229, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_26228])).
% 17.56/8.22  tff(c_26261, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26229, c_15496])).
% 17.56/8.22  tff(c_26273, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22032, c_26261])).
% 17.56/8.22  tff(c_26275, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_26228])).
% 17.56/8.22  tff(c_26002, plain, (k1_xboole_0='#skF_5' | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_25813])).
% 17.56/8.22  tff(c_26004, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitLeft, [status(thm)], [c_26002])).
% 17.56/8.22  tff(c_25786, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_9275, c_25772])).
% 17.56/8.22  tff(c_25809, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_25709, c_25786])).
% 17.56/8.22  tff(c_26358, plain, (k9_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_26004, c_25809])).
% 17.56/8.22  tff(c_26359, plain, (k9_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_26048, c_26275, c_26358])).
% 17.56/8.22  tff(c_26360, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_26359])).
% 17.56/8.22  tff(c_26394, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_26360, c_15496])).
% 17.56/8.22  tff(c_26406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15438, c_26394])).
% 17.56/8.22  tff(c_26408, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_26359])).
% 17.56/8.22  tff(c_26047, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9' | k10_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_26006])).
% 17.56/8.22  tff(c_26560, plain, (k10_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9', '#skF_10')=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_26408, c_26275, c_26047])).
% 17.56/8.22  tff(c_36, plain, (![C_22, D_23, A_20, B_21, E_24]: (m1_subset_1(k10_mcart_1(A_20, B_21, C_22, D_23, E_24), C_22) | ~m1_subset_1(E_24, k4_zfmisc_1(A_20, B_21, C_22, D_23)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 17.56/8.22  tff(c_26564, plain, (m1_subset_1(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8') | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_26560, c_36])).
% 17.56/8.22  tff(c_26568, plain, (m1_subset_1(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9275, c_26564])).
% 17.56/8.22  tff(c_26570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22006, c_26568])).
% 17.56/8.22  tff(c_26571, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_25360])).
% 17.56/8.22  tff(c_26573, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_26571])).
% 17.56/8.22  tff(c_26594, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26573, c_15496])).
% 17.56/8.22  tff(c_26603, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26573, c_26573, c_8])).
% 17.56/8.22  tff(c_26684, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26603, c_234])).
% 17.56/8.22  tff(c_26722, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26684, c_22032])).
% 17.56/8.22  tff(c_26732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26594, c_26722])).
% 17.56/8.22  tff(c_26733, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_26571])).
% 17.56/8.22  tff(c_26802, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26733, c_15496])).
% 17.56/8.22  tff(c_26814, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24810, c_26802])).
% 17.56/8.22  tff(c_26816, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_24806])).
% 17.56/8.22  tff(c_26820, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_26816, c_10])).
% 17.56/8.22  tff(c_26865, plain, (![A_2572]: (k3_xboole_0(A_2572, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26820, c_26820, c_8])).
% 17.56/8.22  tff(c_26881, plain, ('#skF_5'='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_26865, c_9222])).
% 17.56/8.22  tff(c_26954, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_26881, c_26816])).
% 17.56/8.22  tff(c_26970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15438, c_26954])).
% 17.56/8.22  tff(c_26972, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_22010])).
% 17.56/8.22  tff(c_26976, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_26972, c_10])).
% 17.56/8.22  tff(c_26985, plain, (![A_40, B_41, D_43]: (k4_zfmisc_1(A_40, B_41, '#skF_8', D_43)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26976, c_26976, c_48])).
% 17.56/8.22  tff(c_27074, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_26985, c_99])).
% 17.56/8.22  tff(c_27078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26972, c_27074])).
% 17.56/8.22  tff(c_27079, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_21994])).
% 17.56/8.22  tff(c_27084, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_27079, c_10])).
% 17.56/8.22  tff(c_27098, plain, (![A_40, B_41, D_43]: (k4_zfmisc_1(A_40, B_41, '#skF_8', D_43)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_27084, c_27084, c_48])).
% 17.56/8.22  tff(c_27221, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_27098, c_99])).
% 17.56/8.22  tff(c_27225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27079, c_27221])).
% 17.56/8.22  tff(c_27226, plain, (![B_953]: (~v1_xboole_0(B_953))), inference(splitRight, [status(thm)], [c_9366])).
% 17.56/8.22  tff(c_27233, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_27226, c_4])).
% 17.56/8.22  tff(c_27336, plain, (![C_2625, B_2626]: (k3_xboole_0(k2_tarski(C_2625, C_2625), B_2626)=k1_tarski(C_2625) | ~r2_hidden(C_2625, B_2626))), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.56/8.22  tff(c_27360, plain, (![C_2627]: (k1_tarski(C_2627)=k1_xboole_0 | ~r2_hidden(C_2627, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_27336, c_8])).
% 17.56/8.22  tff(c_27374, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_27233, c_27360])).
% 17.56/8.22  tff(c_27249, plain, (![B_2616, A_2617]: (m1_subset_1(B_2616, A_2617) | ~r2_hidden(B_2616, A_2617))), inference(negUnitSimplification, [status(thm)], [c_27226, c_24])).
% 17.56/8.22  tff(c_27277, plain, (![A_2618, B_2619]: (m1_subset_1(A_2618, B_2619) | k1_tarski(A_2618)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_9351, c_27249])).
% 17.56/8.22  tff(c_27283, plain, (![A_2620, B_2621]: (r1_tarski(A_2620, B_2621) | k1_tarski(A_2620)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_27277, c_32])).
% 17.56/8.22  tff(c_27288, plain, (![A_2622, B_2623]: (k3_xboole_0(A_2622, B_2623)=A_2622 | k1_tarski(A_2622)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_27283, c_6])).
% 17.56/8.22  tff(c_27306, plain, (![A_2622]: (k1_xboole_0=A_2622 | k1_tarski(A_2622)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_27288, c_8])).
% 17.56/8.22  tff(c_27394, plain, ('#skF_1'(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_27374, c_27306])).
% 17.56/8.22  tff(c_27398, plain, (k1_tarski(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_27394, c_27374])).
% 17.56/8.22  tff(c_22, plain, (![A_14, B_15]: (k4_xboole_0(k1_tarski(A_14), B_15)=k1_tarski(A_14) | r2_hidden(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 17.56/8.22  tff(c_27419, plain, (![B_15]: (k4_xboole_0(k1_xboole_0, B_15)=k1_tarski(k1_xboole_0) | r2_hidden(k1_xboole_0, B_15))), inference(superposition, [status(thm), theory('equality')], [c_27398, c_22])).
% 17.56/8.22  tff(c_27431, plain, (![B_15]: (k4_xboole_0(k1_xboole_0, B_15)=k1_xboole_0 | r2_hidden(k1_xboole_0, B_15))), inference(demodulation, [status(thm), theory('equality')], [c_27398, c_27419])).
% 17.56/8.22  tff(c_27490, plain, (![B_2631]: (k4_xboole_0(k1_xboole_0, B_2631)=k1_xboole_0 | ~r2_hidden(k1_xboole_0, B_2631))), inference(superposition, [status(thm), theory('equality')], [c_27398, c_14])).
% 17.56/8.22  tff(c_27509, plain, (![B_15]: (k4_xboole_0(k1_xboole_0, B_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_27431, c_27490])).
% 17.56/8.22  tff(c_27422, plain, (![B_10]: (r2_hidden(k1_xboole_0, B_10) | k4_xboole_0(k1_xboole_0, B_10)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_27398, c_12])).
% 17.56/8.22  tff(c_27517, plain, (![B_10]: (r2_hidden(k1_xboole_0, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_27509, c_27422])).
% 17.56/8.22  tff(c_27416, plain, (![B_15]: (~r2_hidden(k1_xboole_0, B_15) | k4_xboole_0(k1_xboole_0, B_15)!=k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_27398, c_20])).
% 17.56/8.22  tff(c_27430, plain, (![B_15]: (~r2_hidden(k1_xboole_0, B_15) | k4_xboole_0(k1_xboole_0, B_15)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_27398, c_27416])).
% 17.56/8.22  tff(c_27624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27509, c_27517, c_27430])).
% 17.56/8.22  tff(c_27626, plain, (v1_xboole_0(k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_196])).
% 17.56/8.22  tff(c_27625, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_196])).
% 17.56/8.22  tff(c_27630, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_27625, c_10])).
% 17.56/8.22  tff(c_27638, plain, (![A_8]: (A_8='#skF_10' | ~v1_xboole_0(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_27630, c_10])).
% 17.56/8.22  tff(c_27668, plain, (k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')='#skF_10'), inference(resolution, [status(thm)], [c_27626, c_27638])).
% 17.56/8.22  tff(c_44, plain, (![A_40, B_41, C_42, D_43]: (k4_zfmisc_1(A_40, B_41, C_42, D_43)!=k1_xboole_0 | k1_xboole_0=D_43 | k1_xboole_0=C_42 | k1_xboole_0=B_41 | k1_xboole_0=A_40)), inference(cnfTransformation, [status(thm)], [f_107])).
% 17.56/8.22  tff(c_27923, plain, (![A_2679, B_2680, C_2681, D_2682]: (k4_zfmisc_1(A_2679, B_2680, C_2681, D_2682)!='#skF_10' | D_2682='#skF_10' | C_2681='#skF_10' | B_2680='#skF_10' | A_2679='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_27630, c_27630, c_27630, c_27630, c_27630, c_44])).
% 17.56/8.22  tff(c_27939, plain, ('#skF_10'='#skF_5' | '#skF_10'='#skF_4' | '#skF_10'='#skF_3' | '#skF_10'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_27668, c_27923])).
% 17.56/8.22  tff(c_27948, plain, ('#skF_10'='#skF_2'), inference(splitLeft, [status(thm)], [c_27939])).
% 17.56/8.22  tff(c_27966, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_27948, c_27625])).
% 17.56/8.22  tff(c_27637, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_27630, c_27630, c_8])).
% 17.56/8.22  tff(c_27964, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_27948, c_27948, c_27637])).
% 17.56/8.22  tff(c_28024, plain, ('#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_27964, c_9231])).
% 17.56/8.22  tff(c_28053, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28024, c_9243])).
% 17.56/8.22  tff(c_28059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_27966, c_28053])).
% 17.56/8.22  tff(c_28060, plain, ('#skF_10'='#skF_3' | '#skF_10'='#skF_4' | '#skF_10'='#skF_5'), inference(splitRight, [status(thm)], [c_27939])).
% 17.56/8.22  tff(c_28062, plain, ('#skF_10'='#skF_5'), inference(splitLeft, [status(thm)], [c_28060])).
% 17.56/8.22  tff(c_28139, plain, (![A_2700]: (k3_xboole_0(A_2700, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28062, c_28062, c_27637])).
% 17.56/8.22  tff(c_28151, plain, ('#skF_5'='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_28139, c_9222])).
% 17.56/8.22  tff(c_28081, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_28062, c_27625])).
% 17.56/8.22  tff(c_28176, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_28151, c_28081])).
% 17.56/8.22  tff(c_28185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_27810, c_28176])).
% 17.56/8.22  tff(c_28186, plain, ('#skF_10'='#skF_4' | '#skF_10'='#skF_3'), inference(splitRight, [status(thm)], [c_28060])).
% 17.56/8.22  tff(c_28198, plain, ('#skF_10'='#skF_3'), inference(splitLeft, [status(thm)], [c_28186])).
% 17.56/8.22  tff(c_28218, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28198, c_27625])).
% 17.56/8.22  tff(c_27634, plain, (![A_40, C_42, D_43]: (k4_zfmisc_1(A_40, '#skF_10', C_42, D_43)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_27630, c_27630, c_50])).
% 17.56/8.22  tff(c_28212, plain, (![A_40, C_42, D_43]: (k4_zfmisc_1(A_40, '#skF_3', C_42, D_43)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28198, c_28198, c_27634])).
% 17.56/8.22  tff(c_28216, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28198, c_28198, c_27637])).
% 17.56/8.22  tff(c_28276, plain, ('#skF_7'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28216, c_9235])).
% 17.56/8.22  tff(c_28312, plain, (~v1_xboole_0(k4_zfmisc_1('#skF_6', '#skF_3', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_28276, c_99])).
% 17.56/8.22  tff(c_28350, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28212, c_28312])).
% 17.56/8.22  tff(c_28353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28218, c_28350])).
% 17.56/8.22  tff(c_28354, plain, ('#skF_10'='#skF_4'), inference(splitRight, [status(thm)], [c_28186])).
% 17.56/8.22  tff(c_27784, plain, (![A_2663, B_2664]: (r2_hidden(A_2663, B_2664) | k4_xboole_0(k1_tarski(A_2663), B_2664)!='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_27630, c_12])).
% 17.56/8.22  tff(c_27787, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | k1_tarski(A_14)!='#skF_10' | r2_hidden(A_14, B_15))), inference(superposition, [status(thm), theory('equality')], [c_22, c_27784])).
% 17.56/8.22  tff(c_27888, plain, (![A_2675, B_2676]: (k1_tarski(A_2675)!='#skF_10' | r2_hidden(A_2675, B_2676))), inference(factorization, [status(thm), theory('equality')], [c_27787])).
% 17.56/8.22  tff(c_27905, plain, (![B_2676, A_2675]: (~v1_xboole_0(B_2676) | k1_tarski(A_2675)!='#skF_10')), inference(resolution, [status(thm)], [c_27888, c_2])).
% 17.56/8.22  tff(c_27906, plain, (![A_2675]: (k1_tarski(A_2675)!='#skF_10')), inference(splitLeft, [status(thm)], [c_27905])).
% 17.56/8.22  tff(c_27811, plain, (![C_2667, B_2668]: (k3_xboole_0(k2_tarski(C_2667, C_2667), B_2668)=k1_tarski(C_2667) | ~r2_hidden(C_2667, B_2668))), inference(cnfTransformation, [status(thm)], [f_54])).
% 17.56/8.22  tff(c_27825, plain, (![C_2667]: (k1_tarski(C_2667)='#skF_10' | ~r2_hidden(C_2667, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_27637, c_27811])).
% 17.56/8.22  tff(c_27907, plain, (![C_2667]: (~r2_hidden(C_2667, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_27906, c_27825])).
% 17.56/8.22  tff(c_28360, plain, (![C_2667]: (~r2_hidden(C_2667, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28354, c_27907])).
% 17.56/8.22  tff(c_27635, plain, (![A_40, B_41, D_43]: (k4_zfmisc_1(A_40, B_41, '#skF_10', D_43)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_27630, c_27630, c_48])).
% 17.56/8.22  tff(c_28372, plain, (![A_40, B_41, D_43]: (k4_zfmisc_1(A_40, B_41, '#skF_4', D_43)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28354, c_28354, c_27635])).
% 17.56/8.22  tff(c_28374, plain, (![A_7]: (k3_xboole_0(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28354, c_28354, c_27637])).
% 17.56/8.22  tff(c_28439, plain, ('#skF_8'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28374, c_234])).
% 17.56/8.22  tff(c_28379, plain, (r2_hidden('#skF_4', k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_28354, c_64])).
% 17.56/8.22  tff(c_28468, plain, (r2_hidden('#skF_4', k4_zfmisc_1('#skF_6', '#skF_7', '#skF_4', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_28439, c_28379])).
% 17.56/8.22  tff(c_28537, plain, (r2_hidden('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28372, c_28468])).
% 17.56/8.22  tff(c_28541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28360, c_28537])).
% 17.56/8.22  tff(c_28542, plain, (![B_2676]: (~v1_xboole_0(B_2676))), inference(splitRight, [status(thm)], [c_27905])).
% 17.56/8.22  tff(c_28551, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28542, c_27625])).
% 17.56/8.22  tff(c_28553, plain, (v1_xboole_0('#skF_9')), inference(splitRight, [status(thm)], [c_27778])).
% 17.56/8.22  tff(c_28557, plain, ('#skF_10'='#skF_9'), inference(resolution, [status(thm)], [c_28553, c_27638])).
% 17.56/8.22  tff(c_27636, plain, (![A_40, B_41, C_42]: (k4_zfmisc_1(A_40, B_41, C_42, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_27630, c_27630, c_46])).
% 17.56/8.22  tff(c_28567, plain, (![A_40, B_41, C_42]: (k4_zfmisc_1(A_40, B_41, C_42, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_28557, c_28557, c_27636])).
% 17.56/8.22  tff(c_28707, plain, (~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_28567, c_99])).
% 17.56/8.22  tff(c_28710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28553, c_28707])).
% 17.56/8.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.56/8.22  
% 17.56/8.22  Inference rules
% 17.56/8.22  ----------------------
% 17.56/8.22  #Ref     : 0
% 17.56/8.22  #Sup     : 5534
% 17.56/8.22  #Fact    : 6
% 17.56/8.22  #Define  : 0
% 17.56/8.22  #Split   : 221
% 17.56/8.22  #Chain   : 0
% 17.56/8.22  #Close   : 0
% 17.56/8.22  
% 17.56/8.22  Ordering : KBO
% 17.56/8.22  
% 17.56/8.22  Simplification rules
% 17.56/8.22  ----------------------
% 17.56/8.22  #Subsume      : 819
% 17.56/8.22  #Demod        : 10345
% 17.56/8.22  #Tautology    : 2021
% 17.56/8.22  #SimpNegUnit  : 660
% 17.56/8.22  #BackRed      : 4338
% 17.56/8.22  
% 17.56/8.22  #Partial instantiations: 0
% 17.56/8.22  #Strategies tried      : 1
% 17.56/8.22  
% 17.56/8.22  Timing (in seconds)
% 17.56/8.22  ----------------------
% 17.56/8.23  Preprocessing        : 0.58
% 17.56/8.23  Parsing              : 0.29
% 17.56/8.23  CNF conversion       : 0.06
% 17.56/8.23  Main loop            : 6.60
% 17.56/8.23  Inferencing          : 1.92
% 17.56/8.23  Reduction            : 2.34
% 17.56/8.23  Demodulation         : 1.60
% 17.56/8.23  BG Simplification    : 0.28
% 17.56/8.23  Subsumption          : 1.37
% 17.56/8.23  Abstraction          : 0.35
% 17.56/8.23  MUC search           : 0.00
% 17.56/8.23  Cooper               : 0.00
% 17.56/8.23  Total                : 7.35
% 17.56/8.23  Index Insertion      : 0.00
% 17.56/8.23  Index Deletion       : 0.00
% 17.56/8.23  Index Matching       : 0.00
% 17.56/8.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
