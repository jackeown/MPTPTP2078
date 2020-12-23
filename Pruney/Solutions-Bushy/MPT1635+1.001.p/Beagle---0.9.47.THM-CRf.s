%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1635+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:09 EST 2020

% Result     : Theorem 9.35s
% Output     : CNFRefutation 9.35s
% Verified   : 
% Statistics : Number of formulae       :  178 (3465 expanded)
%              Number of leaves         :   27 (1217 expanded)
%              Depth                    :   33
%              Number of atoms          :  576 (13919 expanded)
%              Number of equality atoms :   58 (1731 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > m1_subset_1 > v2_struct_0 > l1_orders_2 > k4_waybel_0 > a_2_1_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_4 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(a_2_1_waybel_0,type,(
    a_2_1_waybel_0: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_waybel_0,type,(
    k4_waybel_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => k4_waybel_0(A,B) = a_2_1_waybel_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_waybel_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_1_waybel_0(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ? [E] :
                ( m1_subset_1(E,u1_struct_0(B))
                & r1_orders_2(B,E,D)
                & r2_hidden(E,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_waybel_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k4_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_0)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = k4_waybel_0(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_hidden(D,C)
                    <=> ? [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                          & r1_orders_2(A,E,D)
                          & r2_hidden(E,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_waybel_0)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_52,plain,(
    k4_waybel_0('#skF_8','#skF_9') != a_2_1_waybel_0('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_56,plain,(
    l1_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_54,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_6'(A_100,B_101),B_101)
      | ~ r2_hidden('#skF_7'(A_100,B_101),B_101)
      | B_101 = A_100 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_36,plain,(
    ! [A_87,B_88,C_89] :
      ( m1_subset_1('#skF_5'(A_87,B_88,C_89),u1_struct_0(B_88))
      | ~ r2_hidden(A_87,a_2_1_waybel_0(B_88,C_89))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(B_88)))
      | ~ l1_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1(k4_waybel_0(A_85,B_86),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    ! [B_88,A_87,C_89] :
      ( r1_orders_2(B_88,'#skF_5'(A_87,B_88,C_89),'#skF_4'(A_87,B_88,C_89))
      | ~ r2_hidden(A_87,a_2_1_waybel_0(B_88,C_89))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(B_88)))
      | ~ l1_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_120,plain,(
    ! [A_127,B_128,C_129] :
      ( r2_hidden('#skF_5'(A_127,B_128,C_129),C_129)
      | ~ r2_hidden(A_127,a_2_1_waybel_0(B_128,C_129))
      | ~ m1_subset_1(C_129,k1_zfmisc_1(u1_struct_0(B_128)))
      | ~ l1_orders_2(B_128)
      | v2_struct_0(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_124,plain,(
    ! [A_127] :
      ( r2_hidden('#skF_5'(A_127,'#skF_8','#skF_9'),'#skF_9')
      | ~ r2_hidden(A_127,a_2_1_waybel_0('#skF_8','#skF_9'))
      | ~ l1_orders_2('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_54,c_120])).

tff(c_128,plain,(
    ! [A_127] :
      ( r2_hidden('#skF_5'(A_127,'#skF_8','#skF_9'),'#skF_9')
      | ~ r2_hidden(A_127,a_2_1_waybel_0('#skF_8','#skF_9'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_124])).

tff(c_129,plain,(
    ! [A_127] :
      ( r2_hidden('#skF_5'(A_127,'#skF_8','#skF_9'),'#skF_9')
      | ~ r2_hidden(A_127,a_2_1_waybel_0('#skF_8','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_128])).

tff(c_5245,plain,(
    ! [D_557,A_558,B_559,E_560] :
      ( r2_hidden(D_557,k4_waybel_0(A_558,B_559))
      | ~ r2_hidden(E_560,B_559)
      | ~ r1_orders_2(A_558,E_560,D_557)
      | ~ m1_subset_1(E_560,u1_struct_0(A_558))
      | ~ m1_subset_1(D_557,u1_struct_0(A_558))
      | ~ m1_subset_1(k4_waybel_0(A_558,B_559),k1_zfmisc_1(u1_struct_0(A_558)))
      | ~ m1_subset_1(B_559,k1_zfmisc_1(u1_struct_0(A_558)))
      | ~ l1_orders_2(A_558) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5627,plain,(
    ! [D_629,A_630,A_631] :
      ( r2_hidden(D_629,k4_waybel_0(A_630,'#skF_9'))
      | ~ r1_orders_2(A_630,'#skF_5'(A_631,'#skF_8','#skF_9'),D_629)
      | ~ m1_subset_1('#skF_5'(A_631,'#skF_8','#skF_9'),u1_struct_0(A_630))
      | ~ m1_subset_1(D_629,u1_struct_0(A_630))
      | ~ m1_subset_1(k4_waybel_0(A_630,'#skF_9'),k1_zfmisc_1(u1_struct_0(A_630)))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0(A_630)))
      | ~ l1_orders_2(A_630)
      | ~ r2_hidden(A_631,a_2_1_waybel_0('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_129,c_5245])).

tff(c_5636,plain,(
    ! [A_87] :
      ( r2_hidden('#skF_4'(A_87,'#skF_8','#skF_9'),k4_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_5'(A_87,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_4'(A_87,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ m1_subset_1(k4_waybel_0('#skF_8','#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r2_hidden(A_87,a_2_1_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_orders_2('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_5627])).

tff(c_5648,plain,(
    ! [A_87] :
      ( r2_hidden('#skF_4'(A_87,'#skF_8','#skF_9'),k4_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_5'(A_87,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_4'(A_87,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ m1_subset_1(k4_waybel_0('#skF_8','#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r2_hidden(A_87,a_2_1_waybel_0('#skF_8','#skF_9'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_5636])).

tff(c_5649,plain,(
    ! [A_87] :
      ( r2_hidden('#skF_4'(A_87,'#skF_8','#skF_9'),k4_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_5'(A_87,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_4'(A_87,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ m1_subset_1(k4_waybel_0('#skF_8','#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r2_hidden(A_87,a_2_1_waybel_0('#skF_8','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5648])).

tff(c_5677,plain,(
    ~ m1_subset_1(k4_waybel_0('#skF_8','#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_5649])).

tff(c_5680,plain,
    ( ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_28,c_5677])).

tff(c_5684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_5680])).

tff(c_5686,plain,(
    m1_subset_1(k4_waybel_0('#skF_8','#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_5649])).

tff(c_48,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_6'(A_100,B_101),B_101)
      | r2_hidden('#skF_7'(A_100,B_101),A_100)
      | B_101 = A_100 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_107,plain,(
    ! [A_124,B_125,C_126] :
      ( '#skF_4'(A_124,B_125,C_126) = A_124
      | ~ r2_hidden(A_124,a_2_1_waybel_0(B_125,C_126))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(u1_struct_0(B_125)))
      | ~ l1_orders_2(B_125)
      | v2_struct_0(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5201,plain,(
    ! [A_554,B_555,C_556] :
      ( '#skF_4'('#skF_6'(A_554,a_2_1_waybel_0(B_555,C_556)),B_555,C_556) = '#skF_6'(A_554,a_2_1_waybel_0(B_555,C_556))
      | ~ m1_subset_1(C_556,k1_zfmisc_1(u1_struct_0(B_555)))
      | ~ l1_orders_2(B_555)
      | v2_struct_0(B_555)
      | r2_hidden('#skF_7'(A_554,a_2_1_waybel_0(B_555,C_556)),A_554)
      | a_2_1_waybel_0(B_555,C_556) = A_554 ) ),
    inference(resolution,[status(thm)],[c_48,c_107])).

tff(c_11151,plain,(
    ! [B_947,A_948,C_949] :
      ( r1_orders_2(B_947,'#skF_5'('#skF_6'(A_948,a_2_1_waybel_0(B_947,C_949)),B_947,C_949),'#skF_6'(A_948,a_2_1_waybel_0(B_947,C_949)))
      | ~ r2_hidden('#skF_6'(A_948,a_2_1_waybel_0(B_947,C_949)),a_2_1_waybel_0(B_947,C_949))
      | ~ m1_subset_1(C_949,k1_zfmisc_1(u1_struct_0(B_947)))
      | ~ l1_orders_2(B_947)
      | v2_struct_0(B_947)
      | ~ m1_subset_1(C_949,k1_zfmisc_1(u1_struct_0(B_947)))
      | ~ l1_orders_2(B_947)
      | v2_struct_0(B_947)
      | r2_hidden('#skF_7'(A_948,a_2_1_waybel_0(B_947,C_949)),A_948)
      | a_2_1_waybel_0(B_947,C_949) = A_948 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5201,c_34])).

tff(c_5290,plain,(
    ! [D_557,A_558,A_127] :
      ( r2_hidden(D_557,k4_waybel_0(A_558,'#skF_9'))
      | ~ r1_orders_2(A_558,'#skF_5'(A_127,'#skF_8','#skF_9'),D_557)
      | ~ m1_subset_1('#skF_5'(A_127,'#skF_8','#skF_9'),u1_struct_0(A_558))
      | ~ m1_subset_1(D_557,u1_struct_0(A_558))
      | ~ m1_subset_1(k4_waybel_0(A_558,'#skF_9'),k1_zfmisc_1(u1_struct_0(A_558)))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0(A_558)))
      | ~ l1_orders_2(A_558)
      | ~ r2_hidden(A_127,a_2_1_waybel_0('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_129,c_5245])).

tff(c_11154,plain,(
    ! [A_948] :
      ( r2_hidden('#skF_6'(A_948,a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_5'('#skF_6'(A_948,a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_6'(A_948,a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | ~ m1_subset_1(k4_waybel_0('#skF_8','#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r2_hidden('#skF_6'(A_948,a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | r2_hidden('#skF_7'(A_948,a_2_1_waybel_0('#skF_8','#skF_9')),A_948)
      | a_2_1_waybel_0('#skF_8','#skF_9') = A_948 ) ),
    inference(resolution,[status(thm)],[c_11151,c_5290])).

tff(c_11160,plain,(
    ! [A_948] :
      ( r2_hidden('#skF_6'(A_948,a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_5'('#skF_6'(A_948,a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_6'(A_948,a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | ~ r2_hidden('#skF_6'(A_948,a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9'))
      | v2_struct_0('#skF_8')
      | r2_hidden('#skF_7'(A_948,a_2_1_waybel_0('#skF_8','#skF_9')),A_948)
      | a_2_1_waybel_0('#skF_8','#skF_9') = A_948 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_5686,c_11154])).

tff(c_11168,plain,(
    ! [A_956] :
      ( r2_hidden('#skF_6'(A_956,a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_5'('#skF_6'(A_956,a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_6'(A_956,a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | ~ r2_hidden('#skF_6'(A_956,a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9'))
      | r2_hidden('#skF_7'(A_956,a_2_1_waybel_0('#skF_8','#skF_9')),A_956)
      | a_2_1_waybel_0('#skF_8','#skF_9') = A_956 ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_11160])).

tff(c_11171,plain,(
    ! [A_956] :
      ( r2_hidden('#skF_6'(A_956,a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_6'(A_956,a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | r2_hidden('#skF_7'(A_956,a_2_1_waybel_0('#skF_8','#skF_9')),A_956)
      | a_2_1_waybel_0('#skF_8','#skF_9') = A_956
      | ~ r2_hidden('#skF_6'(A_956,a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_orders_2('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_11168])).

tff(c_11177,plain,(
    ! [A_956] :
      ( r2_hidden('#skF_6'(A_956,a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_6'(A_956,a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | r2_hidden('#skF_7'(A_956,a_2_1_waybel_0('#skF_8','#skF_9')),A_956)
      | a_2_1_waybel_0('#skF_8','#skF_9') = A_956
      | ~ r2_hidden('#skF_6'(A_956,a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_11171])).

tff(c_11180,plain,(
    ! [A_957] :
      ( r2_hidden('#skF_6'(A_957,a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_6'(A_957,a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | r2_hidden('#skF_7'(A_957,a_2_1_waybel_0('#skF_8','#skF_9')),A_957)
      | a_2_1_waybel_0('#skF_8','#skF_9') = A_957
      | ~ r2_hidden('#skF_6'(A_957,a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_11177])).

tff(c_46,plain,(
    ! [A_100,B_101] :
      ( ~ r2_hidden('#skF_6'(A_100,B_101),A_100)
      | r2_hidden('#skF_7'(A_100,B_101),A_100)
      | B_101 = A_100 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_11193,plain,
    ( ~ m1_subset_1('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
    | r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9'))
    | k4_waybel_0('#skF_8','#skF_9') = a_2_1_waybel_0('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_11180,c_46])).

tff(c_11223,plain,
    ( ~ m1_subset_1('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
    | r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9'))
    | ~ r2_hidden('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_52,c_11193])).

tff(c_11231,plain,(
    ~ r2_hidden('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_11223])).

tff(c_11240,plain,
    ( ~ r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9'))
    | k4_waybel_0('#skF_8','#skF_9') = a_2_1_waybel_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_44,c_11231])).

tff(c_11253,plain,(
    ~ r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_11240])).

tff(c_50,plain,(
    ! [A_103,C_105,B_104] :
      ( m1_subset_1(A_103,C_105)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(C_105))
      | ~ r2_hidden(A_103,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5716,plain,(
    ! [A_637] :
      ( m1_subset_1(A_637,u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_637,k4_waybel_0('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_5686,c_50])).

tff(c_5847,plain,(
    ! [B_645] :
      ( m1_subset_1('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),B_645),u1_struct_0('#skF_8'))
      | r2_hidden('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),B_645),B_645)
      | k4_waybel_0('#skF_8','#skF_9') = B_645 ) ),
    inference(resolution,[status(thm)],[c_48,c_5716])).

tff(c_40,plain,(
    ! [A_87,B_88,C_89] :
      ( m1_subset_1('#skF_4'(A_87,B_88,C_89),u1_struct_0(B_88))
      | ~ r2_hidden(A_87,a_2_1_waybel_0(B_88,C_89))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(B_88)))
      | ~ l1_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4852,plain,(
    ! [D_496,B_497,C_498,E_499] :
      ( r2_hidden(D_496,a_2_1_waybel_0(B_497,C_498))
      | ~ r2_hidden(E_499,C_498)
      | ~ r1_orders_2(B_497,E_499,D_496)
      | ~ m1_subset_1(E_499,u1_struct_0(B_497))
      | ~ m1_subset_1(D_496,u1_struct_0(B_497))
      | ~ m1_subset_1(C_498,k1_zfmisc_1(u1_struct_0(B_497)))
      | ~ l1_orders_2(B_497)
      | v2_struct_0(B_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4876,plain,(
    ! [D_506,B_507,A_508] :
      ( r2_hidden(D_506,a_2_1_waybel_0(B_507,'#skF_9'))
      | ~ r1_orders_2(B_507,'#skF_5'(A_508,'#skF_8','#skF_9'),D_506)
      | ~ m1_subset_1('#skF_5'(A_508,'#skF_8','#skF_9'),u1_struct_0(B_507))
      | ~ m1_subset_1(D_506,u1_struct_0(B_507))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0(B_507)))
      | ~ l1_orders_2(B_507)
      | v2_struct_0(B_507)
      | ~ r2_hidden(A_508,a_2_1_waybel_0('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_129,c_4852])).

tff(c_4879,plain,(
    ! [A_87] :
      ( r2_hidden('#skF_4'(A_87,'#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_5'(A_87,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_4'(A_87,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_87,a_2_1_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_orders_2('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_4876])).

tff(c_4882,plain,(
    ! [A_87] :
      ( r2_hidden('#skF_4'(A_87,'#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_5'(A_87,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_4'(A_87,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_87,a_2_1_waybel_0('#skF_8','#skF_9'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4879])).

tff(c_4918,plain,(
    ! [A_515] :
      ( r2_hidden('#skF_4'(A_515,'#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_5'(A_515,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_4'(A_515,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_515,a_2_1_waybel_0('#skF_8','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4882])).

tff(c_38,plain,(
    ! [A_87,B_88,C_89] :
      ( '#skF_4'(A_87,B_88,C_89) = A_87
      | ~ r2_hidden(A_87,a_2_1_waybel_0(B_88,C_89))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(B_88)))
      | ~ l1_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4922,plain,(
    ! [A_515] :
      ( '#skF_4'('#skF_4'(A_515,'#skF_8','#skF_9'),'#skF_8','#skF_9') = '#skF_4'(A_515,'#skF_8','#skF_9')
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1('#skF_5'(A_515,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_4'(A_515,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_515,a_2_1_waybel_0('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_4918,c_38])).

tff(c_4926,plain,(
    ! [A_515] :
      ( '#skF_4'('#skF_4'(A_515,'#skF_8','#skF_9'),'#skF_8','#skF_9') = '#skF_4'(A_515,'#skF_8','#skF_9')
      | v2_struct_0('#skF_8')
      | ~ m1_subset_1('#skF_5'(A_515,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_4'(A_515,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_515,a_2_1_waybel_0('#skF_8','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4922])).

tff(c_4960,plain,(
    ! [A_527] :
      ( '#skF_4'('#skF_4'(A_527,'#skF_8','#skF_9'),'#skF_8','#skF_9') = '#skF_4'(A_527,'#skF_8','#skF_9')
      | ~ m1_subset_1('#skF_5'(A_527,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_4'(A_527,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_527,a_2_1_waybel_0('#skF_8','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4926])).

tff(c_4964,plain,(
    ! [A_87] :
      ( '#skF_4'('#skF_4'(A_87,'#skF_8','#skF_9'),'#skF_8','#skF_9') = '#skF_4'(A_87,'#skF_8','#skF_9')
      | ~ m1_subset_1('#skF_5'(A_87,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_87,a_2_1_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_orders_2('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_4960])).

tff(c_4970,plain,(
    ! [A_87] :
      ( '#skF_4'('#skF_4'(A_87,'#skF_8','#skF_9'),'#skF_8','#skF_9') = '#skF_4'(A_87,'#skF_8','#skF_9')
      | ~ m1_subset_1('#skF_5'(A_87,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_87,a_2_1_waybel_0('#skF_8','#skF_9'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4964])).

tff(c_4973,plain,(
    ! [A_528] :
      ( '#skF_4'('#skF_4'(A_528,'#skF_8','#skF_9'),'#skF_8','#skF_9') = '#skF_4'(A_528,'#skF_8','#skF_9')
      | ~ m1_subset_1('#skF_5'(A_528,'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_528,a_2_1_waybel_0('#skF_8','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4970])).

tff(c_4977,plain,(
    ! [A_87] :
      ( '#skF_4'('#skF_4'(A_87,'#skF_8','#skF_9'),'#skF_8','#skF_9') = '#skF_4'(A_87,'#skF_8','#skF_9')
      | ~ r2_hidden(A_87,a_2_1_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_orders_2('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_4973])).

tff(c_4983,plain,(
    ! [A_87] :
      ( '#skF_4'('#skF_4'(A_87,'#skF_8','#skF_9'),'#skF_8','#skF_9') = '#skF_4'(A_87,'#skF_8','#skF_9')
      | ~ r2_hidden(A_87,a_2_1_waybel_0('#skF_8','#skF_9'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4977])).

tff(c_4984,plain,(
    ! [A_87] :
      ( '#skF_4'('#skF_4'(A_87,'#skF_8','#skF_9'),'#skF_8','#skF_9') = '#skF_4'(A_87,'#skF_8','#skF_9')
      | ~ r2_hidden(A_87,a_2_1_waybel_0('#skF_8','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4983])).

tff(c_5857,plain,
    ( '#skF_4'('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),'#skF_8','#skF_9') = '#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9')
    | m1_subset_1('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
    | k4_waybel_0('#skF_8','#skF_9') = a_2_1_waybel_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_5847,c_4984])).

tff(c_5878,plain,
    ( '#skF_4'('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),'#skF_8','#skF_9') = '#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9')
    | m1_subset_1('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_5857])).

tff(c_10247,plain,(
    m1_subset_1('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_5878])).

tff(c_11243,plain,
    ( r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9'))
    | k4_waybel_0('#skF_8','#skF_9') = a_2_1_waybel_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_48,c_11231])).

tff(c_11256,plain,(
    r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_11243])).

tff(c_5113,plain,(
    ! [A_532,B_533,D_534] :
      ( r2_hidden('#skF_1'(A_532,B_533,k4_waybel_0(A_532,B_533),D_534),B_533)
      | ~ r2_hidden(D_534,k4_waybel_0(A_532,B_533))
      | ~ m1_subset_1(D_534,u1_struct_0(A_532))
      | ~ m1_subset_1(k4_waybel_0(A_532,B_533),k1_zfmisc_1(u1_struct_0(A_532)))
      | ~ m1_subset_1(B_533,k1_zfmisc_1(u1_struct_0(A_532)))
      | ~ l1_orders_2(A_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5116,plain,(
    ! [A_85,B_86,D_534] :
      ( r2_hidden('#skF_1'(A_85,B_86,k4_waybel_0(A_85,B_86),D_534),B_86)
      | ~ r2_hidden(D_534,k4_waybel_0(A_85,B_86))
      | ~ m1_subset_1(D_534,u1_struct_0(A_85))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85) ) ),
    inference(resolution,[status(thm)],[c_28,c_5113])).

tff(c_59,plain,(
    ! [A_107,C_108,B_109] :
      ( m1_subset_1(A_107,C_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(C_108))
      | ~ r2_hidden(A_107,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_62,plain,(
    ! [A_107] :
      ( m1_subset_1(A_107,u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_107,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_54,c_59])).

tff(c_5150,plain,(
    ! [A_545,B_546,D_547] :
      ( r1_orders_2(A_545,'#skF_1'(A_545,B_546,k4_waybel_0(A_545,B_546),D_547),D_547)
      | ~ r2_hidden(D_547,k4_waybel_0(A_545,B_546))
      | ~ m1_subset_1(D_547,u1_struct_0(A_545))
      | ~ m1_subset_1(k4_waybel_0(A_545,B_546),k1_zfmisc_1(u1_struct_0(A_545)))
      | ~ m1_subset_1(B_546,k1_zfmisc_1(u1_struct_0(A_545)))
      | ~ l1_orders_2(A_545) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5153,plain,(
    ! [A_85,B_86,D_547] :
      ( r1_orders_2(A_85,'#skF_1'(A_85,B_86,k4_waybel_0(A_85,B_86),D_547),D_547)
      | ~ r2_hidden(D_547,k4_waybel_0(A_85,B_86))
      | ~ m1_subset_1(D_547,u1_struct_0(A_85))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_orders_2(A_85) ) ),
    inference(resolution,[status(thm)],[c_28,c_5150])).

tff(c_5117,plain,(
    ! [A_535,B_536,D_537] :
      ( r2_hidden('#skF_1'(A_535,B_536,k4_waybel_0(A_535,B_536),D_537),B_536)
      | ~ r2_hidden(D_537,k4_waybel_0(A_535,B_536))
      | ~ m1_subset_1(D_537,u1_struct_0(A_535))
      | ~ m1_subset_1(B_536,k1_zfmisc_1(u1_struct_0(A_535)))
      | ~ l1_orders_2(A_535) ) ),
    inference(resolution,[status(thm)],[c_28,c_5113])).

tff(c_30,plain,(
    ! [D_97,B_88,C_89,E_99] :
      ( r2_hidden(D_97,a_2_1_waybel_0(B_88,C_89))
      | ~ r2_hidden(E_99,C_89)
      | ~ r1_orders_2(B_88,E_99,D_97)
      | ~ m1_subset_1(E_99,u1_struct_0(B_88))
      | ~ m1_subset_1(D_97,u1_struct_0(B_88))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(B_88)))
      | ~ l1_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_11273,plain,(
    ! [D_962,B_958,A_959,B_961,D_960] :
      ( r2_hidden(D_960,a_2_1_waybel_0(B_961,B_958))
      | ~ r1_orders_2(B_961,'#skF_1'(A_959,B_958,k4_waybel_0(A_959,B_958),D_962),D_960)
      | ~ m1_subset_1('#skF_1'(A_959,B_958,k4_waybel_0(A_959,B_958),D_962),u1_struct_0(B_961))
      | ~ m1_subset_1(D_960,u1_struct_0(B_961))
      | ~ m1_subset_1(B_958,k1_zfmisc_1(u1_struct_0(B_961)))
      | ~ l1_orders_2(B_961)
      | v2_struct_0(B_961)
      | ~ r2_hidden(D_962,k4_waybel_0(A_959,B_958))
      | ~ m1_subset_1(D_962,u1_struct_0(A_959))
      | ~ m1_subset_1(B_958,k1_zfmisc_1(u1_struct_0(A_959)))
      | ~ l1_orders_2(A_959) ) ),
    inference(resolution,[status(thm)],[c_5117,c_30])).

tff(c_11281,plain,(
    ! [D_963,A_964,B_965] :
      ( r2_hidden(D_963,a_2_1_waybel_0(A_964,B_965))
      | ~ m1_subset_1('#skF_1'(A_964,B_965,k4_waybel_0(A_964,B_965),D_963),u1_struct_0(A_964))
      | v2_struct_0(A_964)
      | ~ r2_hidden(D_963,k4_waybel_0(A_964,B_965))
      | ~ m1_subset_1(D_963,u1_struct_0(A_964))
      | ~ m1_subset_1(B_965,k1_zfmisc_1(u1_struct_0(A_964)))
      | ~ l1_orders_2(A_964) ) ),
    inference(resolution,[status(thm)],[c_5153,c_11273])).

tff(c_11299,plain,(
    ! [D_963,B_965] :
      ( r2_hidden(D_963,a_2_1_waybel_0('#skF_8',B_965))
      | v2_struct_0('#skF_8')
      | ~ r2_hidden(D_963,k4_waybel_0('#skF_8',B_965))
      | ~ m1_subset_1(D_963,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_965,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_orders_2('#skF_8')
      | ~ r2_hidden('#skF_1'('#skF_8',B_965,k4_waybel_0('#skF_8',B_965),D_963),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_62,c_11281])).

tff(c_11311,plain,(
    ! [D_963,B_965] :
      ( r2_hidden(D_963,a_2_1_waybel_0('#skF_8',B_965))
      | v2_struct_0('#skF_8')
      | ~ r2_hidden(D_963,k4_waybel_0('#skF_8',B_965))
      | ~ m1_subset_1(D_963,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_965,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r2_hidden('#skF_1'('#skF_8',B_965,k4_waybel_0('#skF_8',B_965),D_963),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_11299])).

tff(c_11540,plain,(
    ! [D_968,B_969] :
      ( r2_hidden(D_968,a_2_1_waybel_0('#skF_8',B_969))
      | ~ r2_hidden(D_968,k4_waybel_0('#skF_8',B_969))
      | ~ m1_subset_1(D_968,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_969,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r2_hidden('#skF_1'('#skF_8',B_969,k4_waybel_0('#skF_8',B_969),D_968),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_11311])).

tff(c_11547,plain,(
    ! [D_534] :
      ( r2_hidden(D_534,a_2_1_waybel_0('#skF_8','#skF_9'))
      | ~ r2_hidden(D_534,k4_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1(D_534,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_5116,c_11540])).

tff(c_11553,plain,(
    ! [D_970] :
      ( r2_hidden(D_970,a_2_1_waybel_0('#skF_8','#skF_9'))
      | ~ r2_hidden(D_970,k4_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1(D_970,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_11547])).

tff(c_11556,plain,
    ( r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_11256,c_11553])).

tff(c_11688,plain,(
    r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10247,c_11556])).

tff(c_11690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11253,c_11688])).

tff(c_11692,plain,(
    r2_hidden('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_11223])).

tff(c_11701,plain,
    ( '#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9') = '#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_11692,c_38])).

tff(c_11707,plain,
    ( '#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9') = '#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_11701])).

tff(c_11708,plain,(
    '#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9') = '#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_11707])).

tff(c_11751,plain,
    ( m1_subset_1('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
    | ~ r2_hidden('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_11708,c_40])).

tff(c_11787,plain,
    ( m1_subset_1('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_11692,c_11751])).

tff(c_11788,plain,(
    m1_subset_1('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_11787])).

tff(c_11748,plain,
    ( r1_orders_2('#skF_8','#skF_5'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),'#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')))
    | ~ r2_hidden('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_11708,c_34])).

tff(c_11784,plain,
    ( r1_orders_2('#skF_8','#skF_5'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),'#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_11692,c_11748])).

tff(c_11785,plain,(
    r1_orders_2('#skF_8','#skF_5'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),'#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_11784])).

tff(c_11801,plain,
    ( r2_hidden('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_5'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
    | ~ m1_subset_1(k4_waybel_0('#skF_8','#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_orders_2('#skF_8')
    | ~ r2_hidden('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_11785,c_5290])).

tff(c_11806,plain,
    ( r2_hidden('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_5'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11692,c_56,c_54,c_5686,c_11788,c_11801])).

tff(c_11834,plain,(
    ~ m1_subset_1('#skF_5'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_11806])).

tff(c_11902,plain,
    ( ~ r2_hidden('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_11834])).

tff(c_11908,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_11692,c_11902])).

tff(c_11910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_11908])).

tff(c_11911,plain,(
    r2_hidden('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_11806])).

tff(c_42,plain,(
    ! [A_100,B_101] :
      ( ~ r2_hidden('#skF_6'(A_100,B_101),A_100)
      | ~ r2_hidden('#skF_7'(A_100,B_101),B_101)
      | B_101 = A_100 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_11926,plain,
    ( ~ r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9'))
    | k4_waybel_0('#skF_8','#skF_9') = a_2_1_waybel_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_11911,c_42])).

tff(c_11939,plain,(
    ~ r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_11926])).

tff(c_11691,plain,
    ( ~ m1_subset_1('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
    | r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_11223])).

tff(c_11815,plain,(
    r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11788,c_11691])).

tff(c_11791,plain,(
    ! [B_971,D_973,B_974,A_972,D_975] :
      ( r2_hidden(D_973,a_2_1_waybel_0(B_974,B_971))
      | ~ r1_orders_2(B_974,'#skF_1'(A_972,B_971,k4_waybel_0(A_972,B_971),D_975),D_973)
      | ~ m1_subset_1('#skF_1'(A_972,B_971,k4_waybel_0(A_972,B_971),D_975),u1_struct_0(B_974))
      | ~ m1_subset_1(D_973,u1_struct_0(B_974))
      | ~ m1_subset_1(B_971,k1_zfmisc_1(u1_struct_0(B_974)))
      | ~ l1_orders_2(B_974)
      | v2_struct_0(B_974)
      | ~ r2_hidden(D_975,k4_waybel_0(A_972,B_971))
      | ~ m1_subset_1(D_975,u1_struct_0(A_972))
      | ~ m1_subset_1(B_971,k1_zfmisc_1(u1_struct_0(A_972)))
      | ~ l1_orders_2(A_972) ) ),
    inference(resolution,[status(thm)],[c_5117,c_30])).

tff(c_11942,plain,(
    ! [D_980,A_981,B_982] :
      ( r2_hidden(D_980,a_2_1_waybel_0(A_981,B_982))
      | ~ m1_subset_1('#skF_1'(A_981,B_982,k4_waybel_0(A_981,B_982),D_980),u1_struct_0(A_981))
      | v2_struct_0(A_981)
      | ~ r2_hidden(D_980,k4_waybel_0(A_981,B_982))
      | ~ m1_subset_1(D_980,u1_struct_0(A_981))
      | ~ m1_subset_1(B_982,k1_zfmisc_1(u1_struct_0(A_981)))
      | ~ l1_orders_2(A_981) ) ),
    inference(resolution,[status(thm)],[c_5153,c_11791])).

tff(c_11960,plain,(
    ! [D_980,B_982] :
      ( r2_hidden(D_980,a_2_1_waybel_0('#skF_8',B_982))
      | v2_struct_0('#skF_8')
      | ~ r2_hidden(D_980,k4_waybel_0('#skF_8',B_982))
      | ~ m1_subset_1(D_980,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_982,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_orders_2('#skF_8')
      | ~ r2_hidden('#skF_1'('#skF_8',B_982,k4_waybel_0('#skF_8',B_982),D_980),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_62,c_11942])).

tff(c_11972,plain,(
    ! [D_980,B_982] :
      ( r2_hidden(D_980,a_2_1_waybel_0('#skF_8',B_982))
      | v2_struct_0('#skF_8')
      | ~ r2_hidden(D_980,k4_waybel_0('#skF_8',B_982))
      | ~ m1_subset_1(D_980,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_982,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r2_hidden('#skF_1'('#skF_8',B_982,k4_waybel_0('#skF_8',B_982),D_980),'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_11960])).

tff(c_12305,plain,(
    ! [D_989,B_990] :
      ( r2_hidden(D_989,a_2_1_waybel_0('#skF_8',B_990))
      | ~ r2_hidden(D_989,k4_waybel_0('#skF_8',B_990))
      | ~ m1_subset_1(D_989,u1_struct_0('#skF_8'))
      | ~ m1_subset_1(B_990,k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ r2_hidden('#skF_1'('#skF_8',B_990,k4_waybel_0('#skF_8',B_990),D_989),'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_11972])).

tff(c_12312,plain,(
    ! [D_534] :
      ( r2_hidden(D_534,a_2_1_waybel_0('#skF_8','#skF_9'))
      | ~ r2_hidden(D_534,k4_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1(D_534,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
      | ~ l1_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_5116,c_12305])).

tff(c_12318,plain,(
    ! [D_991] :
      ( r2_hidden(D_991,a_2_1_waybel_0('#skF_8','#skF_9'))
      | ~ r2_hidden(D_991,k4_waybel_0('#skF_8','#skF_9'))
      | ~ m1_subset_1(D_991,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_12312])).

tff(c_12324,plain,
    ( r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_11815,c_12318])).

tff(c_12459,plain,(
    r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10247,c_12324])).

tff(c_12461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11939,c_12459])).

tff(c_12463,plain,(
    ~ m1_subset_1('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_5878])).

tff(c_90,plain,(
    ! [A_119,B_120] :
      ( m1_subset_1(k4_waybel_0(A_119,B_120),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_orders_2(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_93,plain,(
    ! [A_103,A_119,B_120] :
      ( m1_subset_1(A_103,u1_struct_0(A_119))
      | ~ r2_hidden(A_103,k4_waybel_0(A_119,B_120))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_orders_2(A_119) ) ),
    inference(resolution,[status(thm)],[c_90,c_50])).

tff(c_13131,plain,(
    ! [A_1042,B_1043,B_1044,C_1045] :
      ( m1_subset_1('#skF_7'(k4_waybel_0(A_1042,B_1043),a_2_1_waybel_0(B_1044,C_1045)),u1_struct_0(A_1042))
      | ~ m1_subset_1(B_1043,k1_zfmisc_1(u1_struct_0(A_1042)))
      | ~ l1_orders_2(A_1042)
      | '#skF_4'('#skF_6'(k4_waybel_0(A_1042,B_1043),a_2_1_waybel_0(B_1044,C_1045)),B_1044,C_1045) = '#skF_6'(k4_waybel_0(A_1042,B_1043),a_2_1_waybel_0(B_1044,C_1045))
      | ~ m1_subset_1(C_1045,k1_zfmisc_1(u1_struct_0(B_1044)))
      | ~ l1_orders_2(B_1044)
      | v2_struct_0(B_1044)
      | k4_waybel_0(A_1042,B_1043) = a_2_1_waybel_0(B_1044,C_1045) ) ),
    inference(resolution,[status(thm)],[c_5201,c_93])).

tff(c_13134,plain,
    ( '#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9') = '#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_orders_2('#skF_8')
    | v2_struct_0('#skF_8')
    | k4_waybel_0('#skF_8','#skF_9') = a_2_1_waybel_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_13131,c_12463])).

tff(c_13189,plain,
    ( '#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9') = '#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9'))
    | v2_struct_0('#skF_8')
    | k4_waybel_0('#skF_8','#skF_9') = a_2_1_waybel_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_13134])).

tff(c_13190,plain,(
    '#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9') = '#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_58,c_13189])).

tff(c_5808,plain,(
    ! [B_101] :
      ( m1_subset_1('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),B_101),u1_struct_0('#skF_8'))
      | r2_hidden('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),B_101),B_101)
      | k4_waybel_0('#skF_8','#skF_9') = B_101 ) ),
    inference(resolution,[status(thm)],[c_48,c_5716])).

tff(c_12733,plain,(
    ! [A_1013,B_1014,B_1015,C_1016] :
      ( m1_subset_1('#skF_7'(k4_waybel_0(A_1013,B_1014),a_2_1_waybel_0(B_1015,C_1016)),u1_struct_0(A_1013))
      | ~ m1_subset_1(B_1014,k1_zfmisc_1(u1_struct_0(A_1013)))
      | ~ l1_orders_2(A_1013)
      | '#skF_4'('#skF_6'(k4_waybel_0(A_1013,B_1014),a_2_1_waybel_0(B_1015,C_1016)),B_1015,C_1016) = '#skF_6'(k4_waybel_0(A_1013,B_1014),a_2_1_waybel_0(B_1015,C_1016))
      | ~ m1_subset_1(C_1016,k1_zfmisc_1(u1_struct_0(B_1015)))
      | ~ l1_orders_2(B_1015)
      | v2_struct_0(B_1015)
      | k4_waybel_0(A_1013,B_1014) = a_2_1_waybel_0(B_1015,C_1016) ) ),
    inference(resolution,[status(thm)],[c_5201,c_93])).

tff(c_12736,plain,
    ( '#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9') = '#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_orders_2('#skF_8')
    | v2_struct_0('#skF_8')
    | k4_waybel_0('#skF_8','#skF_9') = a_2_1_waybel_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_12733,c_12463])).

tff(c_12786,plain,
    ( '#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9') = '#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9'))
    | v2_struct_0('#skF_8')
    | k4_waybel_0('#skF_8','#skF_9') = a_2_1_waybel_0('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_12736])).

tff(c_12787,plain,(
    '#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9') = '#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_58,c_12786])).

tff(c_12462,plain,(
    '#skF_4'('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),'#skF_8','#skF_9') = '#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_5878])).

tff(c_12580,plain,
    ( m1_subset_1('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ r2_hidden('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_12462,c_40])).

tff(c_12601,plain,
    ( m1_subset_1('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ r2_hidden('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_12580])).

tff(c_12602,plain,
    ( m1_subset_1('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ r2_hidden('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_12601])).

tff(c_12604,plain,(
    ~ r2_hidden('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_12602])).

tff(c_12796,plain,(
    ~ r2_hidden('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12787,c_12604])).

tff(c_12863,plain,
    ( m1_subset_1('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8'))
    | k4_waybel_0('#skF_8','#skF_9') = a_2_1_waybel_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_5808,c_12796])).

tff(c_12876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_12463,c_12863])).

tff(c_12878,plain,(
    r2_hidden('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_12602])).

tff(c_12877,plain,(
    m1_subset_1('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_12602])).

tff(c_12577,plain,
    ( r1_orders_2('#skF_8','#skF_5'('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),'#skF_8','#skF_9'),'#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'))
    | ~ r2_hidden('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_12462,c_34])).

tff(c_12598,plain,
    ( r1_orders_2('#skF_8','#skF_5'('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),'#skF_8','#skF_9'),'#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'))
    | ~ r2_hidden('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_12577])).

tff(c_12599,plain,
    ( r1_orders_2('#skF_8','#skF_5'('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),'#skF_8','#skF_9'),'#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'))
    | ~ r2_hidden('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_12598])).

tff(c_13083,plain,(
    r1_orders_2('#skF_8','#skF_5'('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),'#skF_8','#skF_9'),'#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12878,c_12599])).

tff(c_13085,plain,
    ( r2_hidden('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),k4_waybel_0('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_5'('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ m1_subset_1('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ m1_subset_1(k4_waybel_0('#skF_8','#skF_9'),k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_orders_2('#skF_8')
    | ~ r2_hidden('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_13083,c_5290])).

tff(c_13092,plain,
    ( r2_hidden('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),k4_waybel_0('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_5'('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),'#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12878,c_56,c_54,c_5686,c_12877,c_13085])).

tff(c_13097,plain,(
    ~ m1_subset_1('#skF_5'('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),'#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_13092])).

tff(c_13101,plain,
    ( ~ r2_hidden('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0('#skF_8')))
    | ~ l1_orders_2('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_13097])).

tff(c_13107,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_12878,c_13101])).

tff(c_13109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_13107])).

tff(c_13110,plain,(
    r2_hidden('#skF_4'('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),'#skF_8','#skF_9'),k4_waybel_0('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_13092])).

tff(c_13200,plain,(
    r2_hidden('#skF_6'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13190,c_13110])).

tff(c_13298,plain,
    ( r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9'))
    | k4_waybel_0('#skF_8','#skF_9') = a_2_1_waybel_0('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_13200,c_46])).

tff(c_13310,plain,(
    r2_hidden('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),k4_waybel_0('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_13298])).

tff(c_5703,plain,(
    ! [A_103] :
      ( m1_subset_1(A_103,u1_struct_0('#skF_8'))
      | ~ r2_hidden(A_103,k4_waybel_0('#skF_8','#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_5686,c_50])).

tff(c_13316,plain,(
    m1_subset_1('#skF_7'(k4_waybel_0('#skF_8','#skF_9'),a_2_1_waybel_0('#skF_8','#skF_9')),u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_13310,c_5703])).

tff(c_13326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12463,c_13316])).

%------------------------------------------------------------------------------
