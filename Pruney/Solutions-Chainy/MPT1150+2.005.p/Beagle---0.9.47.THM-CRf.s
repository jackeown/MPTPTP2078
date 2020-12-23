%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:24 EST 2020

% Result     : Theorem 9.27s
% Output     : CNFRefutation 9.27s
% Verified   : 
% Statistics : Number of formulae       :  105 (1017 expanded)
%              Number of leaves         :   37 ( 393 expanded)
%              Depth                    :   21
%              Number of atoms          :  278 (3156 expanded)
%              Number of equality atoms :   41 ( 592 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k4_mcart_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_168,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_73,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_154,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,E,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_40,plain,(
    ! [A_47] :
      ( l1_struct_0(A_47)
      | ~ l1_orders_2(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_76,plain,(
    ! [A_68] :
      ( u1_struct_0(A_68) = k2_struct_0(A_68)
      | ~ l1_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_88,plain,(
    ! [A_70] :
      ( u1_struct_0(A_70) = k2_struct_0(A_70)
      | ~ l1_orders_2(A_70) ) ),
    inference(resolution,[status(thm)],[c_40,c_76])).

tff(c_92,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_88])).

tff(c_62,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_60,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_58,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_326,plain,(
    ! [A_129,B_130] :
      ( k1_orders_2(A_129,B_130) = a_2_0_orders_2(A_129,B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_orders_2(A_129)
      | ~ v5_orders_2(A_129)
      | ~ v4_orders_2(A_129)
      | ~ v3_orders_2(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_333,plain,(
    ! [B_130] :
      ( k1_orders_2('#skF_4',B_130) = a_2_0_orders_2('#skF_4',B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_326])).

tff(c_344,plain,(
    ! [B_130] :
      ( k1_orders_2('#skF_4',B_130) = a_2_0_orders_2('#skF_4',B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_333])).

tff(c_374,plain,(
    ! [B_133] :
      ( k1_orders_2('#skF_4',B_133) = a_2_0_orders_2('#skF_4',B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_344])).

tff(c_394,plain,(
    ! [A_134] :
      ( k1_orders_2('#skF_4',A_134) = a_2_0_orders_2('#skF_4',A_134)
      | ~ r1_tarski(A_134,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_16,c_374])).

tff(c_408,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_394])).

tff(c_54,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_411,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_54])).

tff(c_22,plain,(
    ! [A_16] :
      ( r2_hidden('#skF_1'(A_16),A_16)
      | k1_xboole_0 = A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_118,plain,(
    ! [C_77,A_78,B_79] :
      ( r2_hidden(C_77,A_78)
      | ~ r2_hidden(C_77,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_167,plain,(
    ! [A_98,A_99] :
      ( r2_hidden('#skF_1'(A_98),A_99)
      | ~ m1_subset_1(A_98,k1_zfmisc_1(A_99))
      | k1_xboole_0 = A_98 ) ),
    inference(resolution,[status(thm)],[c_22,c_118])).

tff(c_10,plain,(
    ! [C_7,A_4,B_5] :
      ( r2_hidden(C_7,A_4)
      | ~ r2_hidden(C_7,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3310,plain,(
    ! [A_313,A_314,A_315] :
      ( r2_hidden('#skF_1'(A_313),A_314)
      | ~ m1_subset_1(A_315,k1_zfmisc_1(A_314))
      | ~ m1_subset_1(A_313,k1_zfmisc_1(A_315))
      | k1_xboole_0 = A_313 ) ),
    inference(resolution,[status(thm)],[c_167,c_10])).

tff(c_3349,plain,(
    ! [A_316,B_317,A_318] :
      ( r2_hidden('#skF_1'(A_316),B_317)
      | ~ m1_subset_1(A_316,k1_zfmisc_1(A_318))
      | k1_xboole_0 = A_316
      | ~ r1_tarski(A_318,B_317) ) ),
    inference(resolution,[status(thm)],[c_16,c_3310])).

tff(c_3699,plain,(
    ! [A_329,B_330,B_331] :
      ( r2_hidden('#skF_1'(A_329),B_330)
      | k1_xboole_0 = A_329
      | ~ r1_tarski(B_331,B_330)
      | ~ r1_tarski(A_329,B_331) ) ),
    inference(resolution,[status(thm)],[c_16,c_3349])).

tff(c_3725,plain,(
    ! [A_329,B_2] :
      ( r2_hidden('#skF_1'(A_329),B_2)
      | k1_xboole_0 = A_329
      | ~ r1_tarski(A_329,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_3699])).

tff(c_442,plain,(
    ! [A_139,B_140] :
      ( m1_subset_1(k1_orders_2(A_139,B_140),k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_orders_2(A_139)
      | ~ v5_orders_2(A_139)
      | ~ v4_orders_2(A_139)
      | ~ v3_orders_2(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_453,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_442])).

tff(c_464,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_92,c_92,c_453])).

tff(c_465,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_464])).

tff(c_656,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_465])).

tff(c_659,plain,(
    ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_16,c_656])).

tff(c_663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_659])).

tff(c_665,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_596,plain,(
    ! [A_145,B_146,C_147] :
      ( '#skF_2'(A_145,B_146,C_147) = A_145
      | ~ r2_hidden(A_145,a_2_0_orders_2(B_146,C_147))
      | ~ m1_subset_1(C_147,k1_zfmisc_1(u1_struct_0(B_146)))
      | ~ l1_orders_2(B_146)
      | ~ v5_orders_2(B_146)
      | ~ v4_orders_2(B_146)
      | ~ v3_orders_2(B_146)
      | v2_struct_0(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_5521,plain,(
    ! [B_408,C_409] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2(B_408,C_409)),B_408,C_409) = '#skF_1'(a_2_0_orders_2(B_408,C_409))
      | ~ m1_subset_1(C_409,k1_zfmisc_1(u1_struct_0(B_408)))
      | ~ l1_orders_2(B_408)
      | ~ v5_orders_2(B_408)
      | ~ v4_orders_2(B_408)
      | ~ v3_orders_2(B_408)
      | v2_struct_0(B_408)
      | a_2_0_orders_2(B_408,C_409) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_596])).

tff(c_5540,plain,(
    ! [C_409] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_409)),'#skF_4',C_409) = '#skF_1'(a_2_0_orders_2('#skF_4',C_409))
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_0_orders_2('#skF_4',C_409) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_5521])).

tff(c_5554,plain,(
    ! [C_409] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_409)),'#skF_4',C_409) = '#skF_1'(a_2_0_orders_2('#skF_4',C_409))
      | ~ m1_subset_1(C_409,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_0_orders_2('#skF_4',C_409) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_56,c_5540])).

tff(c_5693,plain,(
    ! [C_415] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_415)),'#skF_4',C_415) = '#skF_1'(a_2_0_orders_2('#skF_4',C_415))
      | ~ m1_subset_1(C_415,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_0_orders_2('#skF_4',C_415) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5554])).

tff(c_5713,plain,
    ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_665,c_5693])).

tff(c_5741,plain,(
    '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_411,c_5713])).

tff(c_3285,plain,(
    ! [B_309,E_310,A_311,C_312] :
      ( r2_orders_2(B_309,E_310,'#skF_2'(A_311,B_309,C_312))
      | ~ r2_hidden(E_310,C_312)
      | ~ m1_subset_1(E_310,u1_struct_0(B_309))
      | ~ r2_hidden(A_311,a_2_0_orders_2(B_309,C_312))
      | ~ m1_subset_1(C_312,k1_zfmisc_1(u1_struct_0(B_309)))
      | ~ l1_orders_2(B_309)
      | ~ v5_orders_2(B_309)
      | ~ v4_orders_2(B_309)
      | ~ v3_orders_2(B_309)
      | v2_struct_0(B_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_3308,plain,(
    ! [B_309,E_310,A_311,A_9] :
      ( r2_orders_2(B_309,E_310,'#skF_2'(A_311,B_309,A_9))
      | ~ r2_hidden(E_310,A_9)
      | ~ m1_subset_1(E_310,u1_struct_0(B_309))
      | ~ r2_hidden(A_311,a_2_0_orders_2(B_309,A_9))
      | ~ l1_orders_2(B_309)
      | ~ v5_orders_2(B_309)
      | ~ v4_orders_2(B_309)
      | ~ v3_orders_2(B_309)
      | v2_struct_0(B_309)
      | ~ r1_tarski(A_9,u1_struct_0(B_309)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3285])).

tff(c_6731,plain,(
    ! [E_310] :
      ( r2_orders_2('#skF_4',E_310,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_310,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_310,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(k2_struct_0('#skF_4'),u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5741,c_3308])).

tff(c_6741,plain,(
    ! [E_310] :
      ( r2_orders_2('#skF_4',E_310,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_310,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_310,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_92,c_62,c_60,c_58,c_56,c_92,c_6731])).

tff(c_6742,plain,(
    ! [E_310] :
      ( r2_orders_2('#skF_4',E_310,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_310,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_310,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_6741])).

tff(c_8914,plain,(
    ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_6742])).

tff(c_8920,plain,
    ( a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0
    | ~ r1_tarski(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_3725,c_8914])).

tff(c_8933,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8920])).

tff(c_8935,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_411,c_8933])).

tff(c_8937,plain,(
    r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_6742])).

tff(c_664,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_465])).

tff(c_18,plain,(
    ! [A_11,C_13,B_12] :
      ( m1_subset_1(A_11,C_13)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(C_13))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_807,plain,(
    ! [A_156] :
      ( m1_subset_1(A_156,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_156,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_664,c_18])).

tff(c_815,plain,
    ( m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_807])).

tff(c_819,plain,(
    m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_411,c_815])).

tff(c_3353,plain,(
    ! [B_317] :
      ( r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),B_317)
      | a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0
      | ~ r1_tarski(k2_struct_0('#skF_4'),B_317) ) ),
    inference(resolution,[status(thm)],[c_664,c_3349])).

tff(c_3614,plain,(
    ! [B_327] :
      ( r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),B_327)
      | ~ r1_tarski(k2_struct_0('#skF_4'),B_327) ) ),
    inference(negUnitSimplification,[status(thm)],[c_411,c_3353])).

tff(c_8605,plain,(
    ! [A_531,B_532] :
      ( r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),A_531)
      | ~ m1_subset_1(B_532,k1_zfmisc_1(A_531))
      | ~ r1_tarski(k2_struct_0('#skF_4'),B_532) ) ),
    inference(resolution,[status(thm)],[c_3614,c_10])).

tff(c_8640,plain,
    ( r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_665,c_8605])).

tff(c_8675,plain,(
    r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8640])).

tff(c_5929,plain,(
    ! [B_421,E_422,A_423,A_424] :
      ( r2_orders_2(B_421,E_422,'#skF_2'(A_423,B_421,A_424))
      | ~ r2_hidden(E_422,A_424)
      | ~ m1_subset_1(E_422,u1_struct_0(B_421))
      | ~ r2_hidden(A_423,a_2_0_orders_2(B_421,A_424))
      | ~ l1_orders_2(B_421)
      | ~ v5_orders_2(B_421)
      | ~ v4_orders_2(B_421)
      | ~ v3_orders_2(B_421)
      | v2_struct_0(B_421)
      | ~ r1_tarski(A_424,u1_struct_0(B_421)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3285])).

tff(c_32,plain,(
    ! [A_35,C_41] :
      ( ~ r2_orders_2(A_35,C_41,C_41)
      | ~ m1_subset_1(C_41,u1_struct_0(A_35))
      | ~ l1_orders_2(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_12081,plain,(
    ! [A_665,B_666,A_667] :
      ( ~ r2_hidden('#skF_2'(A_665,B_666,A_667),A_667)
      | ~ m1_subset_1('#skF_2'(A_665,B_666,A_667),u1_struct_0(B_666))
      | ~ r2_hidden(A_665,a_2_0_orders_2(B_666,A_667))
      | ~ l1_orders_2(B_666)
      | ~ v5_orders_2(B_666)
      | ~ v4_orders_2(B_666)
      | ~ v3_orders_2(B_666)
      | v2_struct_0(B_666)
      | ~ r1_tarski(A_667,u1_struct_0(B_666)) ) ),
    inference(resolution,[status(thm)],[c_5929,c_32])).

tff(c_12099,plain,
    ( ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5741,c_12081])).

tff(c_12116,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_92,c_62,c_60,c_58,c_56,c_8937,c_819,c_92,c_5741,c_8675,c_12099])).

tff(c_12118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_12116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:02:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.27/3.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.27/3.51  
% 9.27/3.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.27/3.52  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k4_mcart_1 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 9.27/3.52  
% 9.27/3.52  %Foreground sorts:
% 9.27/3.52  
% 9.27/3.52  
% 9.27/3.52  %Background operators:
% 9.27/3.52  
% 9.27/3.52  
% 9.27/3.52  %Foreground operators:
% 9.27/3.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.27/3.52  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 9.27/3.52  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 9.27/3.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.27/3.52  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 9.27/3.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.27/3.52  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.27/3.52  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 9.27/3.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.27/3.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.27/3.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.27/3.52  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 9.27/3.52  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 9.27/3.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.27/3.52  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.27/3.52  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 9.27/3.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.27/3.52  tff('#skF_4', type, '#skF_4': $i).
% 9.27/3.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.27/3.52  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 9.27/3.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.27/3.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.27/3.52  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 9.27/3.52  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.27/3.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.27/3.52  
% 9.27/3.53  tff(f_168, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_orders_2)).
% 9.27/3.53  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.27/3.53  tff(f_127, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 9.27/3.53  tff(f_77, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 9.27/3.53  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.27/3.53  tff(f_108, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 9.27/3.53  tff(f_73, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 9.27/3.53  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 9.27/3.53  tff(f_123, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 9.27/3.53  tff(f_154, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 9.27/3.53  tff(f_52, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 9.27/3.53  tff(f_92, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 9.27/3.53  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.27/3.53  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.27/3.53  tff(c_56, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.27/3.53  tff(c_40, plain, (![A_47]: (l1_struct_0(A_47) | ~l1_orders_2(A_47))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.27/3.53  tff(c_76, plain, (![A_68]: (u1_struct_0(A_68)=k2_struct_0(A_68) | ~l1_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.27/3.53  tff(c_88, plain, (![A_70]: (u1_struct_0(A_70)=k2_struct_0(A_70) | ~l1_orders_2(A_70))), inference(resolution, [status(thm)], [c_40, c_76])).
% 9.27/3.53  tff(c_92, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_88])).
% 9.27/3.53  tff(c_62, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.27/3.53  tff(c_60, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.27/3.53  tff(c_58, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.27/3.53  tff(c_16, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.27/3.53  tff(c_326, plain, (![A_129, B_130]: (k1_orders_2(A_129, B_130)=a_2_0_orders_2(A_129, B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_orders_2(A_129) | ~v5_orders_2(A_129) | ~v4_orders_2(A_129) | ~v3_orders_2(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_108])).
% 9.27/3.53  tff(c_333, plain, (![B_130]: (k1_orders_2('#skF_4', B_130)=a_2_0_orders_2('#skF_4', B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_92, c_326])).
% 9.27/3.53  tff(c_344, plain, (![B_130]: (k1_orders_2('#skF_4', B_130)=a_2_0_orders_2('#skF_4', B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_333])).
% 9.27/3.53  tff(c_374, plain, (![B_133]: (k1_orders_2('#skF_4', B_133)=a_2_0_orders_2('#skF_4', B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_344])).
% 9.27/3.53  tff(c_394, plain, (![A_134]: (k1_orders_2('#skF_4', A_134)=a_2_0_orders_2('#skF_4', A_134) | ~r1_tarski(A_134, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_16, c_374])).
% 9.27/3.53  tff(c_408, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_394])).
% 9.27/3.53  tff(c_54, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_168])).
% 9.27/3.53  tff(c_411, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_408, c_54])).
% 9.27/3.53  tff(c_22, plain, (![A_16]: (r2_hidden('#skF_1'(A_16), A_16) | k1_xboole_0=A_16)), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.27/3.53  tff(c_118, plain, (![C_77, A_78, B_79]: (r2_hidden(C_77, A_78) | ~r2_hidden(C_77, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.27/3.53  tff(c_167, plain, (![A_98, A_99]: (r2_hidden('#skF_1'(A_98), A_99) | ~m1_subset_1(A_98, k1_zfmisc_1(A_99)) | k1_xboole_0=A_98)), inference(resolution, [status(thm)], [c_22, c_118])).
% 9.27/3.53  tff(c_10, plain, (![C_7, A_4, B_5]: (r2_hidden(C_7, A_4) | ~r2_hidden(C_7, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.27/3.53  tff(c_3310, plain, (![A_313, A_314, A_315]: (r2_hidden('#skF_1'(A_313), A_314) | ~m1_subset_1(A_315, k1_zfmisc_1(A_314)) | ~m1_subset_1(A_313, k1_zfmisc_1(A_315)) | k1_xboole_0=A_313)), inference(resolution, [status(thm)], [c_167, c_10])).
% 9.27/3.53  tff(c_3349, plain, (![A_316, B_317, A_318]: (r2_hidden('#skF_1'(A_316), B_317) | ~m1_subset_1(A_316, k1_zfmisc_1(A_318)) | k1_xboole_0=A_316 | ~r1_tarski(A_318, B_317))), inference(resolution, [status(thm)], [c_16, c_3310])).
% 9.27/3.53  tff(c_3699, plain, (![A_329, B_330, B_331]: (r2_hidden('#skF_1'(A_329), B_330) | k1_xboole_0=A_329 | ~r1_tarski(B_331, B_330) | ~r1_tarski(A_329, B_331))), inference(resolution, [status(thm)], [c_16, c_3349])).
% 9.27/3.53  tff(c_3725, plain, (![A_329, B_2]: (r2_hidden('#skF_1'(A_329), B_2) | k1_xboole_0=A_329 | ~r1_tarski(A_329, B_2))), inference(resolution, [status(thm)], [c_6, c_3699])).
% 9.27/3.53  tff(c_442, plain, (![A_139, B_140]: (m1_subset_1(k1_orders_2(A_139, B_140), k1_zfmisc_1(u1_struct_0(A_139))) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_orders_2(A_139) | ~v5_orders_2(A_139) | ~v4_orders_2(A_139) | ~v3_orders_2(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_123])).
% 9.27/3.53  tff(c_453, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_408, c_442])).
% 9.27/3.53  tff(c_464, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_92, c_92, c_453])).
% 9.27/3.53  tff(c_465, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_464])).
% 9.27/3.53  tff(c_656, plain, (~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_465])).
% 9.27/3.53  tff(c_659, plain, (~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_656])).
% 9.27/3.53  tff(c_663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_659])).
% 9.27/3.53  tff(c_665, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_465])).
% 9.27/3.53  tff(c_596, plain, (![A_145, B_146, C_147]: ('#skF_2'(A_145, B_146, C_147)=A_145 | ~r2_hidden(A_145, a_2_0_orders_2(B_146, C_147)) | ~m1_subset_1(C_147, k1_zfmisc_1(u1_struct_0(B_146))) | ~l1_orders_2(B_146) | ~v5_orders_2(B_146) | ~v4_orders_2(B_146) | ~v3_orders_2(B_146) | v2_struct_0(B_146))), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.27/3.53  tff(c_5521, plain, (![B_408, C_409]: ('#skF_2'('#skF_1'(a_2_0_orders_2(B_408, C_409)), B_408, C_409)='#skF_1'(a_2_0_orders_2(B_408, C_409)) | ~m1_subset_1(C_409, k1_zfmisc_1(u1_struct_0(B_408))) | ~l1_orders_2(B_408) | ~v5_orders_2(B_408) | ~v4_orders_2(B_408) | ~v3_orders_2(B_408) | v2_struct_0(B_408) | a_2_0_orders_2(B_408, C_409)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_596])).
% 9.27/3.53  tff(c_5540, plain, (![C_409]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_409)), '#skF_4', C_409)='#skF_1'(a_2_0_orders_2('#skF_4', C_409)) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_0_orders_2('#skF_4', C_409)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_92, c_5521])).
% 9.27/3.53  tff(c_5554, plain, (![C_409]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_409)), '#skF_4', C_409)='#skF_1'(a_2_0_orders_2('#skF_4', C_409)) | ~m1_subset_1(C_409, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_0_orders_2('#skF_4', C_409)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_56, c_5540])).
% 9.27/3.53  tff(c_5693, plain, (![C_415]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_415)), '#skF_4', C_415)='#skF_1'(a_2_0_orders_2('#skF_4', C_415)) | ~m1_subset_1(C_415, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_0_orders_2('#skF_4', C_415)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_64, c_5554])).
% 9.27/3.53  tff(c_5713, plain, ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_665, c_5693])).
% 9.27/3.53  tff(c_5741, plain, ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_411, c_5713])).
% 9.27/3.53  tff(c_3285, plain, (![B_309, E_310, A_311, C_312]: (r2_orders_2(B_309, E_310, '#skF_2'(A_311, B_309, C_312)) | ~r2_hidden(E_310, C_312) | ~m1_subset_1(E_310, u1_struct_0(B_309)) | ~r2_hidden(A_311, a_2_0_orders_2(B_309, C_312)) | ~m1_subset_1(C_312, k1_zfmisc_1(u1_struct_0(B_309))) | ~l1_orders_2(B_309) | ~v5_orders_2(B_309) | ~v4_orders_2(B_309) | ~v3_orders_2(B_309) | v2_struct_0(B_309))), inference(cnfTransformation, [status(thm)], [f_154])).
% 9.27/3.53  tff(c_3308, plain, (![B_309, E_310, A_311, A_9]: (r2_orders_2(B_309, E_310, '#skF_2'(A_311, B_309, A_9)) | ~r2_hidden(E_310, A_9) | ~m1_subset_1(E_310, u1_struct_0(B_309)) | ~r2_hidden(A_311, a_2_0_orders_2(B_309, A_9)) | ~l1_orders_2(B_309) | ~v5_orders_2(B_309) | ~v4_orders_2(B_309) | ~v3_orders_2(B_309) | v2_struct_0(B_309) | ~r1_tarski(A_9, u1_struct_0(B_309)))), inference(resolution, [status(thm)], [c_16, c_3285])).
% 9.27/3.53  tff(c_6731, plain, (![E_310]: (r2_orders_2('#skF_4', E_310, '#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | ~r2_hidden(E_310, k2_struct_0('#skF_4')) | ~m1_subset_1(E_310, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5741, c_3308])).
% 9.27/3.53  tff(c_6741, plain, (![E_310]: (r2_orders_2('#skF_4', E_310, '#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | ~r2_hidden(E_310, k2_struct_0('#skF_4')) | ~m1_subset_1(E_310, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_92, c_62, c_60, c_58, c_56, c_92, c_6731])).
% 9.27/3.53  tff(c_6742, plain, (![E_310]: (r2_orders_2('#skF_4', E_310, '#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | ~r2_hidden(E_310, k2_struct_0('#skF_4')) | ~m1_subset_1(E_310, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_64, c_6741])).
% 9.27/3.53  tff(c_8914, plain, (~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_6742])).
% 9.27/3.53  tff(c_8920, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0 | ~r1_tarski(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_3725, c_8914])).
% 9.27/3.53  tff(c_8933, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8920])).
% 9.27/3.53  tff(c_8935, plain, $false, inference(negUnitSimplification, [status(thm)], [c_411, c_8933])).
% 9.27/3.53  tff(c_8937, plain, (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_6742])).
% 9.27/3.53  tff(c_664, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_465])).
% 9.27/3.53  tff(c_18, plain, (![A_11, C_13, B_12]: (m1_subset_1(A_11, C_13) | ~m1_subset_1(B_12, k1_zfmisc_1(C_13)) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.27/3.53  tff(c_807, plain, (![A_156]: (m1_subset_1(A_156, k2_struct_0('#skF_4')) | ~r2_hidden(A_156, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_664, c_18])).
% 9.27/3.53  tff(c_815, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_807])).
% 9.27/3.53  tff(c_819, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_411, c_815])).
% 9.27/3.53  tff(c_3353, plain, (![B_317]: (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), B_317) | a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0 | ~r1_tarski(k2_struct_0('#skF_4'), B_317))), inference(resolution, [status(thm)], [c_664, c_3349])).
% 9.27/3.53  tff(c_3614, plain, (![B_327]: (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), B_327) | ~r1_tarski(k2_struct_0('#skF_4'), B_327))), inference(negUnitSimplification, [status(thm)], [c_411, c_3353])).
% 9.27/3.53  tff(c_8605, plain, (![A_531, B_532]: (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), A_531) | ~m1_subset_1(B_532, k1_zfmisc_1(A_531)) | ~r1_tarski(k2_struct_0('#skF_4'), B_532))), inference(resolution, [status(thm)], [c_3614, c_10])).
% 9.27/3.53  tff(c_8640, plain, (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_665, c_8605])).
% 9.27/3.53  tff(c_8675, plain, (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8640])).
% 9.27/3.53  tff(c_5929, plain, (![B_421, E_422, A_423, A_424]: (r2_orders_2(B_421, E_422, '#skF_2'(A_423, B_421, A_424)) | ~r2_hidden(E_422, A_424) | ~m1_subset_1(E_422, u1_struct_0(B_421)) | ~r2_hidden(A_423, a_2_0_orders_2(B_421, A_424)) | ~l1_orders_2(B_421) | ~v5_orders_2(B_421) | ~v4_orders_2(B_421) | ~v3_orders_2(B_421) | v2_struct_0(B_421) | ~r1_tarski(A_424, u1_struct_0(B_421)))), inference(resolution, [status(thm)], [c_16, c_3285])).
% 9.27/3.53  tff(c_32, plain, (![A_35, C_41]: (~r2_orders_2(A_35, C_41, C_41) | ~m1_subset_1(C_41, u1_struct_0(A_35)) | ~l1_orders_2(A_35))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.27/3.53  tff(c_12081, plain, (![A_665, B_666, A_667]: (~r2_hidden('#skF_2'(A_665, B_666, A_667), A_667) | ~m1_subset_1('#skF_2'(A_665, B_666, A_667), u1_struct_0(B_666)) | ~r2_hidden(A_665, a_2_0_orders_2(B_666, A_667)) | ~l1_orders_2(B_666) | ~v5_orders_2(B_666) | ~v4_orders_2(B_666) | ~v3_orders_2(B_666) | v2_struct_0(B_666) | ~r1_tarski(A_667, u1_struct_0(B_666)))), inference(resolution, [status(thm)], [c_5929, c_32])).
% 9.27/3.53  tff(c_12099, plain, (~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5741, c_12081])).
% 9.27/3.53  tff(c_12116, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_92, c_62, c_60, c_58, c_56, c_8937, c_819, c_92, c_5741, c_8675, c_12099])).
% 9.27/3.53  tff(c_12118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_12116])).
% 9.27/3.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.27/3.53  
% 9.27/3.53  Inference rules
% 9.27/3.53  ----------------------
% 9.27/3.53  #Ref     : 0
% 9.27/3.53  #Sup     : 2659
% 9.27/3.53  #Fact    : 0
% 9.27/3.53  #Define  : 0
% 9.27/3.53  #Split   : 33
% 9.27/3.53  #Chain   : 0
% 9.27/3.53  #Close   : 0
% 9.27/3.53  
% 9.27/3.53  Ordering : KBO
% 9.27/3.53  
% 9.27/3.53  Simplification rules
% 9.27/3.53  ----------------------
% 9.27/3.53  #Subsume      : 663
% 9.27/3.53  #Demod        : 1881
% 9.27/3.53  #Tautology    : 384
% 9.27/3.53  #SimpNegUnit  : 274
% 9.27/3.53  #BackRed      : 91
% 9.27/3.53  
% 9.27/3.53  #Partial instantiations: 0
% 9.27/3.53  #Strategies tried      : 1
% 9.27/3.53  
% 9.27/3.53  Timing (in seconds)
% 9.27/3.53  ----------------------
% 9.27/3.54  Preprocessing        : 0.37
% 9.27/3.54  Parsing              : 0.20
% 9.27/3.54  CNF conversion       : 0.03
% 9.27/3.54  Main loop            : 2.37
% 9.27/3.54  Inferencing          : 0.58
% 9.27/3.54  Reduction            : 0.74
% 9.27/3.54  Demodulation         : 0.47
% 9.27/3.54  BG Simplification    : 0.07
% 9.27/3.54  Subsumption          : 0.80
% 9.27/3.54  Abstraction          : 0.10
% 9.27/3.54  MUC search           : 0.00
% 9.27/3.54  Cooper               : 0.00
% 9.27/3.54  Total                : 2.78
% 9.27/3.54  Index Insertion      : 0.00
% 9.27/3.54  Index Deletion       : 0.00
% 9.27/3.54  Index Matching       : 0.00
% 9.27/3.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
