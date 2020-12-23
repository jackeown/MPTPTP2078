%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:29 EST 2020

% Result     : Theorem 5.85s
% Output     : CNFRefutation 6.07s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 191 expanded)
%              Number of leaves         :   37 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :  181 ( 479 expanded)
%              Number of equality atoms :   21 (  81 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_145,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_1_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_84,axiom,(
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

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_50,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_48,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_46,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_44,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_28,plain,(
    ! [A_34] :
      ( l1_struct_0(A_34)
      | ~ l1_orders_2(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_66,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_71,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_orders_2(A_53) ) ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_75,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_200,plain,(
    ! [A_104,B_105] :
      ( k2_orders_2(A_104,B_105) = a_2_1_orders_2(A_104,B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_orders_2(A_104)
      | ~ v5_orders_2(A_104)
      | ~ v4_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_211,plain,(
    ! [B_105] :
      ( k2_orders_2('#skF_4',B_105) = a_2_1_orders_2('#skF_4',B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_200])).

tff(c_219,plain,(
    ! [B_105] :
      ( k2_orders_2('#skF_4',B_105) = a_2_1_orders_2('#skF_4',B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_211])).

tff(c_222,plain,(
    ! [B_106] :
      ( k2_orders_2('#skF_4',B_106) = a_2_1_orders_2('#skF_4',B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_219])).

tff(c_237,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_53,c_222])).

tff(c_42,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_238,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_42])).

tff(c_10,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3416,plain,(
    ! [A_356,B_357,C_358] :
      ( m1_subset_1('#skF_2'(A_356,B_357,C_358),u1_struct_0(B_357))
      | ~ r2_hidden(A_356,a_2_1_orders_2(B_357,C_358))
      | ~ m1_subset_1(C_358,k1_zfmisc_1(u1_struct_0(B_357)))
      | ~ l1_orders_2(B_357)
      | ~ v5_orders_2(B_357)
      | ~ v4_orders_2(B_357)
      | ~ v3_orders_2(B_357)
      | v2_struct_0(B_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3421,plain,(
    ! [A_356,C_358] :
      ( m1_subset_1('#skF_2'(A_356,'#skF_4',C_358),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_356,a_2_1_orders_2('#skF_4',C_358))
      | ~ m1_subset_1(C_358,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_3416])).

tff(c_3424,plain,(
    ! [A_356,C_358] :
      ( m1_subset_1('#skF_2'(A_356,'#skF_4',C_358),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_356,a_2_1_orders_2('#skF_4',C_358))
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_75,c_3421])).

tff(c_3425,plain,(
    ! [A_356,C_358] :
      ( m1_subset_1('#skF_2'(A_356,'#skF_4',C_358),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_356,a_2_1_orders_2('#skF_4',C_358))
      | ~ m1_subset_1(C_358,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3424])).

tff(c_80,plain,(
    ! [A_54] :
      ( ~ v1_xboole_0(u1_struct_0(A_54))
      | ~ l1_struct_0(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_83,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_80])).

tff(c_84,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_83])).

tff(c_85,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_89,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_85])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_89])).

tff(c_94,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3813,plain,(
    ! [B_396,A_397,C_398,E_399] :
      ( r2_orders_2(B_396,'#skF_2'(A_397,B_396,C_398),E_399)
      | ~ r2_hidden(E_399,C_398)
      | ~ m1_subset_1(E_399,u1_struct_0(B_396))
      | ~ r2_hidden(A_397,a_2_1_orders_2(B_396,C_398))
      | ~ m1_subset_1(C_398,k1_zfmisc_1(u1_struct_0(B_396)))
      | ~ l1_orders_2(B_396)
      | ~ v5_orders_2(B_396)
      | ~ v4_orders_2(B_396)
      | ~ v3_orders_2(B_396)
      | v2_struct_0(B_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3821,plain,(
    ! [A_397,C_398,E_399] :
      ( r2_orders_2('#skF_4','#skF_2'(A_397,'#skF_4',C_398),E_399)
      | ~ r2_hidden(E_399,C_398)
      | ~ m1_subset_1(E_399,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_397,a_2_1_orders_2('#skF_4',C_398))
      | ~ m1_subset_1(C_398,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_3813])).

tff(c_3828,plain,(
    ! [A_397,C_398,E_399] :
      ( r2_orders_2('#skF_4','#skF_2'(A_397,'#skF_4',C_398),E_399)
      | ~ r2_hidden(E_399,C_398)
      | ~ m1_subset_1(E_399,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_397,a_2_1_orders_2('#skF_4',C_398))
      | ~ m1_subset_1(C_398,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_75,c_3821])).

tff(c_3834,plain,(
    ! [A_406,C_407,E_408] :
      ( r2_orders_2('#skF_4','#skF_2'(A_406,'#skF_4',C_407),E_408)
      | ~ r2_hidden(E_408,C_407)
      | ~ m1_subset_1(E_408,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_406,a_2_1_orders_2('#skF_4',C_407))
      | ~ m1_subset_1(C_407,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3828])).

tff(c_3856,plain,(
    ! [A_409,E_410] :
      ( r2_orders_2('#skF_4','#skF_2'(A_409,'#skF_4',k2_struct_0('#skF_4')),E_410)
      | ~ r2_hidden(E_410,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_410,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_409,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_53,c_3834])).

tff(c_22,plain,(
    ! [A_24,C_30] :
      ( ~ r2_orders_2(A_24,C_30,C_30)
      | ~ m1_subset_1(C_30,u1_struct_0(A_24))
      | ~ l1_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_3864,plain,(
    ! [A_409] :
      ( ~ m1_subset_1('#skF_2'(A_409,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_409,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_409,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_409,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_3856,c_22])).

tff(c_3875,plain,(
    ! [A_411] :
      ( ~ r2_hidden('#skF_2'(A_411,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_411,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_411,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_75,c_3864])).

tff(c_3878,plain,(
    ! [A_411] :
      ( ~ r2_hidden(A_411,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v1_xboole_0(k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_411,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_3875])).

tff(c_3882,plain,(
    ! [A_412] :
      ( ~ r2_hidden(A_412,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_412,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_3878])).

tff(c_3886,plain,(
    ! [A_356] :
      ( ~ r2_hidden(A_356,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_3425,c_3882])).

tff(c_3894,plain,(
    ! [A_413] : ~ r2_hidden(A_413,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_3886])).

tff(c_3902,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_3894])).

tff(c_3907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_3902])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n012.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 13:00:37 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.85/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.85/2.11  
% 5.85/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.07/2.12  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k3_mcart_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 6.07/2.12  
% 6.07/2.12  %Foreground sorts:
% 6.07/2.12  
% 6.07/2.12  
% 6.07/2.12  %Background operators:
% 6.07/2.12  
% 6.07/2.12  
% 6.07/2.12  %Foreground operators:
% 6.07/2.12  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.07/2.12  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.07/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.07/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.07/2.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.07/2.12  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 6.07/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.07/2.12  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 6.07/2.12  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 6.07/2.12  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 6.07/2.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.07/2.12  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.07/2.12  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.07/2.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.07/2.12  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.07/2.12  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.07/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.07/2.12  tff('#skF_4', type, '#skF_4': $i).
% 6.07/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.07/2.12  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 6.07/2.12  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.07/2.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.07/2.12  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.07/2.12  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.07/2.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.07/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.07/2.12  
% 6.07/2.13  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.07/2.13  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.07/2.13  tff(f_145, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 6.07/2.13  tff(f_104, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 6.07/2.13  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 6.07/2.13  tff(f_100, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 6.07/2.13  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 6.07/2.13  tff(f_131, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 6.07/2.13  tff(f_69, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.07/2.13  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 6.07/2.13  tff(f_84, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 6.07/2.13  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.07/2.13  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.07/2.13  tff(c_53, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 6.07/2.13  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.07/2.13  tff(c_50, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.07/2.13  tff(c_48, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.07/2.13  tff(c_46, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.07/2.13  tff(c_44, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.07/2.13  tff(c_28, plain, (![A_34]: (l1_struct_0(A_34) | ~l1_orders_2(A_34))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.07/2.13  tff(c_66, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.07/2.13  tff(c_71, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_orders_2(A_53))), inference(resolution, [status(thm)], [c_28, c_66])).
% 6.07/2.13  tff(c_75, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_71])).
% 6.07/2.13  tff(c_200, plain, (![A_104, B_105]: (k2_orders_2(A_104, B_105)=a_2_1_orders_2(A_104, B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_orders_2(A_104) | ~v5_orders_2(A_104) | ~v4_orders_2(A_104) | ~v3_orders_2(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.07/2.13  tff(c_211, plain, (![B_105]: (k2_orders_2('#skF_4', B_105)=a_2_1_orders_2('#skF_4', B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_200])).
% 6.07/2.13  tff(c_219, plain, (![B_105]: (k2_orders_2('#skF_4', B_105)=a_2_1_orders_2('#skF_4', B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_211])).
% 6.07/2.13  tff(c_222, plain, (![B_106]: (k2_orders_2('#skF_4', B_106)=a_2_1_orders_2('#skF_4', B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_219])).
% 6.07/2.13  tff(c_237, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_53, c_222])).
% 6.07/2.13  tff(c_42, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.07/2.13  tff(c_238, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_237, c_42])).
% 6.07/2.13  tff(c_10, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.07/2.13  tff(c_3416, plain, (![A_356, B_357, C_358]: (m1_subset_1('#skF_2'(A_356, B_357, C_358), u1_struct_0(B_357)) | ~r2_hidden(A_356, a_2_1_orders_2(B_357, C_358)) | ~m1_subset_1(C_358, k1_zfmisc_1(u1_struct_0(B_357))) | ~l1_orders_2(B_357) | ~v5_orders_2(B_357) | ~v4_orders_2(B_357) | ~v3_orders_2(B_357) | v2_struct_0(B_357))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.07/2.13  tff(c_3421, plain, (![A_356, C_358]: (m1_subset_1('#skF_2'(A_356, '#skF_4', C_358), k2_struct_0('#skF_4')) | ~r2_hidden(A_356, a_2_1_orders_2('#skF_4', C_358)) | ~m1_subset_1(C_358, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_3416])).
% 6.07/2.13  tff(c_3424, plain, (![A_356, C_358]: (m1_subset_1('#skF_2'(A_356, '#skF_4', C_358), k2_struct_0('#skF_4')) | ~r2_hidden(A_356, a_2_1_orders_2('#skF_4', C_358)) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_75, c_3421])).
% 6.07/2.13  tff(c_3425, plain, (![A_356, C_358]: (m1_subset_1('#skF_2'(A_356, '#skF_4', C_358), k2_struct_0('#skF_4')) | ~r2_hidden(A_356, a_2_1_orders_2('#skF_4', C_358)) | ~m1_subset_1(C_358, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_3424])).
% 6.07/2.13  tff(c_80, plain, (![A_54]: (~v1_xboole_0(u1_struct_0(A_54)) | ~l1_struct_0(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.07/2.13  tff(c_83, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_75, c_80])).
% 6.07/2.13  tff(c_84, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_52, c_83])).
% 6.07/2.13  tff(c_85, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_84])).
% 6.07/2.13  tff(c_89, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_28, c_85])).
% 6.07/2.13  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_89])).
% 6.07/2.13  tff(c_94, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_84])).
% 6.07/2.13  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.07/2.13  tff(c_3813, plain, (![B_396, A_397, C_398, E_399]: (r2_orders_2(B_396, '#skF_2'(A_397, B_396, C_398), E_399) | ~r2_hidden(E_399, C_398) | ~m1_subset_1(E_399, u1_struct_0(B_396)) | ~r2_hidden(A_397, a_2_1_orders_2(B_396, C_398)) | ~m1_subset_1(C_398, k1_zfmisc_1(u1_struct_0(B_396))) | ~l1_orders_2(B_396) | ~v5_orders_2(B_396) | ~v4_orders_2(B_396) | ~v3_orders_2(B_396) | v2_struct_0(B_396))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.07/2.13  tff(c_3821, plain, (![A_397, C_398, E_399]: (r2_orders_2('#skF_4', '#skF_2'(A_397, '#skF_4', C_398), E_399) | ~r2_hidden(E_399, C_398) | ~m1_subset_1(E_399, u1_struct_0('#skF_4')) | ~r2_hidden(A_397, a_2_1_orders_2('#skF_4', C_398)) | ~m1_subset_1(C_398, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_3813])).
% 6.07/2.13  tff(c_3828, plain, (![A_397, C_398, E_399]: (r2_orders_2('#skF_4', '#skF_2'(A_397, '#skF_4', C_398), E_399) | ~r2_hidden(E_399, C_398) | ~m1_subset_1(E_399, k2_struct_0('#skF_4')) | ~r2_hidden(A_397, a_2_1_orders_2('#skF_4', C_398)) | ~m1_subset_1(C_398, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_75, c_3821])).
% 6.07/2.13  tff(c_3834, plain, (![A_406, C_407, E_408]: (r2_orders_2('#skF_4', '#skF_2'(A_406, '#skF_4', C_407), E_408) | ~r2_hidden(E_408, C_407) | ~m1_subset_1(E_408, k2_struct_0('#skF_4')) | ~r2_hidden(A_406, a_2_1_orders_2('#skF_4', C_407)) | ~m1_subset_1(C_407, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_52, c_3828])).
% 6.07/2.13  tff(c_3856, plain, (![A_409, E_410]: (r2_orders_2('#skF_4', '#skF_2'(A_409, '#skF_4', k2_struct_0('#skF_4')), E_410) | ~r2_hidden(E_410, k2_struct_0('#skF_4')) | ~m1_subset_1(E_410, k2_struct_0('#skF_4')) | ~r2_hidden(A_409, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_53, c_3834])).
% 6.07/2.13  tff(c_22, plain, (![A_24, C_30]: (~r2_orders_2(A_24, C_30, C_30) | ~m1_subset_1(C_30, u1_struct_0(A_24)) | ~l1_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.07/2.13  tff(c_3864, plain, (![A_409]: (~m1_subset_1('#skF_2'(A_409, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_409, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_409, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_409, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_3856, c_22])).
% 6.07/2.13  tff(c_3875, plain, (![A_411]: (~r2_hidden('#skF_2'(A_411, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_411, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_411, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_75, c_3864])).
% 6.07/2.13  tff(c_3878, plain, (![A_411]: (~r2_hidden(A_411, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_411, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_3875])).
% 6.07/2.13  tff(c_3882, plain, (![A_412]: (~r2_hidden(A_412, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_412, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_94, c_3878])).
% 6.07/2.13  tff(c_3886, plain, (![A_356]: (~r2_hidden(A_356, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_3425, c_3882])).
% 6.07/2.13  tff(c_3894, plain, (![A_413]: (~r2_hidden(A_413, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_3886])).
% 6.07/2.13  tff(c_3902, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_3894])).
% 6.07/2.13  tff(c_3907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_3902])).
% 6.07/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.07/2.13  
% 6.07/2.13  Inference rules
% 6.07/2.13  ----------------------
% 6.07/2.13  #Ref     : 0
% 6.07/2.13  #Sup     : 827
% 6.07/2.13  #Fact    : 0
% 6.07/2.13  #Define  : 0
% 6.07/2.13  #Split   : 28
% 6.07/2.13  #Chain   : 0
% 6.07/2.13  #Close   : 0
% 6.07/2.13  
% 6.07/2.13  Ordering : KBO
% 6.07/2.13  
% 6.07/2.13  Simplification rules
% 6.07/2.13  ----------------------
% 6.07/2.13  #Subsume      : 65
% 6.07/2.13  #Demod        : 865
% 6.07/2.13  #Tautology    : 230
% 6.07/2.13  #SimpNegUnit  : 125
% 6.07/2.13  #BackRed      : 36
% 6.07/2.13  
% 6.07/2.13  #Partial instantiations: 0
% 6.07/2.13  #Strategies tried      : 1
% 6.07/2.13  
% 6.07/2.13  Timing (in seconds)
% 6.07/2.13  ----------------------
% 6.07/2.13  Preprocessing        : 0.34
% 6.07/2.14  Parsing              : 0.18
% 6.07/2.14  CNF conversion       : 0.02
% 6.07/2.14  Main loop            : 1.05
% 6.07/2.14  Inferencing          : 0.35
% 6.07/2.14  Reduction            : 0.33
% 6.07/2.14  Demodulation         : 0.23
% 6.07/2.14  BG Simplification    : 0.05
% 6.07/2.14  Subsumption          : 0.23
% 6.07/2.14  Abstraction          : 0.06
% 6.07/2.14  MUC search           : 0.00
% 6.07/2.14  Cooper               : 0.00
% 6.07/2.14  Total                : 1.41
% 6.07/2.14  Index Insertion      : 0.00
% 6.07/2.14  Index Deletion       : 0.00
% 6.07/2.14  Index Matching       : 0.00
% 6.07/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
