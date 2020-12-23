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
% DateTime   : Thu Dec  3 10:19:28 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 365 expanded)
%              Number of leaves         :   35 ( 143 expanded)
%              Depth                    :   17
%              Number of atoms          :  213 ( 954 expanded)
%              Number of equality atoms :   18 ( 160 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_103,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_149,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_87,axiom,(
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

tff(f_118,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(c_48,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_32,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_58,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = k2_struct_0(A_37)
      | ~ l1_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_63,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_orders_2(A_38) ) ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_67,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_63])).

tff(c_76,plain,(
    ! [A_40] :
      ( ~ v1_xboole_0(u1_struct_0(A_40))
      | ~ l1_struct_0(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_82,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_76])).

tff(c_84,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_82])).

tff(c_85,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_88,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_85])).

tff(c_92,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_88])).

tff(c_94,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_106,plain,(
    ! [A_45] :
      ( m1_subset_1(k2_struct_0(A_45),k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_112,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_106])).

tff(c_115,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_112])).

tff(c_54,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_52,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_50,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_215,plain,(
    ! [A_72,B_73] :
      ( k2_orders_2(A_72,B_73) = a_2_1_orders_2(A_72,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_233,plain,(
    ! [B_73] :
      ( k2_orders_2('#skF_4',B_73) = a_2_1_orders_2('#skF_4',B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_215])).

tff(c_239,plain,(
    ! [B_73] :
      ( k2_orders_2('#skF_4',B_73) = a_2_1_orders_2('#skF_4',B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_233])).

tff(c_260,plain,(
    ! [B_76] :
      ( k2_orders_2('#skF_4',B_76) = a_2_1_orders_2('#skF_4',B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_239])).

tff(c_280,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_115,c_260])).

tff(c_46,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_282,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_46])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | k1_xboole_0 = B_4
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_540,plain,(
    ! [A_84,B_85,C_86] :
      ( m1_subset_1('#skF_2'(A_84,B_85,C_86),u1_struct_0(B_85))
      | ~ r2_hidden(A_84,a_2_1_orders_2(B_85,C_86))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0(B_85)))
      | ~ l1_orders_2(B_85)
      | ~ v5_orders_2(B_85)
      | ~ v4_orders_2(B_85)
      | ~ v3_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_548,plain,(
    ! [A_84,C_86] :
      ( m1_subset_1('#skF_2'(A_84,'#skF_4',C_86),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_84,a_2_1_orders_2('#skF_4',C_86))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_540])).

tff(c_552,plain,(
    ! [A_84,C_86] :
      ( m1_subset_1('#skF_2'(A_84,'#skF_4',C_86),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_84,a_2_1_orders_2('#skF_4',C_86))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_67,c_548])).

tff(c_553,plain,(
    ! [A_84,C_86] :
      ( m1_subset_1('#skF_2'(A_84,'#skF_4',C_86),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_84,a_2_1_orders_2('#skF_4',C_86))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_552])).

tff(c_93,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2612,plain,(
    ! [B_195,A_196,C_197,E_198] :
      ( r2_orders_2(B_195,'#skF_2'(A_196,B_195,C_197),E_198)
      | ~ r2_hidden(E_198,C_197)
      | ~ m1_subset_1(E_198,u1_struct_0(B_195))
      | ~ r2_hidden(A_196,a_2_1_orders_2(B_195,C_197))
      | ~ m1_subset_1(C_197,k1_zfmisc_1(u1_struct_0(B_195)))
      | ~ l1_orders_2(B_195)
      | ~ v5_orders_2(B_195)
      | ~ v4_orders_2(B_195)
      | ~ v3_orders_2(B_195)
      | v2_struct_0(B_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_2627,plain,(
    ! [A_196,C_197,E_198] :
      ( r2_orders_2('#skF_4','#skF_2'(A_196,'#skF_4',C_197),E_198)
      | ~ r2_hidden(E_198,C_197)
      | ~ m1_subset_1(E_198,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_196,a_2_1_orders_2('#skF_4',C_197))
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_2612])).

tff(c_2634,plain,(
    ! [A_196,C_197,E_198] :
      ( r2_orders_2('#skF_4','#skF_2'(A_196,'#skF_4',C_197),E_198)
      | ~ r2_hidden(E_198,C_197)
      | ~ m1_subset_1(E_198,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_196,a_2_1_orders_2('#skF_4',C_197))
      | ~ m1_subset_1(C_197,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_67,c_2627])).

tff(c_2636,plain,(
    ! [A_199,C_200,E_201] :
      ( r2_orders_2('#skF_4','#skF_2'(A_199,'#skF_4',C_200),E_201)
      | ~ r2_hidden(E_201,C_200)
      | ~ m1_subset_1(E_201,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_199,a_2_1_orders_2('#skF_4',C_200))
      | ~ m1_subset_1(C_200,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_2634])).

tff(c_2675,plain,(
    ! [A_202,E_203] :
      ( r2_orders_2('#skF_4','#skF_2'(A_202,'#skF_4',k2_struct_0('#skF_4')),E_203)
      | ~ r2_hidden(E_203,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_203,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_202,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_115,c_2636])).

tff(c_24,plain,(
    ! [A_10,C_16] :
      ( ~ r2_orders_2(A_10,C_16,C_16)
      | ~ m1_subset_1(C_16,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2683,plain,(
    ! [A_202] :
      ( ~ m1_subset_1('#skF_2'(A_202,'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_2'(A_202,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_202,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_202,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_2675,c_24])).

tff(c_2694,plain,(
    ! [A_204] :
      ( ~ r2_hidden('#skF_2'(A_204,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_2'(A_204,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_204,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_67,c_2683])).

tff(c_2697,plain,(
    ! [A_204] :
      ( ~ r2_hidden(A_204,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_204,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
      | v1_xboole_0(k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4,c_2694])).

tff(c_2727,plain,(
    ! [A_206] :
      ( ~ r2_hidden(A_206,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'(A_206,'#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_2697])).

tff(c_2734,plain,(
    ! [A_84] :
      ( ~ r2_hidden(A_84,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_553,c_2727])).

tff(c_2745,plain,(
    ! [A_207] : ~ r2_hidden(A_207,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_2734])).

tff(c_2749,plain,(
    ! [A_3] :
      ( a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0
      | ~ m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_10,c_2745])).

tff(c_2756,plain,(
    ! [A_3] : ~ m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(A_3)) ),
    inference(negUnitSimplification,[status(thm)],[c_282,c_2749])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k2_orders_2(A_20,B_21),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_orders_2(A_20)
      | ~ v5_orders_2(A_20)
      | ~ v4_orders_2(A_20)
      | ~ v3_orders_2(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_286,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_30])).

tff(c_290,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_115,c_67,c_67,c_286])).

tff(c_291,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_290])).

tff(c_2759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2756,c_291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.89  
% 4.82/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.90  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.82/1.90  
% 4.82/1.90  %Foreground sorts:
% 4.82/1.90  
% 4.82/1.90  
% 4.82/1.90  %Background operators:
% 4.82/1.90  
% 4.82/1.90  
% 4.82/1.90  %Foreground operators:
% 4.82/1.90  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.82/1.90  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.82/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.82/1.90  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.82/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.82/1.90  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 4.82/1.90  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 4.82/1.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.82/1.90  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.82/1.90  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.82/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.82/1.90  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.82/1.90  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.82/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.90  tff('#skF_4', type, '#skF_4': $i).
% 4.82/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.90  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 4.82/1.90  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.82/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.82/1.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.82/1.90  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.82/1.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.82/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.82/1.90  
% 4.82/1.91  tff(f_163, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 4.82/1.91  tff(f_122, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 4.82/1.91  tff(f_54, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.82/1.91  tff(f_72, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.82/1.91  tff(f_58, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 4.82/1.91  tff(f_103, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 4.82/1.91  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 4.82/1.91  tff(f_149, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 4.82/1.91  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.82/1.91  tff(f_87, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 4.82/1.91  tff(f_118, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 4.82/1.91  tff(c_48, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.82/1.91  tff(c_32, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.82/1.91  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.82/1.91  tff(c_58, plain, (![A_37]: (u1_struct_0(A_37)=k2_struct_0(A_37) | ~l1_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.82/1.91  tff(c_63, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_orders_2(A_38))), inference(resolution, [status(thm)], [c_32, c_58])).
% 4.82/1.91  tff(c_67, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_63])).
% 4.82/1.91  tff(c_76, plain, (![A_40]: (~v1_xboole_0(u1_struct_0(A_40)) | ~l1_struct_0(A_40) | v2_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.82/1.91  tff(c_82, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_67, c_76])).
% 4.82/1.91  tff(c_84, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_82])).
% 4.82/1.91  tff(c_85, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_84])).
% 4.82/1.91  tff(c_88, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_32, c_85])).
% 4.82/1.91  tff(c_92, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_88])).
% 4.82/1.91  tff(c_94, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 4.82/1.91  tff(c_106, plain, (![A_45]: (m1_subset_1(k2_struct_0(A_45), k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.82/1.91  tff(c_112, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_67, c_106])).
% 4.82/1.91  tff(c_115, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_112])).
% 4.82/1.91  tff(c_54, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.82/1.91  tff(c_52, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.82/1.91  tff(c_50, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.82/1.91  tff(c_215, plain, (![A_72, B_73]: (k2_orders_2(A_72, B_73)=a_2_1_orders_2(A_72, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.82/1.91  tff(c_233, plain, (![B_73]: (k2_orders_2('#skF_4', B_73)=a_2_1_orders_2('#skF_4', B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_215])).
% 4.82/1.91  tff(c_239, plain, (![B_73]: (k2_orders_2('#skF_4', B_73)=a_2_1_orders_2('#skF_4', B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_233])).
% 4.82/1.91  tff(c_260, plain, (![B_76]: (k2_orders_2('#skF_4', B_76)=a_2_1_orders_2('#skF_4', B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_239])).
% 4.82/1.91  tff(c_280, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_115, c_260])).
% 4.82/1.91  tff(c_46, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.82/1.91  tff(c_282, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_280, c_46])).
% 4.82/1.91  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | k1_xboole_0=B_4 | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.82/1.91  tff(c_540, plain, (![A_84, B_85, C_86]: (m1_subset_1('#skF_2'(A_84, B_85, C_86), u1_struct_0(B_85)) | ~r2_hidden(A_84, a_2_1_orders_2(B_85, C_86)) | ~m1_subset_1(C_86, k1_zfmisc_1(u1_struct_0(B_85))) | ~l1_orders_2(B_85) | ~v5_orders_2(B_85) | ~v4_orders_2(B_85) | ~v3_orders_2(B_85) | v2_struct_0(B_85))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.82/1.91  tff(c_548, plain, (![A_84, C_86]: (m1_subset_1('#skF_2'(A_84, '#skF_4', C_86), k2_struct_0('#skF_4')) | ~r2_hidden(A_84, a_2_1_orders_2('#skF_4', C_86)) | ~m1_subset_1(C_86, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_540])).
% 4.82/1.91  tff(c_552, plain, (![A_84, C_86]: (m1_subset_1('#skF_2'(A_84, '#skF_4', C_86), k2_struct_0('#skF_4')) | ~r2_hidden(A_84, a_2_1_orders_2('#skF_4', C_86)) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_67, c_548])).
% 4.82/1.91  tff(c_553, plain, (![A_84, C_86]: (m1_subset_1('#skF_2'(A_84, '#skF_4', C_86), k2_struct_0('#skF_4')) | ~r2_hidden(A_84, a_2_1_orders_2('#skF_4', C_86)) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_552])).
% 4.82/1.91  tff(c_93, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_84])).
% 4.82/1.91  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.82/1.91  tff(c_2612, plain, (![B_195, A_196, C_197, E_198]: (r2_orders_2(B_195, '#skF_2'(A_196, B_195, C_197), E_198) | ~r2_hidden(E_198, C_197) | ~m1_subset_1(E_198, u1_struct_0(B_195)) | ~r2_hidden(A_196, a_2_1_orders_2(B_195, C_197)) | ~m1_subset_1(C_197, k1_zfmisc_1(u1_struct_0(B_195))) | ~l1_orders_2(B_195) | ~v5_orders_2(B_195) | ~v4_orders_2(B_195) | ~v3_orders_2(B_195) | v2_struct_0(B_195))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.82/1.91  tff(c_2627, plain, (![A_196, C_197, E_198]: (r2_orders_2('#skF_4', '#skF_2'(A_196, '#skF_4', C_197), E_198) | ~r2_hidden(E_198, C_197) | ~m1_subset_1(E_198, u1_struct_0('#skF_4')) | ~r2_hidden(A_196, a_2_1_orders_2('#skF_4', C_197)) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_2612])).
% 4.82/1.91  tff(c_2634, plain, (![A_196, C_197, E_198]: (r2_orders_2('#skF_4', '#skF_2'(A_196, '#skF_4', C_197), E_198) | ~r2_hidden(E_198, C_197) | ~m1_subset_1(E_198, k2_struct_0('#skF_4')) | ~r2_hidden(A_196, a_2_1_orders_2('#skF_4', C_197)) | ~m1_subset_1(C_197, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_67, c_2627])).
% 4.82/1.91  tff(c_2636, plain, (![A_199, C_200, E_201]: (r2_orders_2('#skF_4', '#skF_2'(A_199, '#skF_4', C_200), E_201) | ~r2_hidden(E_201, C_200) | ~m1_subset_1(E_201, k2_struct_0('#skF_4')) | ~r2_hidden(A_199, a_2_1_orders_2('#skF_4', C_200)) | ~m1_subset_1(C_200, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_56, c_2634])).
% 4.82/1.91  tff(c_2675, plain, (![A_202, E_203]: (r2_orders_2('#skF_4', '#skF_2'(A_202, '#skF_4', k2_struct_0('#skF_4')), E_203) | ~r2_hidden(E_203, k2_struct_0('#skF_4')) | ~m1_subset_1(E_203, k2_struct_0('#skF_4')) | ~r2_hidden(A_202, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_115, c_2636])).
% 4.82/1.91  tff(c_24, plain, (![A_10, C_16]: (~r2_orders_2(A_10, C_16, C_16) | ~m1_subset_1(C_16, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.82/1.91  tff(c_2683, plain, (![A_202]: (~m1_subset_1('#skF_2'(A_202, '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_2'(A_202, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_202, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_202, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_2675, c_24])).
% 4.82/1.91  tff(c_2694, plain, (![A_204]: (~r2_hidden('#skF_2'(A_204, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'(A_204, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~r2_hidden(A_204, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_67, c_2683])).
% 4.82/1.91  tff(c_2697, plain, (![A_204]: (~r2_hidden(A_204, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_204, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | v1_xboole_0(k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_4, c_2694])).
% 4.82/1.91  tff(c_2727, plain, (![A_206]: (~r2_hidden(A_206, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1('#skF_2'(A_206, '#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_93, c_2697])).
% 4.82/1.91  tff(c_2734, plain, (![A_84]: (~r2_hidden(A_84, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_553, c_2727])).
% 4.82/1.91  tff(c_2745, plain, (![A_207]: (~r2_hidden(A_207, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_2734])).
% 4.82/1.91  tff(c_2749, plain, (![A_3]: (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0 | ~m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_10, c_2745])).
% 4.82/1.91  tff(c_2756, plain, (![A_3]: (~m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(A_3)))), inference(negUnitSimplification, [status(thm)], [c_282, c_2749])).
% 4.82/1.91  tff(c_30, plain, (![A_20, B_21]: (m1_subset_1(k2_orders_2(A_20, B_21), k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_21, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_orders_2(A_20) | ~v5_orders_2(A_20) | ~v4_orders_2(A_20) | ~v3_orders_2(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.82/1.91  tff(c_286, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_280, c_30])).
% 4.82/1.91  tff(c_290, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_115, c_67, c_67, c_286])).
% 4.82/1.91  tff(c_291, plain, (m1_subset_1(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_290])).
% 4.82/1.91  tff(c_2759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2756, c_291])).
% 4.82/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.91  
% 4.82/1.91  Inference rules
% 4.82/1.91  ----------------------
% 4.82/1.91  #Ref     : 0
% 4.82/1.91  #Sup     : 607
% 4.82/1.91  #Fact    : 0
% 4.82/1.91  #Define  : 0
% 4.82/1.91  #Split   : 4
% 4.82/1.91  #Chain   : 0
% 4.82/1.91  #Close   : 0
% 4.82/1.91  
% 4.82/1.91  Ordering : KBO
% 4.82/1.91  
% 4.82/1.91  Simplification rules
% 4.82/1.91  ----------------------
% 4.82/1.91  #Subsume      : 86
% 4.82/1.91  #Demod        : 900
% 4.82/1.91  #Tautology    : 145
% 4.82/1.91  #SimpNegUnit  : 97
% 4.82/1.91  #BackRed      : 23
% 4.82/1.91  
% 4.82/1.91  #Partial instantiations: 0
% 4.82/1.91  #Strategies tried      : 1
% 4.82/1.91  
% 4.82/1.91  Timing (in seconds)
% 4.82/1.91  ----------------------
% 5.12/1.91  Preprocessing        : 0.35
% 5.12/1.91  Parsing              : 0.19
% 5.12/1.91  CNF conversion       : 0.02
% 5.12/1.91  Main loop            : 0.78
% 5.12/1.91  Inferencing          : 0.27
% 5.12/1.91  Reduction            : 0.25
% 5.12/1.91  Demodulation         : 0.17
% 5.12/1.91  BG Simplification    : 0.04
% 5.12/1.91  Subsumption          : 0.16
% 5.12/1.91  Abstraction          : 0.05
% 5.12/1.92  MUC search           : 0.00
% 5.12/1.92  Cooper               : 0.00
% 5.12/1.92  Total                : 1.17
% 5.12/1.92  Index Insertion      : 0.00
% 5.12/1.92  Index Deletion       : 0.00
% 5.12/1.92  Index Matching       : 0.00
% 5.12/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
