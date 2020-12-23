%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:28 EST 2020

% Result     : Theorem 7.05s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :   95 (1158 expanded)
%              Number of leaves         :   35 ( 417 expanded)
%              Depth                    :   19
%              Number of atoms          :  229 (3263 expanded)
%              Number of equality atoms :   31 ( 618 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_101,axiom,(
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

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_132,axiom,(
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

tff(f_85,axiom,(
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

tff(c_46,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_30,plain,(
    ! [A_26] :
      ( l1_struct_0(A_26)
      | ~ l1_orders_2(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_57,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_63,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_orders_2(A_45) ) ),
    inference(resolution,[status(thm)],[c_30,c_57])).

tff(c_67,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_63])).

tff(c_77,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(u1_struct_0(A_48))
      | ~ l1_struct_0(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_80,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_77])).

tff(c_81,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_80])).

tff(c_82,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_90,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_82])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_90])).

tff(c_95,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_96,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_112,plain,(
    ! [A_55] :
      ( m1_subset_1(k2_struct_0(A_55),k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_118,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_112])).

tff(c_121,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_118])).

tff(c_52,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_50,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_173,plain,(
    ! [A_82,B_83] :
      ( k2_orders_2(A_82,B_83) = a_2_1_orders_2(A_82,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_183,plain,(
    ! [B_83] :
      ( k2_orders_2('#skF_4',B_83) = a_2_1_orders_2('#skF_4',B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_173])).

tff(c_191,plain,(
    ! [B_83] :
      ( k2_orders_2('#skF_4',B_83) = a_2_1_orders_2('#skF_4',B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_183])).

tff(c_194,plain,(
    ! [B_84] :
      ( k2_orders_2('#skF_4',B_84) = a_2_1_orders_2('#skF_4',B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_191])).

tff(c_209,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_121,c_194])).

tff(c_44,plain,(
    k2_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_211,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_44])).

tff(c_10,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2606,plain,(
    ! [A_308,B_309,C_310] :
      ( '#skF_2'(A_308,B_309,C_310) = A_308
      | ~ r2_hidden(A_308,a_2_1_orders_2(B_309,C_310))
      | ~ m1_subset_1(C_310,k1_zfmisc_1(u1_struct_0(B_309)))
      | ~ l1_orders_2(B_309)
      | ~ v5_orders_2(B_309)
      | ~ v4_orders_2(B_309)
      | ~ v3_orders_2(B_309)
      | v2_struct_0(B_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4004,plain,(
    ! [B_470,C_471] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2(B_470,C_471)),B_470,C_471) = '#skF_1'(a_2_1_orders_2(B_470,C_471))
      | ~ m1_subset_1(C_471,k1_zfmisc_1(u1_struct_0(B_470)))
      | ~ l1_orders_2(B_470)
      | ~ v5_orders_2(B_470)
      | ~ v4_orders_2(B_470)
      | ~ v3_orders_2(B_470)
      | v2_struct_0(B_470)
      | a_2_1_orders_2(B_470,C_471) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_2606])).

tff(c_4011,plain,(
    ! [C_471] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_471)),'#skF_4',C_471) = '#skF_1'(a_2_1_orders_2('#skF_4',C_471))
      | ~ m1_subset_1(C_471,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_471) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_4004])).

tff(c_4018,plain,(
    ! [C_471] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_471)),'#skF_4',C_471) = '#skF_1'(a_2_1_orders_2('#skF_4',C_471))
      | ~ m1_subset_1(C_471,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_1_orders_2('#skF_4',C_471) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_4011])).

tff(c_4021,plain,(
    ! [C_472] :
      ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',C_472)),'#skF_4',C_472) = '#skF_1'(a_2_1_orders_2('#skF_4',C_472))
      | ~ m1_subset_1(C_472,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_1_orders_2('#skF_4',C_472) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4018])).

tff(c_4026,plain,
    ( '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_121,c_4021])).

tff(c_4035,plain,(
    '#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_4026])).

tff(c_3800,plain,(
    ! [A_431,B_432,C_433] :
      ( m1_subset_1('#skF_2'(A_431,B_432,C_433),u1_struct_0(B_432))
      | ~ r2_hidden(A_431,a_2_1_orders_2(B_432,C_433))
      | ~ m1_subset_1(C_433,k1_zfmisc_1(u1_struct_0(B_432)))
      | ~ l1_orders_2(B_432)
      | ~ v5_orders_2(B_432)
      | ~ v4_orders_2(B_432)
      | ~ v3_orders_2(B_432)
      | v2_struct_0(B_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3810,plain,(
    ! [A_431,C_433] :
      ( m1_subset_1('#skF_2'(A_431,'#skF_4',C_433),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_431,a_2_1_orders_2('#skF_4',C_433))
      | ~ m1_subset_1(C_433,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_3800])).

tff(c_3815,plain,(
    ! [A_431,C_433] :
      ( m1_subset_1('#skF_2'(A_431,'#skF_4',C_433),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_431,a_2_1_orders_2('#skF_4',C_433))
      | ~ m1_subset_1(C_433,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_67,c_3810])).

tff(c_3816,plain,(
    ! [A_431,C_433] :
      ( m1_subset_1('#skF_2'(A_431,'#skF_4',C_433),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_431,a_2_1_orders_2('#skF_4',C_433))
      | ~ m1_subset_1(C_433,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_3815])).

tff(c_4040,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_4035,c_3816])).

tff(c_4047,plain,
    ( m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_4040])).

tff(c_4052,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_4047])).

tff(c_4058,plain,(
    a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_4052])).

tff(c_4064,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_4058])).

tff(c_4065,plain,(
    m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4047])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r2_hidden(B_2,A_1)
      | ~ m1_subset_1(B_2,A_1)
      | v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4066,plain,(
    r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_4047])).

tff(c_4168,plain,(
    ! [B_481,A_482,C_483,E_484] :
      ( r2_orders_2(B_481,'#skF_2'(A_482,B_481,C_483),E_484)
      | ~ r2_hidden(E_484,C_483)
      | ~ m1_subset_1(E_484,u1_struct_0(B_481))
      | ~ r2_hidden(A_482,a_2_1_orders_2(B_481,C_483))
      | ~ m1_subset_1(C_483,k1_zfmisc_1(u1_struct_0(B_481)))
      | ~ l1_orders_2(B_481)
      | ~ v5_orders_2(B_481)
      | ~ v4_orders_2(B_481)
      | ~ v3_orders_2(B_481)
      | v2_struct_0(B_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_4175,plain,(
    ! [A_482,C_483,E_484] :
      ( r2_orders_2('#skF_4','#skF_2'(A_482,'#skF_4',C_483),E_484)
      | ~ r2_hidden(E_484,C_483)
      | ~ m1_subset_1(E_484,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_482,a_2_1_orders_2('#skF_4',C_483))
      | ~ m1_subset_1(C_483,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_4168])).

tff(c_4182,plain,(
    ! [A_482,C_483,E_484] :
      ( r2_orders_2('#skF_4','#skF_2'(A_482,'#skF_4',C_483),E_484)
      | ~ r2_hidden(E_484,C_483)
      | ~ m1_subset_1(E_484,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_482,a_2_1_orders_2('#skF_4',C_483))
      | ~ m1_subset_1(C_483,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_46,c_67,c_4175])).

tff(c_4223,plain,(
    ! [A_485,C_486,E_487] :
      ( r2_orders_2('#skF_4','#skF_2'(A_485,'#skF_4',C_486),E_487)
      | ~ r2_hidden(E_487,C_486)
      | ~ m1_subset_1(E_487,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_485,a_2_1_orders_2('#skF_4',C_486))
      | ~ m1_subset_1(C_486,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4182])).

tff(c_4382,plain,(
    ! [A_501,E_502] :
      ( r2_orders_2('#skF_4','#skF_2'(A_501,'#skF_4',k2_struct_0('#skF_4')),E_502)
      | ~ r2_hidden(E_502,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_502,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_501,a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_121,c_4223])).

tff(c_4393,plain,(
    ! [E_502] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_502)
      | ~ r2_hidden(E_502,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_502,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4035,c_4382])).

tff(c_4406,plain,(
    ! [E_503] :
      ( r2_orders_2('#skF_4','#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),E_503)
      | ~ r2_hidden(E_503,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_503,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4066,c_4393])).

tff(c_24,plain,(
    ! [A_16,C_22] :
      ( ~ r2_orders_2(A_16,C_22,C_22)
      | ~ m1_subset_1(C_22,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4414,plain,
    ( ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),u1_struct_0('#skF_4'))
    | ~ l1_orders_2('#skF_4')
    | ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4406,c_24])).

tff(c_4424,plain,(
    ~ r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4065,c_46,c_4065,c_67,c_4414])).

tff(c_4427,plain,
    ( ~ m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_4424])).

tff(c_4430,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4065,c_4427])).

tff(c_4432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_4430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:51:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.05/2.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.43  
% 7.05/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.43  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k4_tarski > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 7.05/2.43  
% 7.05/2.43  %Foreground sorts:
% 7.05/2.43  
% 7.05/2.43  
% 7.05/2.43  %Background operators:
% 7.05/2.43  
% 7.05/2.43  
% 7.05/2.43  %Foreground operators:
% 7.05/2.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.05/2.43  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.05/2.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.05/2.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.05/2.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.05/2.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.05/2.43  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.05/2.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.05/2.43  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 7.05/2.43  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 7.05/2.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.05/2.43  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.05/2.43  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.05/2.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.05/2.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.05/2.43  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.05/2.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.05/2.43  tff('#skF_4', type, '#skF_4': $i).
% 7.05/2.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.05/2.43  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 7.05/2.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 7.05/2.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.05/2.43  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.05/2.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.05/2.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.05/2.43  
% 7.05/2.45  tff(f_146, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_orders_2)).
% 7.05/2.45  tff(f_105, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 7.05/2.45  tff(f_58, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 7.05/2.45  tff(f_70, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 7.05/2.45  tff(f_62, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 7.05/2.45  tff(f_101, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 7.05/2.45  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 7.05/2.45  tff(f_132, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 7.05/2.45  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 7.05/2.45  tff(f_85, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 7.05/2.45  tff(c_46, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.05/2.45  tff(c_30, plain, (![A_26]: (l1_struct_0(A_26) | ~l1_orders_2(A_26))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.05/2.45  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.05/2.45  tff(c_57, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.05/2.45  tff(c_63, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_orders_2(A_45))), inference(resolution, [status(thm)], [c_30, c_57])).
% 7.05/2.45  tff(c_67, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_63])).
% 7.05/2.45  tff(c_77, plain, (![A_48]: (~v1_xboole_0(u1_struct_0(A_48)) | ~l1_struct_0(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.05/2.45  tff(c_80, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_67, c_77])).
% 7.05/2.45  tff(c_81, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_80])).
% 7.05/2.45  tff(c_82, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_81])).
% 7.05/2.45  tff(c_90, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_30, c_82])).
% 7.05/2.45  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_90])).
% 7.05/2.45  tff(c_95, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_81])).
% 7.05/2.45  tff(c_96, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_81])).
% 7.05/2.45  tff(c_112, plain, (![A_55]: (m1_subset_1(k2_struct_0(A_55), k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.05/2.45  tff(c_118, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_67, c_112])).
% 7.05/2.45  tff(c_121, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_118])).
% 7.05/2.45  tff(c_52, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.05/2.45  tff(c_50, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.05/2.45  tff(c_48, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.05/2.45  tff(c_173, plain, (![A_82, B_83]: (k2_orders_2(A_82, B_83)=a_2_1_orders_2(A_82, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.05/2.45  tff(c_183, plain, (![B_83]: (k2_orders_2('#skF_4', B_83)=a_2_1_orders_2('#skF_4', B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_173])).
% 7.05/2.45  tff(c_191, plain, (![B_83]: (k2_orders_2('#skF_4', B_83)=a_2_1_orders_2('#skF_4', B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_183])).
% 7.05/2.45  tff(c_194, plain, (![B_84]: (k2_orders_2('#skF_4', B_84)=a_2_1_orders_2('#skF_4', B_84) | ~m1_subset_1(B_84, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_191])).
% 7.05/2.45  tff(c_209, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_121, c_194])).
% 7.05/2.45  tff(c_44, plain, (k2_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.05/2.45  tff(c_211, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_209, c_44])).
% 7.05/2.45  tff(c_10, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.05/2.45  tff(c_2606, plain, (![A_308, B_309, C_310]: ('#skF_2'(A_308, B_309, C_310)=A_308 | ~r2_hidden(A_308, a_2_1_orders_2(B_309, C_310)) | ~m1_subset_1(C_310, k1_zfmisc_1(u1_struct_0(B_309))) | ~l1_orders_2(B_309) | ~v5_orders_2(B_309) | ~v4_orders_2(B_309) | ~v3_orders_2(B_309) | v2_struct_0(B_309))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.05/2.45  tff(c_4004, plain, (![B_470, C_471]: ('#skF_2'('#skF_1'(a_2_1_orders_2(B_470, C_471)), B_470, C_471)='#skF_1'(a_2_1_orders_2(B_470, C_471)) | ~m1_subset_1(C_471, k1_zfmisc_1(u1_struct_0(B_470))) | ~l1_orders_2(B_470) | ~v5_orders_2(B_470) | ~v4_orders_2(B_470) | ~v3_orders_2(B_470) | v2_struct_0(B_470) | a_2_1_orders_2(B_470, C_471)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_2606])).
% 7.05/2.45  tff(c_4011, plain, (![C_471]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_471)), '#skF_4', C_471)='#skF_1'(a_2_1_orders_2('#skF_4', C_471)) | ~m1_subset_1(C_471, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_471)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_67, c_4004])).
% 7.05/2.45  tff(c_4018, plain, (![C_471]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_471)), '#skF_4', C_471)='#skF_1'(a_2_1_orders_2('#skF_4', C_471)) | ~m1_subset_1(C_471, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_1_orders_2('#skF_4', C_471)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_4011])).
% 7.05/2.45  tff(c_4021, plain, (![C_472]: ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', C_472)), '#skF_4', C_472)='#skF_1'(a_2_1_orders_2('#skF_4', C_472)) | ~m1_subset_1(C_472, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', C_472)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_4018])).
% 7.05/2.45  tff(c_4026, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_121, c_4021])).
% 7.05/2.45  tff(c_4035, plain, ('#skF_2'('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_211, c_4026])).
% 7.05/2.45  tff(c_3800, plain, (![A_431, B_432, C_433]: (m1_subset_1('#skF_2'(A_431, B_432, C_433), u1_struct_0(B_432)) | ~r2_hidden(A_431, a_2_1_orders_2(B_432, C_433)) | ~m1_subset_1(C_433, k1_zfmisc_1(u1_struct_0(B_432))) | ~l1_orders_2(B_432) | ~v5_orders_2(B_432) | ~v4_orders_2(B_432) | ~v3_orders_2(B_432) | v2_struct_0(B_432))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.05/2.45  tff(c_3810, plain, (![A_431, C_433]: (m1_subset_1('#skF_2'(A_431, '#skF_4', C_433), k2_struct_0('#skF_4')) | ~r2_hidden(A_431, a_2_1_orders_2('#skF_4', C_433)) | ~m1_subset_1(C_433, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_3800])).
% 7.05/2.45  tff(c_3815, plain, (![A_431, C_433]: (m1_subset_1('#skF_2'(A_431, '#skF_4', C_433), k2_struct_0('#skF_4')) | ~r2_hidden(A_431, a_2_1_orders_2('#skF_4', C_433)) | ~m1_subset_1(C_433, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_67, c_3810])).
% 7.05/2.45  tff(c_3816, plain, (![A_431, C_433]: (m1_subset_1('#skF_2'(A_431, '#skF_4', C_433), k2_struct_0('#skF_4')) | ~r2_hidden(A_431, a_2_1_orders_2('#skF_4', C_433)) | ~m1_subset_1(C_433, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_3815])).
% 7.05/2.45  tff(c_4040, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4035, c_3816])).
% 7.05/2.45  tff(c_4047, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_4040])).
% 7.05/2.45  tff(c_4052, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_4047])).
% 7.05/2.45  tff(c_4058, plain, (a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_4052])).
% 7.05/2.45  tff(c_4064, plain, $false, inference(negUnitSimplification, [status(thm)], [c_211, c_4058])).
% 7.05/2.45  tff(c_4065, plain, (m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_4047])).
% 7.05/2.45  tff(c_4, plain, (![B_2, A_1]: (r2_hidden(B_2, A_1) | ~m1_subset_1(B_2, A_1) | v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.05/2.45  tff(c_4066, plain, (r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_4047])).
% 7.05/2.45  tff(c_4168, plain, (![B_481, A_482, C_483, E_484]: (r2_orders_2(B_481, '#skF_2'(A_482, B_481, C_483), E_484) | ~r2_hidden(E_484, C_483) | ~m1_subset_1(E_484, u1_struct_0(B_481)) | ~r2_hidden(A_482, a_2_1_orders_2(B_481, C_483)) | ~m1_subset_1(C_483, k1_zfmisc_1(u1_struct_0(B_481))) | ~l1_orders_2(B_481) | ~v5_orders_2(B_481) | ~v4_orders_2(B_481) | ~v3_orders_2(B_481) | v2_struct_0(B_481))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.05/2.45  tff(c_4175, plain, (![A_482, C_483, E_484]: (r2_orders_2('#skF_4', '#skF_2'(A_482, '#skF_4', C_483), E_484) | ~r2_hidden(E_484, C_483) | ~m1_subset_1(E_484, u1_struct_0('#skF_4')) | ~r2_hidden(A_482, a_2_1_orders_2('#skF_4', C_483)) | ~m1_subset_1(C_483, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_67, c_4168])).
% 7.05/2.45  tff(c_4182, plain, (![A_482, C_483, E_484]: (r2_orders_2('#skF_4', '#skF_2'(A_482, '#skF_4', C_483), E_484) | ~r2_hidden(E_484, C_483) | ~m1_subset_1(E_484, k2_struct_0('#skF_4')) | ~r2_hidden(A_482, a_2_1_orders_2('#skF_4', C_483)) | ~m1_subset_1(C_483, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_46, c_67, c_4175])).
% 7.05/2.45  tff(c_4223, plain, (![A_485, C_486, E_487]: (r2_orders_2('#skF_4', '#skF_2'(A_485, '#skF_4', C_486), E_487) | ~r2_hidden(E_487, C_486) | ~m1_subset_1(E_487, k2_struct_0('#skF_4')) | ~r2_hidden(A_485, a_2_1_orders_2('#skF_4', C_486)) | ~m1_subset_1(C_486, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_4182])).
% 7.05/2.45  tff(c_4382, plain, (![A_501, E_502]: (r2_orders_2('#skF_4', '#skF_2'(A_501, '#skF_4', k2_struct_0('#skF_4')), E_502) | ~r2_hidden(E_502, k2_struct_0('#skF_4')) | ~m1_subset_1(E_502, k2_struct_0('#skF_4')) | ~r2_hidden(A_501, a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_121, c_4223])).
% 7.05/2.45  tff(c_4393, plain, (![E_502]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_502) | ~r2_hidden(E_502, k2_struct_0('#skF_4')) | ~m1_subset_1(E_502, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_4035, c_4382])).
% 7.05/2.45  tff(c_4406, plain, (![E_503]: (r2_orders_2('#skF_4', '#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), E_503) | ~r2_hidden(E_503, k2_struct_0('#skF_4')) | ~m1_subset_1(E_503, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4066, c_4393])).
% 7.05/2.45  tff(c_24, plain, (![A_16, C_22]: (~r2_orders_2(A_16, C_22, C_22) | ~m1_subset_1(C_22, u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.05/2.45  tff(c_4414, plain, (~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_4406, c_24])).
% 7.05/2.45  tff(c_4424, plain, (~r2_hidden('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4065, c_46, c_4065, c_67, c_4414])).
% 7.05/2.45  tff(c_4427, plain, (~m1_subset_1('#skF_1'(a_2_1_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_4424])).
% 7.05/2.45  tff(c_4430, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4065, c_4427])).
% 7.05/2.45  tff(c_4432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_4430])).
% 7.05/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/2.45  
% 7.05/2.45  Inference rules
% 7.05/2.45  ----------------------
% 7.05/2.45  #Ref     : 0
% 7.05/2.45  #Sup     : 875
% 7.05/2.45  #Fact    : 0
% 7.05/2.45  #Define  : 0
% 7.05/2.45  #Split   : 15
% 7.05/2.45  #Chain   : 0
% 7.05/2.45  #Close   : 0
% 7.05/2.45  
% 7.05/2.45  Ordering : KBO
% 7.05/2.45  
% 7.05/2.45  Simplification rules
% 7.05/2.45  ----------------------
% 7.05/2.45  #Subsume      : 185
% 7.05/2.45  #Demod        : 880
% 7.05/2.45  #Tautology    : 208
% 7.05/2.45  #SimpNegUnit  : 222
% 7.05/2.45  #BackRed      : 43
% 7.05/2.45  
% 7.05/2.45  #Partial instantiations: 0
% 7.05/2.45  #Strategies tried      : 1
% 7.05/2.45  
% 7.05/2.45  Timing (in seconds)
% 7.05/2.45  ----------------------
% 7.05/2.45  Preprocessing        : 0.35
% 7.05/2.45  Parsing              : 0.18
% 7.05/2.45  CNF conversion       : 0.03
% 7.05/2.45  Main loop            : 1.28
% 7.05/2.45  Inferencing          : 0.46
% 7.05/2.45  Reduction            : 0.38
% 7.05/2.45  Demodulation         : 0.25
% 7.05/2.45  BG Simplification    : 0.06
% 7.05/2.45  Subsumption          : 0.29
% 7.05/2.45  Abstraction          : 0.08
% 7.05/2.45  MUC search           : 0.00
% 7.05/2.45  Cooper               : 0.00
% 7.05/2.45  Total                : 1.67
% 7.05/2.45  Index Insertion      : 0.00
% 7.05/2.45  Index Deletion       : 0.00
% 7.05/2.45  Index Matching       : 0.00
% 7.05/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
