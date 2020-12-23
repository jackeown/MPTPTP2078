%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1659+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:12 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 226 expanded)
%              Number of leaves         :   33 (  95 expanded)
%              Depth                    :    9
%              Number of atoms          :  204 ( 731 expanded)
%              Number of equality atoms :   27 ( 111 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_yellow_0 > r1_yellow_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k6_waybel_0 > k6_domain_1 > k4_waybel_0 > k2_yellow_0 > k1_yellow_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k6_waybel_0,type,(
    k6_waybel_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k4_waybel_0,type,(
    k4_waybel_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( r2_yellow_0(A,k6_waybel_0(A,B))
              & k2_yellow_0(A,k6_waybel_0(A,B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_waybel_0)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r1_yellow_0(A,k6_domain_1(u1_struct_0(A),B))
            & r2_yellow_0(A,k6_domain_1(u1_struct_0(A),B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_0)).

tff(f_34,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => k6_waybel_0(A,B) = k4_waybel_0(A,k6_domain_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_waybel_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_yellow_0(A,B)
          <=> r2_yellow_0(A,k4_waybel_0(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_waybel_0)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( k1_yellow_0(A,k6_domain_1(u1_struct_0(A),B)) = B
            & k2_yellow_0(A,k6_domain_1(u1_struct_0(A),B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_0)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( r2_yellow_0(A,B)
           => k2_yellow_0(A,B) = k2_yellow_0(A,k4_waybel_0(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_0)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_26,plain,
    ( k2_yellow_0('#skF_1',k6_waybel_0('#skF_1','#skF_2')) != '#skF_2'
    | ~ r2_yellow_0('#skF_1',k6_waybel_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    ~ r2_yellow_0('#skF_1',k6_waybel_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_36,plain,(
    v3_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_34,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_30,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_32,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_6,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_41,plain,(
    ! [A_25,B_26] :
      ( k6_domain_1(A_25,B_26) = k1_tarski(B_26)
      | ~ m1_subset_1(B_26,A_25)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_45,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_41])).

tff(c_47,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(u1_struct_0(A_7))
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_50,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_47,c_8])).

tff(c_53,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_50])).

tff(c_56,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_56])).

tff(c_61,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_102,plain,(
    ! [A_31,B_32] :
      ( r2_yellow_0(A_31,k6_domain_1(u1_struct_0(A_31),B_32))
      | ~ m1_subset_1(B_32,u1_struct_0(A_31))
      | ~ l1_orders_2(A_31)
      | ~ v5_orders_2(A_31)
      | ~ v3_orders_2(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_105,plain,
    ( r2_yellow_0('#skF_1',k1_tarski('#skF_2'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_102])).

tff(c_107,plain,
    ( r2_yellow_0('#skF_1',k1_tarski('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_28,c_105])).

tff(c_108,plain,(
    r2_yellow_0('#skF_1',k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_107])).

tff(c_83,plain,(
    ! [A_29,B_30] :
      ( k4_waybel_0(A_29,k6_domain_1(u1_struct_0(A_29),B_30)) = k6_waybel_0(A_29,B_30)
      | ~ m1_subset_1(B_30,u1_struct_0(A_29))
      | ~ l1_orders_2(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_92,plain,
    ( k4_waybel_0('#skF_1',k1_tarski('#skF_2')) = k6_waybel_0('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_83])).

tff(c_96,plain,
    ( k4_waybel_0('#skF_1',k1_tarski('#skF_2')) = k6_waybel_0('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_92])).

tff(c_97,plain,(
    k4_waybel_0('#skF_1',k1_tarski('#skF_2')) = k6_waybel_0('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_96])).

tff(c_62,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k6_domain_1(A_4,B_5),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(B_5,A_4)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_4])).

tff(c_75,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_71])).

tff(c_76,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_75])).

tff(c_178,plain,(
    ! [A_41,B_42] :
      ( r2_yellow_0(A_41,k4_waybel_0(A_41,B_42))
      | ~ r2_yellow_0(A_41,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_orders_2(A_41)
      | ~ v4_orders_2(A_41)
      | ~ v3_orders_2(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_180,plain,
    ( r2_yellow_0('#skF_1',k4_waybel_0('#skF_1',k1_tarski('#skF_2')))
    | ~ r2_yellow_0('#skF_1',k1_tarski('#skF_2'))
    | ~ l1_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_76,c_178])).

tff(c_186,plain,
    ( r2_yellow_0('#skF_1',k6_waybel_0('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_108,c_97,c_180])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_46,c_186])).

tff(c_189,plain,(
    k2_yellow_0('#skF_1',k6_waybel_0('#skF_1','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_191,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_45])).

tff(c_199,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_191,c_8])).

tff(c_202,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_199])).

tff(c_205,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_202])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_205])).

tff(c_210,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_258,plain,(
    ! [A_51,B_52] :
      ( r2_yellow_0(A_51,k6_domain_1(u1_struct_0(A_51),B_52))
      | ~ m1_subset_1(B_52,u1_struct_0(A_51))
      | ~ l1_orders_2(A_51)
      | ~ v5_orders_2(A_51)
      | ~ v3_orders_2(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_261,plain,
    ( r2_yellow_0('#skF_1',k1_tarski('#skF_2'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_258])).

tff(c_263,plain,
    ( r2_yellow_0('#skF_1',k1_tarski('#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_28,c_261])).

tff(c_264,plain,(
    r2_yellow_0('#skF_1',k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_263])).

tff(c_289,plain,(
    ! [A_55,B_56] :
      ( k2_yellow_0(A_55,k6_domain_1(u1_struct_0(A_55),B_56)) = B_56
      | ~ m1_subset_1(B_56,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55)
      | ~ v5_orders_2(A_55)
      | ~ v3_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_298,plain,
    ( k2_yellow_0('#skF_1',k1_tarski('#skF_2')) = '#skF_2'
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_289])).

tff(c_302,plain,
    ( k2_yellow_0('#skF_1',k1_tarski('#skF_2')) = '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_28,c_298])).

tff(c_303,plain,(
    k2_yellow_0('#skF_1',k1_tarski('#skF_2')) = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_302])).

tff(c_232,plain,(
    ! [A_47,B_48] :
      ( k4_waybel_0(A_47,k6_domain_1(u1_struct_0(A_47),B_48)) = k6_waybel_0(A_47,B_48)
      | ~ m1_subset_1(B_48,u1_struct_0(A_47))
      | ~ l1_orders_2(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_241,plain,
    ( k4_waybel_0('#skF_1',k1_tarski('#skF_2')) = k6_waybel_0('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_232])).

tff(c_245,plain,
    ( k4_waybel_0('#skF_1',k1_tarski('#skF_2')) = k6_waybel_0('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_241])).

tff(c_246,plain,(
    k4_waybel_0('#skF_1',k1_tarski('#skF_2')) = k6_waybel_0('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_245])).

tff(c_211,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_45])).

tff(c_216,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(k6_domain_1(A_45,B_46),k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_46,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_222,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_216])).

tff(c_225,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_222])).

tff(c_226,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_225])).

tff(c_346,plain,(
    ! [A_63,B_64] :
      ( k2_yellow_0(A_63,k4_waybel_0(A_63,B_64)) = k2_yellow_0(A_63,B_64)
      | ~ r2_yellow_0(A_63,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_orders_2(A_63)
      | ~ v4_orders_2(A_63)
      | ~ v3_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_348,plain,
    ( k2_yellow_0('#skF_1',k4_waybel_0('#skF_1',k1_tarski('#skF_2'))) = k2_yellow_0('#skF_1',k1_tarski('#skF_2'))
    | ~ r2_yellow_0('#skF_1',k1_tarski('#skF_2'))
    | ~ l1_orders_2('#skF_1')
    | ~ v4_orders_2('#skF_1')
    | ~ v3_orders_2('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_226,c_346])).

tff(c_354,plain,
    ( k2_yellow_0('#skF_1',k6_waybel_0('#skF_1','#skF_2')) = '#skF_2'
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_264,c_303,c_246,c_348])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_189,c_354])).

%------------------------------------------------------------------------------
