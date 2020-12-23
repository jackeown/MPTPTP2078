%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2057+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:49 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 469 expanded)
%              Number of leaves         :   37 ( 185 expanded)
%              Depth                    :   17
%              Number of atoms          :  323 (2161 expanded)
%              Number of equality atoms :   19 (  48 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_waybel_0 > v6_waybel_0 > v2_waybel_0 > v13_waybel_0 > r2_hidden > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k4_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
           => ! [C] :
                ( ( ~ v1_xboole_0(C)
                  & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
               => ( r2_hidden(C,B)
                <=> r1_waybel_0(A,k3_yellow19(A,k2_struct_0(A),B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow19)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v1_xboole_0(B)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & ~ v1_xboole_0(C)
        & v2_waybel_0(C,k3_yellow_1(B))
        & v13_waybel_0(C,k3_yellow_1(B))
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B)))) )
     => ( ~ v2_struct_0(k3_yellow19(A,B,C))
        & v6_waybel_0(k3_yellow19(A,B,C),A)
        & l1_waybel_0(k3_yellow19(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_hidden(C,k2_yellow19(A,B))
            <=> ( r1_waybel_0(A,B,C)
                & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow19)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_55,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_113,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_54,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_102,plain,(
    r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_48,plain,
    ( ~ r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3')
    | ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_104,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_48])).

tff(c_44,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_subset_1(k2_struct_0(A_1),k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_40,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_38,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_164,plain,(
    ! [A_60,B_61,C_62] :
      ( l1_waybel_0(k3_yellow19(A_60,B_61,C_62),A_60)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_61))))
      | ~ v13_waybel_0(C_62,k3_yellow_1(B_61))
      | ~ v2_waybel_0(C_62,k3_yellow_1(B_61))
      | v1_xboole_0(C_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | v1_xboole_0(B_61)
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_169,plain,(
    ! [A_60] :
      ( l1_waybel_0(k3_yellow19(A_60,k2_struct_0('#skF_1'),'#skF_2'),A_60)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_60)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_36,c_164])).

tff(c_173,plain,(
    ! [A_60] :
      ( l1_waybel_0(k3_yellow19(A_60,k2_struct_0('#skF_1'),'#skF_2'),A_60)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_60)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_169])).

tff(c_174,plain,(
    ! [A_60] :
      ( l1_waybel_0(k3_yellow19(A_60,k2_struct_0('#skF_1'),'#skF_2'),A_60)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_60)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_173])).

tff(c_175,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_12,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(k2_struct_0(A_5))
      | ~ l1_struct_0(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_178,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_175,c_12])).

tff(c_184,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_178])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_184])).

tff(c_188,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_200,plain,(
    ! [A_66] :
      ( l1_waybel_0(k3_yellow19(A_66,k2_struct_0('#skF_1'),'#skF_2'),A_66)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_66)))
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_203,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_200])).

tff(c_206,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_203])).

tff(c_207,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_206])).

tff(c_74,plain,(
    ! [A_35,B_36,C_37] :
      ( k7_subset_1(A_35,B_36,C_37) = k4_xboole_0(B_36,C_37)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_82,plain,(
    ! [C_37] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',C_37) = k4_xboole_0('#skF_2',C_37) ),
    inference(resolution,[status(thm)],[c_36,c_74])).

tff(c_217,plain,(
    ! [A_68,B_69] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_68))),B_69,k1_tarski(k1_xboole_0)) = k2_yellow19(A_68,k3_yellow19(A_68,k2_struct_0(A_68),B_69))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_68)))))
      | ~ v13_waybel_0(B_69,k3_yellow_1(k2_struct_0(A_68)))
      | ~ v2_waybel_0(B_69,k3_yellow_1(k2_struct_0(A_68)))
      | v1_xboole_0(B_69)
      | ~ l1_struct_0(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_222,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_217])).

tff(c_226,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_82,c_222])).

tff(c_227,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_226])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_127,plain,(
    ! [C_51,A_52,B_53] :
      ( r2_hidden(C_51,k2_yellow19(A_52,B_53))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ r1_waybel_0(A_52,B_53,C_51)
      | ~ l1_waybel_0(B_53,A_52)
      | v2_struct_0(B_53)
      | ~ l1_struct_0(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_133,plain,(
    ! [B_53] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_1',B_53))
      | ~ r1_waybel_0('#skF_1',B_53,'#skF_3')
      | ~ l1_waybel_0(B_53,'#skF_1')
      | v2_struct_0(B_53)
      | ~ l1_struct_0('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_127])).

tff(c_138,plain,(
    ! [B_53] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_1',B_53))
      | ~ r1_waybel_0('#skF_1',B_53,'#skF_3')
      | ~ l1_waybel_0(B_53,'#skF_1')
      | v2_struct_0(B_53)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_133])).

tff(c_139,plain,(
    ! [B_53] :
      ( r2_hidden('#skF_3',k2_yellow19('#skF_1',B_53))
      | ~ r1_waybel_0('#skF_1',B_53,'#skF_3')
      | ~ l1_waybel_0(B_53,'#skF_1')
      | v2_struct_0(B_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_138])).

tff(c_234,plain,
    ( r2_hidden('#skF_3',k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
    | ~ r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3')
    | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_139])).

tff(c_246,plain,
    ( r2_hidden('#skF_3',k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
    | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_102,c_234])).

tff(c_254,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_8,plain,(
    ! [A_2,B_3,C_4] :
      ( ~ v2_struct_0(k3_yellow19(A_2,B_3,C_4))
      | ~ m1_subset_1(C_4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_3))))
      | ~ v13_waybel_0(C_4,k3_yellow_1(B_3))
      | ~ v2_waybel_0(C_4,k3_yellow_1(B_3))
      | v1_xboole_0(C_4)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(u1_struct_0(A_2)))
      | v1_xboole_0(B_3)
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_256,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_254,c_8])).

tff(c_259,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_36,c_256])).

tff(c_260,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_188,c_42,c_259])).

tff(c_264,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_260])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_264])).

tff(c_269,plain,(
    r2_hidden('#skF_3',k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))) ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_28,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_hidden(A_19,B_20)
      | ~ r2_hidden(A_19,k4_xboole_0(B_20,k1_tarski(C_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_273,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_269,c_28])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_273])).

tff(c_278,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_24,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_hidden(A_19,k4_xboole_0(B_20,k1_tarski(C_21)))
      | C_21 = A_19
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_345,plain,(
    ! [A_92,B_93,C_94] :
      ( l1_waybel_0(k3_yellow19(A_92,B_93,C_94),A_92)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(u1_struct_0(k3_yellow_1(B_93))))
      | ~ v13_waybel_0(C_94,k3_yellow_1(B_93))
      | ~ v2_waybel_0(C_94,k3_yellow_1(B_93))
      | v1_xboole_0(C_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | v1_xboole_0(B_93)
      | ~ l1_struct_0(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_350,plain,(
    ! [A_92] :
      ( l1_waybel_0(k3_yellow19(A_92,k2_struct_0('#skF_1'),'#skF_2'),A_92)
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_92)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_92)
      | v2_struct_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_36,c_345])).

tff(c_354,plain,(
    ! [A_92] :
      ( l1_waybel_0(k3_yellow19(A_92,k2_struct_0('#skF_1'),'#skF_2'),A_92)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_92)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_92)
      | v2_struct_0(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_350])).

tff(c_355,plain,(
    ! [A_92] :
      ( l1_waybel_0(k3_yellow19(A_92,k2_struct_0('#skF_1'),'#skF_2'),A_92)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_92)))
      | v1_xboole_0(k2_struct_0('#skF_1'))
      | ~ l1_struct_0(A_92)
      | v2_struct_0(A_92) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_354])).

tff(c_356,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_355])).

tff(c_359,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_356,c_12])).

tff(c_365,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_359])).

tff(c_367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_365])).

tff(c_369,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_370,plain,(
    ! [A_95] :
      ( l1_waybel_0(k3_yellow19(A_95,k2_struct_0('#skF_1'),'#skF_2'),A_95)
      | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(splitRight,[status(thm)],[c_355])).

tff(c_373,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_370])).

tff(c_376,plain,
    ( l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_373])).

tff(c_377,plain,(
    l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_376])).

tff(c_397,plain,(
    ! [A_100,B_101] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_100))),B_101,k1_tarski(k1_xboole_0)) = k2_yellow19(A_100,k3_yellow19(A_100,k2_struct_0(A_100),B_101))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_100)))))
      | ~ v13_waybel_0(B_101,k3_yellow_1(k2_struct_0(A_100)))
      | ~ v2_waybel_0(B_101,k3_yellow_1(k2_struct_0(A_100)))
      | v1_xboole_0(B_101)
      | ~ l1_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_402,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_397])).

tff(c_406,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_82,c_402])).

tff(c_407,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_42,c_406])).

tff(c_18,plain,(
    ! [C_15,A_9,B_13] :
      ( m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ r2_hidden(C_15,k2_yellow19(A_9,B_13))
      | ~ l1_waybel_0(B_13,A_9)
      | v2_struct_0(B_13)
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_416,plain,(
    ! [C_15] :
      ( m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(C_15,k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_struct_0('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_18])).

tff(c_428,plain,(
    ! [C_15] :
      ( m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(C_15,k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_377,c_416])).

tff(c_429,plain,(
    ! [C_15] :
      ( m1_subset_1(C_15,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden(C_15,k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_428])).

tff(c_434,plain,(
    v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_429])).

tff(c_436,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_434,c_8])).

tff(c_439,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_36,c_436])).

tff(c_440,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_369,c_42,c_439])).

tff(c_443,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_440])).

tff(c_447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_443])).

tff(c_449,plain,(
    ~ v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_429])).

tff(c_20,plain,(
    ! [A_9,B_13,C_15] :
      ( r1_waybel_0(A_9,B_13,C_15)
      | ~ r2_hidden(C_15,k2_yellow19(A_9,B_13))
      | ~ l1_waybel_0(B_13,A_9)
      | v2_struct_0(B_13)
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_419,plain,(
    ! [C_15] :
      ( r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_15)
      | ~ r2_hidden(C_15,k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
      | ~ l1_waybel_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | ~ l1_struct_0('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_20])).

tff(c_431,plain,(
    ! [C_15] :
      ( r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_15)
      | ~ r2_hidden(C_15,k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_377,c_419])).

tff(c_432,plain,(
    ! [C_15] :
      ( r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_15)
      | ~ r2_hidden(C_15,k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)))
      | v2_struct_0(k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_431])).

tff(c_538,plain,(
    ! [C_110] :
      ( r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),C_110)
      | ~ r2_hidden(C_110,k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_449,c_432])).

tff(c_279,plain,(
    ~ r1_waybel_0('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_542,plain,(
    ~ r2_hidden('#skF_3',k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))) ),
    inference(resolution,[status(thm)],[c_538,c_279])).

tff(c_545,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r2_hidden('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_542])).

tff(c_548,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_545])).

tff(c_10,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_55,plain,(
    ! [A_27] :
      ( k1_xboole_0 = A_27
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_59,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_55])).

tff(c_60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_10])).

tff(c_557,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_60])).

tff(c_561,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_557])).

%------------------------------------------------------------------------------
