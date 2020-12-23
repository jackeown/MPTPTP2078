%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:28 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 139 expanded)
%              Number of leaves         :   48 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          :  158 ( 318 expanded)
%              Number of equality atoms :   26 (  47 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
              & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
           => B = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_69,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_71,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_67,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_107,axiom,(
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

tff(f_128,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
            & v2_waybel_0(B,k3_yellow_1(A))
            & v13_waybel_0(B,k3_yellow_1(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
         => ! [C] :
              ~ ( r2_hidden(C,B)
                & v1_xboole_0(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_58,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_54,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_52,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_50,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,k3_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_135,plain,(
    ! [A_61,B_62] :
      ( ~ r1_xboole_0(A_61,B_62)
      | v1_xboole_0(k3_xboole_0(A_61,B_62)) ) ),
    inference(resolution,[status(thm)],[c_4,c_130])).

tff(c_147,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_2'(A_70,B_71),A_70)
      | r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_163,plain,(
    ! [A_72,B_73] :
      ( ~ v1_xboole_0(A_72)
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_147,c_2])).

tff(c_28,plain,(
    ! [A_21] : r1_tarski(k1_xboole_0,A_21) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_107,plain,(
    ! [B_58,A_59] :
      ( B_58 = A_59
      | ~ r1_tarski(B_58,A_59)
      | ~ r1_tarski(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_116,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_107])).

tff(c_179,plain,(
    ! [A_77] :
      ( k1_xboole_0 = A_77
      | ~ v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_163,c_116])).

tff(c_210,plain,(
    ! [A_82,B_83] :
      ( k3_xboole_0(A_82,B_83) = k1_xboole_0
      | ~ r1_xboole_0(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_135,c_179])).

tff(c_276,plain,(
    ! [A_88] : k3_xboole_0(A_88,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_210])).

tff(c_26,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_287,plain,(
    ! [A_88] : k5_xboole_0(A_88,k1_xboole_0) = k4_xboole_0(A_88,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_26])).

tff(c_303,plain,(
    ! [A_88] : k5_xboole_0(A_88,k1_xboole_0) = A_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_287])).

tff(c_98,plain,(
    ! [A_53,B_54] :
      ( r1_xboole_0(k1_tarski(A_53),B_54)
      | r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_xboole_0(B_11,A_10)
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_101,plain,(
    ! [B_54,A_53] :
      ( r1_xboole_0(B_54,k1_tarski(A_53))
      | r2_hidden(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_98,c_14])).

tff(c_424,plain,(
    ! [B_101,A_102] :
      ( k3_xboole_0(B_101,k1_tarski(A_102)) = k1_xboole_0
      | r2_hidden(A_102,B_101) ) ),
    inference(resolution,[status(thm)],[c_101,c_210])).

tff(c_447,plain,(
    ! [B_101,A_102] :
      ( k4_xboole_0(B_101,k1_tarski(A_102)) = k5_xboole_0(B_101,k1_xboole_0)
      | r2_hidden(A_102,B_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_26])).

tff(c_473,plain,(
    ! [B_101,A_102] :
      ( k4_xboole_0(B_101,k1_tarski(A_102)) = B_101
      | r2_hidden(A_102,B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_447])).

tff(c_319,plain,(
    ! [A_90,B_91,C_92] :
      ( k7_subset_1(A_90,B_91,C_92) = k4_xboole_0(B_91,C_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_322,plain,(
    ! [C_92] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',C_92) = k4_xboole_0('#skF_5',C_92) ),
    inference(resolution,[status(thm)],[c_48,c_319])).

tff(c_657,plain,(
    ! [A_122,B_123] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_122))),B_123,k1_tarski(k1_xboole_0)) = k2_yellow19(A_122,k3_yellow19(A_122,k2_struct_0(A_122),B_123))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_122)))))
      | ~ v13_waybel_0(B_123,k3_yellow_1(k2_struct_0(A_122)))
      | ~ v2_waybel_0(B_123,k3_yellow_1(k2_struct_0(A_122)))
      | v1_xboole_0(B_123)
      | ~ l1_struct_0(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_659,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_657])).

tff(c_662,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_322,c_659])).

tff(c_663,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_662])).

tff(c_46,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_723,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_663,c_46])).

tff(c_731,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_473,c_723])).

tff(c_44,plain,(
    ! [C_40,B_38,A_34] :
      ( ~ v1_xboole_0(C_40)
      | ~ r2_hidden(C_40,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_34))))
      | ~ v13_waybel_0(B_38,k3_yellow_1(A_34))
      | ~ v2_waybel_0(B_38,k3_yellow_1(A_34))
      | ~ v1_subset_1(B_38,u1_struct_0(k3_yellow_1(A_34)))
      | v1_xboole_0(B_38)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_733,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_34))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_34))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_34))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_34)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_731,c_44])).

tff(c_741,plain,(
    ! [A_34] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_34))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_34))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_34))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_34)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_733])).

tff(c_868,plain,(
    ! [A_143] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_143))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_143))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_143))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_143)))
      | v1_xboole_0(A_143) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_741])).

tff(c_871,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_868])).

tff(c_874,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_871])).

tff(c_38,plain,(
    ! [A_29] :
      ( ~ v1_xboole_0(k2_struct_0(A_29))
      | ~ l1_struct_0(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_884,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_874,c_38])).

tff(c_890,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_884])).

tff(c_892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_890])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:33:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.42  
% 2.80/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.42  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.80/1.42  
% 2.80/1.42  %Foreground sorts:
% 2.80/1.42  
% 2.80/1.42  
% 2.80/1.42  %Background operators:
% 2.80/1.42  
% 2.80/1.42  
% 2.80/1.42  %Foreground operators:
% 2.80/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.42  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.80/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.42  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.80/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.80/1.42  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.80/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.80/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.80/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.42  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.80/1.42  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.80/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.80/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.80/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.80/1.42  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.80/1.42  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.80/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.80/1.42  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.80/1.42  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.80/1.42  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.80/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.80/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.80/1.42  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.80/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.42  
% 2.80/1.44  tff(f_148, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 2.80/1.44  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.80/1.44  tff(f_69, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.80/1.44  tff(f_71, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.80/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.80/1.44  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.80/1.44  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.80/1.44  tff(f_67, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.80/1.44  tff(f_63, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.80/1.44  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.80/1.44  tff(f_76, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.80/1.44  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.80/1.44  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.80/1.44  tff(f_107, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 2.80/1.44  tff(f_128, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 2.80/1.44  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.80/1.44  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.80/1.44  tff(c_58, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.80/1.44  tff(c_54, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.80/1.44  tff(c_52, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.80/1.44  tff(c_50, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.80/1.44  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.80/1.44  tff(c_56, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.80/1.44  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.80/1.44  tff(c_30, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.80/1.44  tff(c_32, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.80/1.44  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.44  tff(c_130, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, k3_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.80/1.44  tff(c_135, plain, (![A_61, B_62]: (~r1_xboole_0(A_61, B_62) | v1_xboole_0(k3_xboole_0(A_61, B_62)))), inference(resolution, [status(thm)], [c_4, c_130])).
% 2.80/1.44  tff(c_147, plain, (![A_70, B_71]: (r2_hidden('#skF_2'(A_70, B_71), A_70) | r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.80/1.44  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.44  tff(c_163, plain, (![A_72, B_73]: (~v1_xboole_0(A_72) | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_147, c_2])).
% 2.80/1.44  tff(c_28, plain, (![A_21]: (r1_tarski(k1_xboole_0, A_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.80/1.44  tff(c_107, plain, (![B_58, A_59]: (B_58=A_59 | ~r1_tarski(B_58, A_59) | ~r1_tarski(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.80/1.44  tff(c_116, plain, (![A_21]: (k1_xboole_0=A_21 | ~r1_tarski(A_21, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_107])).
% 2.80/1.44  tff(c_179, plain, (![A_77]: (k1_xboole_0=A_77 | ~v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_163, c_116])).
% 2.80/1.44  tff(c_210, plain, (![A_82, B_83]: (k3_xboole_0(A_82, B_83)=k1_xboole_0 | ~r1_xboole_0(A_82, B_83))), inference(resolution, [status(thm)], [c_135, c_179])).
% 2.80/1.44  tff(c_276, plain, (![A_88]: (k3_xboole_0(A_88, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_210])).
% 2.80/1.44  tff(c_26, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.80/1.44  tff(c_287, plain, (![A_88]: (k5_xboole_0(A_88, k1_xboole_0)=k4_xboole_0(A_88, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_276, c_26])).
% 2.80/1.44  tff(c_303, plain, (![A_88]: (k5_xboole_0(A_88, k1_xboole_0)=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_287])).
% 2.80/1.44  tff(c_98, plain, (![A_53, B_54]: (r1_xboole_0(k1_tarski(A_53), B_54) | r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.80/1.44  tff(c_14, plain, (![B_11, A_10]: (r1_xboole_0(B_11, A_10) | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.80/1.44  tff(c_101, plain, (![B_54, A_53]: (r1_xboole_0(B_54, k1_tarski(A_53)) | r2_hidden(A_53, B_54))), inference(resolution, [status(thm)], [c_98, c_14])).
% 2.80/1.44  tff(c_424, plain, (![B_101, A_102]: (k3_xboole_0(B_101, k1_tarski(A_102))=k1_xboole_0 | r2_hidden(A_102, B_101))), inference(resolution, [status(thm)], [c_101, c_210])).
% 2.80/1.44  tff(c_447, plain, (![B_101, A_102]: (k4_xboole_0(B_101, k1_tarski(A_102))=k5_xboole_0(B_101, k1_xboole_0) | r2_hidden(A_102, B_101))), inference(superposition, [status(thm), theory('equality')], [c_424, c_26])).
% 2.80/1.44  tff(c_473, plain, (![B_101, A_102]: (k4_xboole_0(B_101, k1_tarski(A_102))=B_101 | r2_hidden(A_102, B_101))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_447])).
% 2.80/1.44  tff(c_319, plain, (![A_90, B_91, C_92]: (k7_subset_1(A_90, B_91, C_92)=k4_xboole_0(B_91, C_92) | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.80/1.44  tff(c_322, plain, (![C_92]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', C_92)=k4_xboole_0('#skF_5', C_92))), inference(resolution, [status(thm)], [c_48, c_319])).
% 2.80/1.44  tff(c_657, plain, (![A_122, B_123]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_122))), B_123, k1_tarski(k1_xboole_0))=k2_yellow19(A_122, k3_yellow19(A_122, k2_struct_0(A_122), B_123)) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_122))))) | ~v13_waybel_0(B_123, k3_yellow_1(k2_struct_0(A_122))) | ~v2_waybel_0(B_123, k3_yellow_1(k2_struct_0(A_122))) | v1_xboole_0(B_123) | ~l1_struct_0(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.80/1.44  tff(c_659, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_657])).
% 2.80/1.44  tff(c_662, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_50, c_322, c_659])).
% 2.80/1.44  tff(c_663, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_662])).
% 2.80/1.44  tff(c_46, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_148])).
% 2.80/1.44  tff(c_723, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_663, c_46])).
% 2.80/1.44  tff(c_731, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_473, c_723])).
% 2.80/1.44  tff(c_44, plain, (![C_40, B_38, A_34]: (~v1_xboole_0(C_40) | ~r2_hidden(C_40, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_34)))) | ~v13_waybel_0(B_38, k3_yellow_1(A_34)) | ~v2_waybel_0(B_38, k3_yellow_1(A_34)) | ~v1_subset_1(B_38, u1_struct_0(k3_yellow_1(A_34))) | v1_xboole_0(B_38) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.80/1.44  tff(c_733, plain, (![A_34]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_34)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_34)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_34)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_34))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_731, c_44])).
% 2.80/1.44  tff(c_741, plain, (![A_34]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_34)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_34)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_34)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_34))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_733])).
% 2.80/1.44  tff(c_868, plain, (![A_143]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_143)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_143)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_143)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_143))) | v1_xboole_0(A_143))), inference(negUnitSimplification, [status(thm)], [c_56, c_741])).
% 2.80/1.44  tff(c_871, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_868])).
% 2.80/1.44  tff(c_874, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_871])).
% 2.80/1.44  tff(c_38, plain, (![A_29]: (~v1_xboole_0(k2_struct_0(A_29)) | ~l1_struct_0(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.80/1.44  tff(c_884, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_874, c_38])).
% 2.80/1.44  tff(c_890, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_884])).
% 2.80/1.44  tff(c_892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_890])).
% 2.80/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.44  
% 2.80/1.44  Inference rules
% 2.80/1.44  ----------------------
% 2.80/1.44  #Ref     : 0
% 2.80/1.44  #Sup     : 182
% 2.80/1.44  #Fact    : 0
% 2.80/1.44  #Define  : 0
% 2.80/1.44  #Split   : 0
% 2.80/1.44  #Chain   : 0
% 2.80/1.44  #Close   : 0
% 2.80/1.44  
% 2.80/1.44  Ordering : KBO
% 2.80/1.44  
% 2.80/1.44  Simplification rules
% 2.80/1.44  ----------------------
% 2.80/1.44  #Subsume      : 42
% 2.80/1.44  #Demod        : 60
% 2.80/1.44  #Tautology    : 82
% 2.80/1.44  #SimpNegUnit  : 14
% 2.80/1.44  #BackRed      : 1
% 2.80/1.44  
% 2.80/1.44  #Partial instantiations: 0
% 2.80/1.44  #Strategies tried      : 1
% 2.80/1.44  
% 2.80/1.44  Timing (in seconds)
% 2.80/1.44  ----------------------
% 2.80/1.44  Preprocessing        : 0.35
% 2.80/1.44  Parsing              : 0.18
% 2.80/1.44  CNF conversion       : 0.02
% 2.80/1.44  Main loop            : 0.33
% 2.80/1.44  Inferencing          : 0.12
% 2.80/1.44  Reduction            : 0.11
% 2.80/1.44  Demodulation         : 0.08
% 2.80/1.44  BG Simplification    : 0.02
% 2.80/1.44  Subsumption          : 0.06
% 2.80/1.44  Abstraction          : 0.02
% 2.80/1.44  MUC search           : 0.00
% 2.80/1.44  Cooper               : 0.00
% 2.80/1.44  Total                : 0.71
% 2.80/1.44  Index Insertion      : 0.00
% 2.80/1.45  Index Deletion       : 0.00
% 2.80/1.45  Index Matching       : 0.00
% 2.80/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
