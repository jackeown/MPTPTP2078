%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:25 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 120 expanded)
%              Number of leaves         :   47 (  63 expanded)
%              Depth                    :   15
%              Number of atoms          :  148 ( 271 expanded)
%              Number of equality atoms :   33 (  51 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
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

tff(f_35,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_61,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_101,axiom,(
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

tff(f_122,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_56,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_52,plain,(
    v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_50,plain,(
    v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_48,plain,(
    v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_10,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_133,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k4_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    ! [A_21] : k4_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_163,plain,(
    ! [B_54] : k3_xboole_0(k1_xboole_0,B_54) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_171,plain,(
    ! [B_54] : k3_xboole_0(B_54,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_2])).

tff(c_327,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_339,plain,(
    ! [B_54] : k5_xboole_0(B_54,k1_xboole_0) = k4_xboole_0(B_54,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_327])).

tff(c_352,plain,(
    ! [B_54] : k5_xboole_0(B_54,k1_xboole_0) = B_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_339])).

tff(c_32,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(k1_tarski(A_22),B_23)
      | r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_385,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_1'(A_71,B_72),A_71)
      | r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_464,plain,(
    ! [A_78,B_79,B_80] :
      ( ~ r1_xboole_0(A_78,B_79)
      | r1_tarski(k3_xboole_0(A_78,B_79),B_80) ) ),
    inference(resolution,[status(thm)],[c_385,c_14])).

tff(c_24,plain,(
    ! [A_17] : r1_tarski(k1_xboole_0,A_17) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_297,plain,(
    ! [B_61,A_62] :
      ( B_61 = A_62
      | ~ r1_tarski(B_61,A_62)
      | ~ r1_tarski(A_62,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_306,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_297])).

tff(c_499,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(A_86,B_87) = k1_xboole_0
      | ~ r1_xboole_0(A_86,B_87) ) ),
    inference(resolution,[status(thm)],[c_464,c_306])).

tff(c_640,plain,(
    ! [A_104,B_105] :
      ( k3_xboole_0(k1_tarski(A_104),B_105) = k1_xboole_0
      | r2_hidden(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_32,c_499])).

tff(c_345,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_327])).

tff(c_658,plain,(
    ! [B_105,A_104] :
      ( k4_xboole_0(B_105,k1_tarski(A_104)) = k5_xboole_0(B_105,k1_xboole_0)
      | r2_hidden(A_104,B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_345])).

tff(c_702,plain,(
    ! [B_105,A_104] :
      ( k4_xboole_0(B_105,k1_tarski(A_104)) = B_105
      | r2_hidden(A_104,B_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_658])).

tff(c_636,plain,(
    ! [A_101,B_102,C_103] :
      ( k7_subset_1(A_101,B_102,C_103) = k4_xboole_0(B_102,C_103)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_639,plain,(
    ! [C_103] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',C_103) = k4_xboole_0('#skF_4',C_103) ),
    inference(resolution,[status(thm)],[c_46,c_636])).

tff(c_834,plain,(
    ! [A_114,B_115] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_114))),B_115,k1_tarski(k1_xboole_0)) = k2_yellow19(A_114,k3_yellow19(A_114,k2_struct_0(A_114),B_115))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_114)))))
      | ~ v13_waybel_0(B_115,k3_yellow_1(k2_struct_0(A_114)))
      | ~ v2_waybel_0(B_115,k3_yellow_1(k2_struct_0(A_114)))
      | v1_xboole_0(B_115)
      | ~ l1_struct_0(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_836,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_834])).

tff(c_839,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_48,c_639,c_836])).

tff(c_840,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_54,c_839])).

tff(c_44,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_949,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_840,c_44])).

tff(c_957,plain,(
    r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_702,c_949])).

tff(c_42,plain,(
    ! [C_38,B_36,A_32] :
      ( ~ v1_xboole_0(C_38)
      | ~ r2_hidden(C_38,B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_32))))
      | ~ v13_waybel_0(B_36,k3_yellow_1(A_32))
      | ~ v2_waybel_0(B_36,k3_yellow_1(A_32))
      | ~ v1_subset_1(B_36,u1_struct_0(k3_yellow_1(A_32)))
      | v1_xboole_0(B_36)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_959,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_32))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_32))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_32))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_32)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_957,c_42])).

tff(c_964,plain,(
    ! [A_32] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_32))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_32))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_32))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_32)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_959])).

tff(c_1120,plain,(
    ! [A_133] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_133))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_133))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_133))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_133)))
      | v1_xboole_0(A_133) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_964])).

tff(c_1123,plain,
    ( ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_1120])).

tff(c_1126,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_1123])).

tff(c_36,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0(k2_struct_0(A_27))
      | ~ l1_struct_0(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1129,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1126,c_36])).

tff(c_1132,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1129])).

tff(c_1134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:50:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.43  
% 2.90/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.43  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.90/1.43  
% 2.90/1.43  %Foreground sorts:
% 2.90/1.43  
% 2.90/1.43  
% 2.90/1.43  %Background operators:
% 2.90/1.43  
% 2.90/1.43  
% 2.90/1.43  %Foreground operators:
% 2.90/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.90/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.43  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.90/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.43  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.90/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.90/1.43  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.90/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.90/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.43  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.90/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.90/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.90/1.43  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.90/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.43  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.90/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.90/1.43  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.90/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.90/1.43  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.90/1.43  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.90/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.90/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.90/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.90/1.43  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.90/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.43  
% 3.15/1.45  tff(f_142, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 3.15/1.45  tff(f_35, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.15/1.45  tff(f_61, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.15/1.45  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.15/1.45  tff(f_65, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.15/1.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.15/1.45  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.15/1.45  tff(f_70, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.15/1.45  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.15/1.45  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.15/1.45  tff(f_59, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.15/1.45  tff(f_55, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.15/1.45  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.15/1.45  tff(f_101, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 3.15/1.45  tff(f_122, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 3.15/1.45  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.15/1.45  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.15/1.45  tff(c_56, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.15/1.45  tff(c_52, plain, (v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.15/1.45  tff(c_50, plain, (v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.15/1.45  tff(c_48, plain, (v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.15/1.45  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.15/1.45  tff(c_54, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.15/1.45  tff(c_10, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.45  tff(c_26, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.15/1.45  tff(c_133, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k4_xboole_0(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.15/1.45  tff(c_30, plain, (![A_21]: (k4_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.45  tff(c_163, plain, (![B_54]: (k3_xboole_0(k1_xboole_0, B_54)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_133, c_30])).
% 3.15/1.45  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.45  tff(c_171, plain, (![B_54]: (k3_xboole_0(B_54, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_163, c_2])).
% 3.15/1.45  tff(c_327, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.15/1.45  tff(c_339, plain, (![B_54]: (k5_xboole_0(B_54, k1_xboole_0)=k4_xboole_0(B_54, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_171, c_327])).
% 3.15/1.45  tff(c_352, plain, (![B_54]: (k5_xboole_0(B_54, k1_xboole_0)=B_54)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_339])).
% 3.15/1.45  tff(c_32, plain, (![A_22, B_23]: (r1_xboole_0(k1_tarski(A_22), B_23) | r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.15/1.45  tff(c_385, plain, (![A_71, B_72]: (r2_hidden('#skF_1'(A_71, B_72), A_71) | r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.15/1.45  tff(c_14, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.15/1.45  tff(c_464, plain, (![A_78, B_79, B_80]: (~r1_xboole_0(A_78, B_79) | r1_tarski(k3_xboole_0(A_78, B_79), B_80))), inference(resolution, [status(thm)], [c_385, c_14])).
% 3.15/1.45  tff(c_24, plain, (![A_17]: (r1_tarski(k1_xboole_0, A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.15/1.45  tff(c_297, plain, (![B_61, A_62]: (B_61=A_62 | ~r1_tarski(B_61, A_62) | ~r1_tarski(A_62, B_61))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.15/1.45  tff(c_306, plain, (![A_17]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_297])).
% 3.15/1.45  tff(c_499, plain, (![A_86, B_87]: (k3_xboole_0(A_86, B_87)=k1_xboole_0 | ~r1_xboole_0(A_86, B_87))), inference(resolution, [status(thm)], [c_464, c_306])).
% 3.15/1.45  tff(c_640, plain, (![A_104, B_105]: (k3_xboole_0(k1_tarski(A_104), B_105)=k1_xboole_0 | r2_hidden(A_104, B_105))), inference(resolution, [status(thm)], [c_32, c_499])).
% 3.15/1.45  tff(c_345, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_327])).
% 3.15/1.45  tff(c_658, plain, (![B_105, A_104]: (k4_xboole_0(B_105, k1_tarski(A_104))=k5_xboole_0(B_105, k1_xboole_0) | r2_hidden(A_104, B_105))), inference(superposition, [status(thm), theory('equality')], [c_640, c_345])).
% 3.15/1.45  tff(c_702, plain, (![B_105, A_104]: (k4_xboole_0(B_105, k1_tarski(A_104))=B_105 | r2_hidden(A_104, B_105))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_658])).
% 3.15/1.45  tff(c_636, plain, (![A_101, B_102, C_103]: (k7_subset_1(A_101, B_102, C_103)=k4_xboole_0(B_102, C_103) | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.15/1.45  tff(c_639, plain, (![C_103]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', C_103)=k4_xboole_0('#skF_4', C_103))), inference(resolution, [status(thm)], [c_46, c_636])).
% 3.15/1.45  tff(c_834, plain, (![A_114, B_115]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_114))), B_115, k1_tarski(k1_xboole_0))=k2_yellow19(A_114, k3_yellow19(A_114, k2_struct_0(A_114), B_115)) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_114))))) | ~v13_waybel_0(B_115, k3_yellow_1(k2_struct_0(A_114))) | ~v2_waybel_0(B_115, k3_yellow_1(k2_struct_0(A_114))) | v1_xboole_0(B_115) | ~l1_struct_0(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.15/1.45  tff(c_836, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_834])).
% 3.15/1.45  tff(c_839, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_48, c_639, c_836])).
% 3.15/1.45  tff(c_840, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_58, c_54, c_839])).
% 3.15/1.45  tff(c_44, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.15/1.45  tff(c_949, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_840, c_44])).
% 3.15/1.45  tff(c_957, plain, (r2_hidden(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_702, c_949])).
% 3.15/1.45  tff(c_42, plain, (![C_38, B_36, A_32]: (~v1_xboole_0(C_38) | ~r2_hidden(C_38, B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_32)))) | ~v13_waybel_0(B_36, k3_yellow_1(A_32)) | ~v2_waybel_0(B_36, k3_yellow_1(A_32)) | ~v1_subset_1(B_36, u1_struct_0(k3_yellow_1(A_32))) | v1_xboole_0(B_36) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.15/1.45  tff(c_959, plain, (![A_32]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_32)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_32)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_32)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_32))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_957, c_42])).
% 3.15/1.45  tff(c_964, plain, (![A_32]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_32)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_32)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_32)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_32))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_959])).
% 3.15/1.45  tff(c_1120, plain, (![A_133]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_133)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_133)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_133)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_133))) | v1_xboole_0(A_133))), inference(negUnitSimplification, [status(thm)], [c_54, c_964])).
% 3.15/1.45  tff(c_1123, plain, (~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_46, c_1120])).
% 3.15/1.45  tff(c_1126, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_1123])).
% 3.15/1.45  tff(c_36, plain, (![A_27]: (~v1_xboole_0(k2_struct_0(A_27)) | ~l1_struct_0(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.15/1.45  tff(c_1129, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1126, c_36])).
% 3.15/1.45  tff(c_1132, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1129])).
% 3.15/1.45  tff(c_1134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1132])).
% 3.15/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.45  
% 3.15/1.45  Inference rules
% 3.15/1.45  ----------------------
% 3.15/1.45  #Ref     : 0
% 3.15/1.45  #Sup     : 256
% 3.15/1.45  #Fact    : 0
% 3.15/1.45  #Define  : 0
% 3.15/1.45  #Split   : 1
% 3.15/1.45  #Chain   : 0
% 3.15/1.45  #Close   : 0
% 3.15/1.45  
% 3.15/1.45  Ordering : KBO
% 3.15/1.45  
% 3.15/1.45  Simplification rules
% 3.15/1.45  ----------------------
% 3.15/1.45  #Subsume      : 64
% 3.15/1.45  #Demod        : 87
% 3.15/1.45  #Tautology    : 118
% 3.15/1.45  #SimpNegUnit  : 17
% 3.15/1.45  #BackRed      : 1
% 3.15/1.45  
% 3.15/1.45  #Partial instantiations: 0
% 3.15/1.45  #Strategies tried      : 1
% 3.15/1.45  
% 3.15/1.45  Timing (in seconds)
% 3.15/1.45  ----------------------
% 3.15/1.45  Preprocessing        : 0.33
% 3.15/1.45  Parsing              : 0.18
% 3.15/1.45  CNF conversion       : 0.02
% 3.15/1.45  Main loop            : 0.36
% 3.15/1.45  Inferencing          : 0.13
% 3.15/1.45  Reduction            : 0.13
% 3.15/1.45  Demodulation         : 0.10
% 3.15/1.45  BG Simplification    : 0.02
% 3.15/1.45  Subsumption          : 0.06
% 3.15/1.45  Abstraction          : 0.02
% 3.15/1.45  MUC search           : 0.00
% 3.15/1.45  Cooper               : 0.00
% 3.15/1.45  Total                : 0.72
% 3.15/1.45  Index Insertion      : 0.00
% 3.15/1.45  Index Deletion       : 0.00
% 3.15/1.45  Index Matching       : 0.00
% 3.15/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
