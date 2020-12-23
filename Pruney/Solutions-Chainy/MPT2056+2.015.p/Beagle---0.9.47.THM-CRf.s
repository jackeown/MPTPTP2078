%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:27 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 109 expanded)
%              Number of leaves         :   46 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  139 ( 258 expanded)
%              Number of equality atoms :   30 (  44 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
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

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_86,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_113,axiom,(
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

tff(f_134,axiom,(
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

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_50,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_46,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_44,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_42,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_130,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_139,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = k2_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_130])).

tff(c_142,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_139])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(k1_tarski(A_18),B_19)
      | r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_3'(A_23),A_23)
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_152,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,B_75)
      | ~ r2_hidden(C_76,k3_xboole_0(A_74,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_169,plain,(
    ! [A_77,B_78] :
      ( ~ r1_xboole_0(A_77,B_78)
      | k3_xboole_0(A_77,B_78) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_152])).

tff(c_339,plain,(
    ! [A_106,B_107] :
      ( k3_xboole_0(k1_tarski(A_106),B_107) = k1_xboole_0
      | r2_hidden(A_106,B_107) ) ),
    inference(resolution,[status(thm)],[c_22,c_169])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_196,plain,(
    ! [A_83,B_84] : k5_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k4_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_205,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_196])).

tff(c_357,plain,(
    ! [B_107,A_106] :
      ( k4_xboole_0(B_107,k1_tarski(A_106)) = k5_xboole_0(B_107,k1_xboole_0)
      | r2_hidden(A_106,B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_205])).

tff(c_392,plain,(
    ! [B_107,A_106] :
      ( k4_xboole_0(B_107,k1_tarski(A_106)) = B_107
      | r2_hidden(A_106,B_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_357])).

tff(c_304,plain,(
    ! [A_99,B_100,C_101] :
      ( k7_subset_1(A_99,B_100,C_101) = k4_xboole_0(B_100,C_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_307,plain,(
    ! [C_101] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',C_101) = k4_xboole_0('#skF_5',C_101) ),
    inference(resolution,[status(thm)],[c_40,c_304])).

tff(c_556,plain,(
    ! [A_125,B_126] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_125))),B_126,k1_tarski(k1_xboole_0)) = k2_yellow19(A_125,k3_yellow19(A_125,k2_struct_0(A_125),B_126))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_125)))))
      | ~ v13_waybel_0(B_126,k3_yellow_1(k2_struct_0(A_125)))
      | ~ v2_waybel_0(B_126,k3_yellow_1(k2_struct_0(A_125)))
      | v1_xboole_0(B_126)
      | ~ l1_struct_0(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_558,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_556])).

tff(c_561,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_42,c_307,c_558])).

tff(c_562,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_561])).

tff(c_38,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_577,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_38])).

tff(c_585,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_577])).

tff(c_36,plain,(
    ! [C_56,B_54,A_50] :
      ( ~ v1_xboole_0(C_56)
      | ~ r2_hidden(C_56,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_50))))
      | ~ v13_waybel_0(B_54,k3_yellow_1(A_50))
      | ~ v2_waybel_0(B_54,k3_yellow_1(A_50))
      | ~ v1_subset_1(B_54,u1_struct_0(k3_yellow_1(A_50)))
      | v1_xboole_0(B_54)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_587,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_50))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_50))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_50))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_50)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_585,c_36])).

tff(c_593,plain,(
    ! [A_50] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_50))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_50))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_50))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_50)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_587])).

tff(c_719,plain,(
    ! [A_141] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_141))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_141))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_141))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_141)))
      | v1_xboole_0(A_141) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_593])).

tff(c_722,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_719])).

tff(c_725,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_722])).

tff(c_30,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0(k2_struct_0(A_45))
      | ~ l1_struct_0(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_728,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_725,c_30])).

tff(c_734,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_728])).

tff(c_736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_734])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n015.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 09:33:38 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.38  
% 2.63/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.38  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 2.63/1.38  
% 2.63/1.38  %Foreground sorts:
% 2.63/1.38  
% 2.63/1.38  
% 2.63/1.38  %Background operators:
% 2.63/1.38  
% 2.63/1.38  
% 2.63/1.38  %Foreground operators:
% 2.63/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.63/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.38  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.63/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.38  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.63/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.63/1.38  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.63/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.63/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.38  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.63/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.63/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.63/1.38  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.63/1.38  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.63/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.63/1.38  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.63/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.38  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.63/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.63/1.38  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.63/1.38  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.63/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.63/1.38  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.63/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.38  
% 2.92/1.40  tff(f_154, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 2.92/1.40  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.92/1.40  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.92/1.40  tff(f_54, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.92/1.40  tff(f_56, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.92/1.40  tff(f_61, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.92/1.40  tff(f_86, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.92/1.40  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.92/1.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.92/1.40  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.92/1.40  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.92/1.40  tff(f_113, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 2.92/1.40  tff(f_134, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 2.92/1.40  tff(f_94, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.92/1.40  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.40  tff(c_50, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.40  tff(c_46, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.40  tff(c_44, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.40  tff(c_42, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.40  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.40  tff(c_48, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.40  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.92/1.40  tff(c_16, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.92/1.40  tff(c_18, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.92/1.40  tff(c_130, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.92/1.40  tff(c_139, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=k2_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_130])).
% 2.92/1.40  tff(c_142, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_139])).
% 2.92/1.40  tff(c_22, plain, (![A_18, B_19]: (r1_xboole_0(k1_tarski(A_18), B_19) | r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.92/1.40  tff(c_28, plain, (![A_23]: (r2_hidden('#skF_3'(A_23), A_23) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.92/1.40  tff(c_152, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, B_75) | ~r2_hidden(C_76, k3_xboole_0(A_74, B_75)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.92/1.40  tff(c_169, plain, (![A_77, B_78]: (~r1_xboole_0(A_77, B_78) | k3_xboole_0(A_77, B_78)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_152])).
% 2.92/1.40  tff(c_339, plain, (![A_106, B_107]: (k3_xboole_0(k1_tarski(A_106), B_107)=k1_xboole_0 | r2_hidden(A_106, B_107))), inference(resolution, [status(thm)], [c_22, c_169])).
% 2.92/1.40  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.92/1.40  tff(c_196, plain, (![A_83, B_84]: (k5_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k4_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.92/1.40  tff(c_205, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_196])).
% 2.92/1.40  tff(c_357, plain, (![B_107, A_106]: (k4_xboole_0(B_107, k1_tarski(A_106))=k5_xboole_0(B_107, k1_xboole_0) | r2_hidden(A_106, B_107))), inference(superposition, [status(thm), theory('equality')], [c_339, c_205])).
% 2.92/1.40  tff(c_392, plain, (![B_107, A_106]: (k4_xboole_0(B_107, k1_tarski(A_106))=B_107 | r2_hidden(A_106, B_107))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_357])).
% 2.92/1.40  tff(c_304, plain, (![A_99, B_100, C_101]: (k7_subset_1(A_99, B_100, C_101)=k4_xboole_0(B_100, C_101) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.92/1.40  tff(c_307, plain, (![C_101]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', C_101)=k4_xboole_0('#skF_5', C_101))), inference(resolution, [status(thm)], [c_40, c_304])).
% 2.92/1.40  tff(c_556, plain, (![A_125, B_126]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_125))), B_126, k1_tarski(k1_xboole_0))=k2_yellow19(A_125, k3_yellow19(A_125, k2_struct_0(A_125), B_126)) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_125))))) | ~v13_waybel_0(B_126, k3_yellow_1(k2_struct_0(A_125))) | ~v2_waybel_0(B_126, k3_yellow_1(k2_struct_0(A_125))) | v1_xboole_0(B_126) | ~l1_struct_0(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.92/1.40  tff(c_558, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_556])).
% 2.92/1.40  tff(c_561, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_42, c_307, c_558])).
% 2.92/1.40  tff(c_562, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_561])).
% 2.92/1.40  tff(c_38, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.92/1.40  tff(c_577, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_562, c_38])).
% 2.92/1.40  tff(c_585, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_392, c_577])).
% 2.92/1.40  tff(c_36, plain, (![C_56, B_54, A_50]: (~v1_xboole_0(C_56) | ~r2_hidden(C_56, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_50)))) | ~v13_waybel_0(B_54, k3_yellow_1(A_50)) | ~v2_waybel_0(B_54, k3_yellow_1(A_50)) | ~v1_subset_1(B_54, u1_struct_0(k3_yellow_1(A_50))) | v1_xboole_0(B_54) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.92/1.40  tff(c_587, plain, (![A_50]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_50)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_50)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_50)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_50))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_585, c_36])).
% 2.92/1.40  tff(c_593, plain, (![A_50]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_50)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_50)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_50)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_50))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_587])).
% 2.92/1.40  tff(c_719, plain, (![A_141]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_141)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_141)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_141)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_141))) | v1_xboole_0(A_141))), inference(negUnitSimplification, [status(thm)], [c_48, c_593])).
% 2.92/1.40  tff(c_722, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_719])).
% 2.92/1.40  tff(c_725, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_722])).
% 2.92/1.40  tff(c_30, plain, (![A_45]: (~v1_xboole_0(k2_struct_0(A_45)) | ~l1_struct_0(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.92/1.40  tff(c_728, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_725, c_30])).
% 2.92/1.40  tff(c_734, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_728])).
% 2.92/1.40  tff(c_736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_734])).
% 2.92/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.40  
% 2.92/1.40  Inference rules
% 2.92/1.40  ----------------------
% 2.92/1.40  #Ref     : 0
% 2.92/1.40  #Sup     : 161
% 2.92/1.40  #Fact    : 0
% 2.92/1.40  #Define  : 0
% 2.92/1.40  #Split   : 1
% 2.92/1.40  #Chain   : 0
% 2.92/1.40  #Close   : 0
% 2.92/1.40  
% 2.92/1.40  Ordering : KBO
% 2.92/1.40  
% 2.92/1.40  Simplification rules
% 2.92/1.40  ----------------------
% 2.92/1.40  #Subsume      : 46
% 2.92/1.40  #Demod        : 34
% 2.92/1.40  #Tautology    : 72
% 2.92/1.40  #SimpNegUnit  : 6
% 2.92/1.40  #BackRed      : 1
% 2.92/1.40  
% 2.92/1.40  #Partial instantiations: 0
% 2.92/1.40  #Strategies tried      : 1
% 2.92/1.40  
% 2.92/1.40  Timing (in seconds)
% 2.92/1.40  ----------------------
% 2.92/1.40  Preprocessing        : 0.33
% 2.92/1.40  Parsing              : 0.18
% 2.92/1.40  CNF conversion       : 0.02
% 2.92/1.40  Main loop            : 0.30
% 2.92/1.40  Inferencing          : 0.12
% 2.92/1.40  Reduction            : 0.09
% 2.92/1.40  Demodulation         : 0.07
% 2.92/1.40  BG Simplification    : 0.02
% 2.92/1.40  Subsumption          : 0.05
% 2.92/1.40  Abstraction          : 0.02
% 2.92/1.40  MUC search           : 0.00
% 2.92/1.40  Cooper               : 0.00
% 2.92/1.40  Total                : 0.67
% 2.92/1.40  Index Insertion      : 0.00
% 2.92/1.40  Index Deletion       : 0.00
% 2.92/1.40  Index Matching       : 0.00
% 2.92/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
