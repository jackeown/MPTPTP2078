%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:26 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 108 expanded)
%              Number of leaves         :   43 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  126 ( 249 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_156,negated_conjecture,(
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

tff(f_38,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_56,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_58,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_115,axiom,(
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

tff(f_136,axiom,(
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

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_52,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_48,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_46,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_44,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_126,plain,(
    ! [A_71,B_72] :
      ( k3_xboole_0(A_71,B_72) = k1_xboole_0
      | ~ r1_xboole_0(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_134,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_126])).

tff(c_197,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_209,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_197])).

tff(c_218,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_209])).

tff(c_192,plain,(
    ! [A_75,B_76] :
      ( r1_xboole_0(k1_tarski(A_75),B_76)
      | r2_hidden(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_196,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(k1_tarski(A_75),B_76) = k1_xboole_0
      | r2_hidden(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_192,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_573,plain,(
    ! [A_118,B_119] : k5_xboole_0(A_118,k3_xboole_0(B_119,A_118)) = k4_xboole_0(A_118,B_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_197])).

tff(c_586,plain,(
    ! [B_76,A_75] :
      ( k4_xboole_0(B_76,k1_tarski(A_75)) = k5_xboole_0(B_76,k1_xboole_0)
      | r2_hidden(A_75,B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_573])).

tff(c_606,plain,(
    ! [B_76,A_75] :
      ( k4_xboole_0(B_76,k1_tarski(A_75)) = B_76
      | r2_hidden(A_75,B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_586])).

tff(c_394,plain,(
    ! [A_96,B_97,C_98] :
      ( k7_subset_1(A_96,B_97,C_98) = k4_xboole_0(B_97,C_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_397,plain,(
    ! [C_98] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',C_98) = k4_xboole_0('#skF_5',C_98) ),
    inference(resolution,[status(thm)],[c_42,c_394])).

tff(c_734,plain,(
    ! [A_128,B_129] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_128))),B_129,k1_tarski(k1_xboole_0)) = k2_yellow19(A_128,k3_yellow19(A_128,k2_struct_0(A_128),B_129))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_128)))))
      | ~ v13_waybel_0(B_129,k3_yellow_1(k2_struct_0(A_128)))
      | ~ v2_waybel_0(B_129,k3_yellow_1(k2_struct_0(A_128)))
      | v1_xboole_0(B_129)
      | ~ l1_struct_0(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_736,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_734])).

tff(c_739,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_44,c_397,c_736])).

tff(c_740,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_50,c_739])).

tff(c_40,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_831,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_740,c_40])).

tff(c_839,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_831])).

tff(c_38,plain,(
    ! [C_56,B_54,A_50] :
      ( ~ v1_xboole_0(C_56)
      | ~ r2_hidden(C_56,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_50))))
      | ~ v13_waybel_0(B_54,k3_yellow_1(A_50))
      | ~ v2_waybel_0(B_54,k3_yellow_1(A_50))
      | ~ v1_subset_1(B_54,u1_struct_0(k3_yellow_1(A_50)))
      | v1_xboole_0(B_54)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_841,plain,(
    ! [A_50] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_50))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_50))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_50))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_50)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_839,c_38])).

tff(c_847,plain,(
    ! [A_50] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_50))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_50))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_50))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_50)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_841])).

tff(c_850,plain,(
    ! [A_136] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_136))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_136))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_136))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_136)))
      | v1_xboole_0(A_136) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_847])).

tff(c_853,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_850])).

tff(c_856,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_853])).

tff(c_32,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0(k2_struct_0(A_45))
      | ~ l1_struct_0(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_859,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_856,c_32])).

tff(c_865,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_859])).

tff(c_867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.48  
% 3.03/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.49  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 3.03/1.49  
% 3.03/1.49  %Foreground sorts:
% 3.03/1.49  
% 3.03/1.49  
% 3.03/1.49  %Background operators:
% 3.03/1.49  
% 3.03/1.49  
% 3.03/1.49  %Foreground operators:
% 3.03/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.03/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.49  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.03/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.03/1.49  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.03/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.03/1.49  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.03/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.03/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.03/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.03/1.49  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.03/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.03/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.03/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.03/1.49  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.03/1.49  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.03/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.03/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.03/1.49  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.03/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.03/1.49  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.03/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.03/1.49  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.03/1.49  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.03/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.03/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.03/1.49  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.03/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.03/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.49  
% 3.03/1.50  tff(f_156, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 3.03/1.50  tff(f_38, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.03/1.50  tff(f_56, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.03/1.50  tff(f_58, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.03/1.50  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.03/1.50  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.03/1.50  tff(f_63, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.03/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.03/1.50  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.03/1.50  tff(f_115, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 3.03/1.50  tff(f_136, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 3.03/1.50  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.03/1.50  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.03/1.50  tff(c_52, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.03/1.50  tff(c_48, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.03/1.50  tff(c_46, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.03/1.50  tff(c_44, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.03/1.50  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.03/1.50  tff(c_50, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.03/1.50  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.03/1.50  tff(c_20, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.03/1.50  tff(c_22, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.03/1.50  tff(c_126, plain, (![A_71, B_72]: (k3_xboole_0(A_71, B_72)=k1_xboole_0 | ~r1_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.03/1.50  tff(c_134, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_126])).
% 3.03/1.50  tff(c_197, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.03/1.50  tff(c_209, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_134, c_197])).
% 3.03/1.50  tff(c_218, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_209])).
% 3.03/1.50  tff(c_192, plain, (![A_75, B_76]: (r1_xboole_0(k1_tarski(A_75), B_76) | r2_hidden(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.03/1.50  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.03/1.50  tff(c_196, plain, (![A_75, B_76]: (k3_xboole_0(k1_tarski(A_75), B_76)=k1_xboole_0 | r2_hidden(A_75, B_76))), inference(resolution, [status(thm)], [c_192, c_8])).
% 3.03/1.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.03/1.50  tff(c_573, plain, (![A_118, B_119]: (k5_xboole_0(A_118, k3_xboole_0(B_119, A_118))=k4_xboole_0(A_118, B_119))), inference(superposition, [status(thm), theory('equality')], [c_2, c_197])).
% 3.03/1.50  tff(c_586, plain, (![B_76, A_75]: (k4_xboole_0(B_76, k1_tarski(A_75))=k5_xboole_0(B_76, k1_xboole_0) | r2_hidden(A_75, B_76))), inference(superposition, [status(thm), theory('equality')], [c_196, c_573])).
% 3.03/1.50  tff(c_606, plain, (![B_76, A_75]: (k4_xboole_0(B_76, k1_tarski(A_75))=B_76 | r2_hidden(A_75, B_76))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_586])).
% 3.03/1.50  tff(c_394, plain, (![A_96, B_97, C_98]: (k7_subset_1(A_96, B_97, C_98)=k4_xboole_0(B_97, C_98) | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.03/1.50  tff(c_397, plain, (![C_98]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', C_98)=k4_xboole_0('#skF_5', C_98))), inference(resolution, [status(thm)], [c_42, c_394])).
% 3.03/1.50  tff(c_734, plain, (![A_128, B_129]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_128))), B_129, k1_tarski(k1_xboole_0))=k2_yellow19(A_128, k3_yellow19(A_128, k2_struct_0(A_128), B_129)) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_128))))) | ~v13_waybel_0(B_129, k3_yellow_1(k2_struct_0(A_128))) | ~v2_waybel_0(B_129, k3_yellow_1(k2_struct_0(A_128))) | v1_xboole_0(B_129) | ~l1_struct_0(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.03/1.50  tff(c_736, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_734])).
% 3.03/1.50  tff(c_739, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_44, c_397, c_736])).
% 3.03/1.50  tff(c_740, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_54, c_50, c_739])).
% 3.03/1.50  tff(c_40, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.03/1.50  tff(c_831, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_740, c_40])).
% 3.03/1.50  tff(c_839, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_606, c_831])).
% 3.03/1.50  tff(c_38, plain, (![C_56, B_54, A_50]: (~v1_xboole_0(C_56) | ~r2_hidden(C_56, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_50)))) | ~v13_waybel_0(B_54, k3_yellow_1(A_50)) | ~v2_waybel_0(B_54, k3_yellow_1(A_50)) | ~v1_subset_1(B_54, u1_struct_0(k3_yellow_1(A_50))) | v1_xboole_0(B_54) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.03/1.50  tff(c_841, plain, (![A_50]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_50)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_50)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_50)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_50))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_839, c_38])).
% 3.03/1.50  tff(c_847, plain, (![A_50]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_50)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_50)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_50)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_50))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_50))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_841])).
% 3.03/1.50  tff(c_850, plain, (![A_136]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_136)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_136)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_136)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_136))) | v1_xboole_0(A_136))), inference(negUnitSimplification, [status(thm)], [c_50, c_847])).
% 3.03/1.50  tff(c_853, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_850])).
% 3.03/1.50  tff(c_856, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_853])).
% 3.03/1.50  tff(c_32, plain, (![A_45]: (~v1_xboole_0(k2_struct_0(A_45)) | ~l1_struct_0(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.03/1.50  tff(c_859, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_856, c_32])).
% 3.03/1.50  tff(c_865, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_859])).
% 3.03/1.50  tff(c_867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_865])).
% 3.03/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.50  
% 3.03/1.50  Inference rules
% 3.03/1.50  ----------------------
% 3.03/1.50  #Ref     : 0
% 3.03/1.50  #Sup     : 189
% 3.03/1.50  #Fact    : 0
% 3.03/1.50  #Define  : 0
% 3.03/1.50  #Split   : 0
% 3.03/1.50  #Chain   : 0
% 3.03/1.50  #Close   : 0
% 3.03/1.50  
% 3.03/1.50  Ordering : KBO
% 3.03/1.50  
% 3.03/1.50  Simplification rules
% 3.03/1.50  ----------------------
% 3.03/1.50  #Subsume      : 53
% 3.03/1.50  #Demod        : 66
% 3.03/1.50  #Tautology    : 100
% 3.03/1.50  #SimpNegUnit  : 19
% 3.03/1.50  #BackRed      : 1
% 3.03/1.50  
% 3.03/1.50  #Partial instantiations: 0
% 3.03/1.50  #Strategies tried      : 1
% 3.03/1.50  
% 3.03/1.50  Timing (in seconds)
% 3.03/1.50  ----------------------
% 3.03/1.51  Preprocessing        : 0.36
% 3.03/1.51  Parsing              : 0.21
% 3.03/1.51  CNF conversion       : 0.02
% 3.03/1.51  Main loop            : 0.32
% 3.03/1.51  Inferencing          : 0.12
% 3.03/1.51  Reduction            : 0.11
% 3.03/1.51  Demodulation         : 0.08
% 3.03/1.51  BG Simplification    : 0.02
% 3.03/1.51  Subsumption          : 0.05
% 3.03/1.51  Abstraction          : 0.02
% 3.03/1.51  MUC search           : 0.00
% 3.03/1.51  Cooper               : 0.00
% 3.03/1.51  Total                : 0.72
% 3.03/1.51  Index Insertion      : 0.00
% 3.03/1.51  Index Deletion       : 0.00
% 3.03/1.51  Index Matching       : 0.00
% 3.03/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
