%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:27 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 114 expanded)
%              Number of leaves         :   44 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  138 ( 277 expanded)
%              Number of equality atoms :   27 (  46 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_48,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_88,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_48,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_44,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_42,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_40,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_26,plain,(
    ! [A_19] :
      ( r2_hidden('#skF_3'(A_19),A_19)
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_108,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r1_xboole_0(A_65,B_66)
      | ~ r2_hidden(C_67,k3_xboole_0(A_65,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_125,plain,(
    ! [A_68,B_69] :
      ( ~ r1_xboole_0(A_68,B_69)
      | k3_xboole_0(A_68,B_69) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_108])).

tff(c_138,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_125])).

tff(c_216,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_228,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_216])).

tff(c_237,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_228])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(k1_tarski(A_12),B_13)
      | r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_498,plain,(
    ! [A_104,B_105] :
      ( k3_xboole_0(k1_tarski(A_104),B_105) = k1_xboole_0
      | r2_hidden(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_16,c_125])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_234,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_216])).

tff(c_507,plain,(
    ! [B_105,A_104] :
      ( k4_xboole_0(B_105,k1_tarski(A_104)) = k5_xboole_0(B_105,k1_xboole_0)
      | r2_hidden(A_104,B_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_234])).

tff(c_551,plain,(
    ! [B_105,A_104] :
      ( k4_xboole_0(B_105,k1_tarski(A_104)) = B_105
      | r2_hidden(A_104,B_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_507])).

tff(c_348,plain,(
    ! [A_83,B_84,C_85] :
      ( k7_subset_1(A_83,B_84,C_85) = k4_xboole_0(B_84,C_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_351,plain,(
    ! [C_85] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',C_85) = k4_xboole_0('#skF_5',C_85) ),
    inference(resolution,[status(thm)],[c_38,c_348])).

tff(c_684,plain,(
    ! [A_114,B_115] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_114))),B_115,k1_tarski(k1_xboole_0)) = k2_yellow19(A_114,k3_yellow19(A_114,k2_struct_0(A_114),B_115))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_114)))))
      | ~ v13_waybel_0(B_115,k3_yellow_1(k2_struct_0(A_114)))
      | ~ v2_waybel_0(B_115,k3_yellow_1(k2_struct_0(A_114)))
      | v1_xboole_0(B_115)
      | ~ l1_struct_0(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_686,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_684])).

tff(c_689,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_40,c_351,c_686])).

tff(c_690,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_689])).

tff(c_36,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_691,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_36])).

tff(c_699,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_691])).

tff(c_34,plain,(
    ! [C_52,B_50,A_46] :
      ( ~ v1_xboole_0(C_52)
      | ~ r2_hidden(C_52,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_46))))
      | ~ v13_waybel_0(B_50,k3_yellow_1(A_46))
      | ~ v2_waybel_0(B_50,k3_yellow_1(A_46))
      | ~ v1_subset_1(B_50,u1_struct_0(k3_yellow_1(A_46)))
      | v1_xboole_0(B_50)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_701,plain,(
    ! [A_46] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_46))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_46))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_46))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_46)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_699,c_34])).

tff(c_704,plain,(
    ! [A_46] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_46))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_46))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_46))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_46)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_701])).

tff(c_787,plain,(
    ! [A_120] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_120))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_120))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_120))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_120)))
      | v1_xboole_0(A_120) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_704])).

tff(c_790,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_787])).

tff(c_793,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_790])).

tff(c_28,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(k2_struct_0(A_41))
      | ~ l1_struct_0(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_796,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_793,c_28])).

tff(c_799,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_796])).

tff(c_801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.39  
% 2.79/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.39  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 2.79/1.39  
% 2.79/1.39  %Foreground sorts:
% 2.79/1.39  
% 2.79/1.39  
% 2.79/1.39  %Background operators:
% 2.79/1.39  
% 2.79/1.39  
% 2.79/1.39  %Foreground operators:
% 2.79/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.79/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.39  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.79/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.39  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.79/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.79/1.39  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.79/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.79/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.39  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.79/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.79/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.79/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.79/1.39  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.79/1.39  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.79/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.79/1.39  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.39  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.39  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.79/1.39  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.79/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.79/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.79/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.79/1.39  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.79/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.39  
% 2.79/1.41  tff(f_156, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 2.79/1.41  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.79/1.41  tff(f_46, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.79/1.41  tff(f_48, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.79/1.41  tff(f_88, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 2.79/1.41  tff(f_42, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.79/1.41  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.79/1.41  tff(f_53, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.79/1.41  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.79/1.41  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.79/1.41  tff(f_115, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 2.79/1.41  tff(f_136, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 2.79/1.41  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.79/1.41  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.79/1.41  tff(c_48, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.79/1.41  tff(c_44, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.79/1.41  tff(c_42, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.79/1.41  tff(c_40, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.79/1.41  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.79/1.41  tff(c_46, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.79/1.41  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.79/1.41  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.79/1.41  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.79/1.41  tff(c_26, plain, (![A_19]: (r2_hidden('#skF_3'(A_19), A_19) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.79/1.41  tff(c_108, plain, (![A_65, B_66, C_67]: (~r1_xboole_0(A_65, B_66) | ~r2_hidden(C_67, k3_xboole_0(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.79/1.41  tff(c_125, plain, (![A_68, B_69]: (~r1_xboole_0(A_68, B_69) | k3_xboole_0(A_68, B_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_108])).
% 2.79/1.41  tff(c_138, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_125])).
% 2.79/1.41  tff(c_216, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.79/1.41  tff(c_228, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_138, c_216])).
% 2.79/1.41  tff(c_237, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_228])).
% 2.79/1.41  tff(c_16, plain, (![A_12, B_13]: (r1_xboole_0(k1_tarski(A_12), B_13) | r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.79/1.41  tff(c_498, plain, (![A_104, B_105]: (k3_xboole_0(k1_tarski(A_104), B_105)=k1_xboole_0 | r2_hidden(A_104, B_105))), inference(resolution, [status(thm)], [c_16, c_125])).
% 2.79/1.41  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.79/1.41  tff(c_234, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_216])).
% 2.79/1.41  tff(c_507, plain, (![B_105, A_104]: (k4_xboole_0(B_105, k1_tarski(A_104))=k5_xboole_0(B_105, k1_xboole_0) | r2_hidden(A_104, B_105))), inference(superposition, [status(thm), theory('equality')], [c_498, c_234])).
% 2.79/1.41  tff(c_551, plain, (![B_105, A_104]: (k4_xboole_0(B_105, k1_tarski(A_104))=B_105 | r2_hidden(A_104, B_105))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_507])).
% 2.79/1.41  tff(c_348, plain, (![A_83, B_84, C_85]: (k7_subset_1(A_83, B_84, C_85)=k4_xboole_0(B_84, C_85) | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.79/1.41  tff(c_351, plain, (![C_85]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', C_85)=k4_xboole_0('#skF_5', C_85))), inference(resolution, [status(thm)], [c_38, c_348])).
% 2.79/1.41  tff(c_684, plain, (![A_114, B_115]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_114))), B_115, k1_tarski(k1_xboole_0))=k2_yellow19(A_114, k3_yellow19(A_114, k2_struct_0(A_114), B_115)) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_114))))) | ~v13_waybel_0(B_115, k3_yellow_1(k2_struct_0(A_114))) | ~v2_waybel_0(B_115, k3_yellow_1(k2_struct_0(A_114))) | v1_xboole_0(B_115) | ~l1_struct_0(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.79/1.41  tff(c_686, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_684])).
% 2.79/1.41  tff(c_689, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_40, c_351, c_686])).
% 2.79/1.41  tff(c_690, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_689])).
% 2.79/1.41  tff(c_36, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_156])).
% 2.79/1.41  tff(c_691, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_690, c_36])).
% 2.79/1.41  tff(c_699, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_551, c_691])).
% 2.79/1.41  tff(c_34, plain, (![C_52, B_50, A_46]: (~v1_xboole_0(C_52) | ~r2_hidden(C_52, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_46)))) | ~v13_waybel_0(B_50, k3_yellow_1(A_46)) | ~v2_waybel_0(B_50, k3_yellow_1(A_46)) | ~v1_subset_1(B_50, u1_struct_0(k3_yellow_1(A_46))) | v1_xboole_0(B_50) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.79/1.41  tff(c_701, plain, (![A_46]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_46)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_46)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_46)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_46))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_699, c_34])).
% 2.79/1.41  tff(c_704, plain, (![A_46]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_46)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_46)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_46)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_46))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_701])).
% 2.79/1.41  tff(c_787, plain, (![A_120]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_120)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_120)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_120)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_120))) | v1_xboole_0(A_120))), inference(negUnitSimplification, [status(thm)], [c_46, c_704])).
% 2.79/1.41  tff(c_790, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_787])).
% 2.79/1.41  tff(c_793, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_790])).
% 2.79/1.41  tff(c_28, plain, (![A_41]: (~v1_xboole_0(k2_struct_0(A_41)) | ~l1_struct_0(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.79/1.41  tff(c_796, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_793, c_28])).
% 2.79/1.41  tff(c_799, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_796])).
% 2.79/1.41  tff(c_801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_799])).
% 2.79/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.41  
% 2.79/1.41  Inference rules
% 2.79/1.41  ----------------------
% 2.79/1.41  #Ref     : 0
% 2.79/1.41  #Sup     : 170
% 2.79/1.41  #Fact    : 0
% 2.79/1.41  #Define  : 0
% 2.79/1.41  #Split   : 0
% 2.79/1.41  #Chain   : 0
% 2.79/1.41  #Close   : 0
% 2.79/1.41  
% 2.79/1.41  Ordering : KBO
% 2.79/1.41  
% 2.79/1.41  Simplification rules
% 2.79/1.41  ----------------------
% 2.79/1.41  #Subsume      : 41
% 2.79/1.41  #Demod        : 45
% 2.79/1.41  #Tautology    : 96
% 2.79/1.41  #SimpNegUnit  : 21
% 2.79/1.41  #BackRed      : 1
% 2.79/1.41  
% 2.79/1.41  #Partial instantiations: 0
% 2.79/1.41  #Strategies tried      : 1
% 2.79/1.41  
% 2.79/1.41  Timing (in seconds)
% 2.79/1.41  ----------------------
% 2.79/1.41  Preprocessing        : 0.33
% 2.79/1.41  Parsing              : 0.18
% 2.79/1.41  CNF conversion       : 0.02
% 2.79/1.41  Main loop            : 0.31
% 2.79/1.41  Inferencing          : 0.12
% 2.79/1.41  Reduction            : 0.11
% 2.79/1.41  Demodulation         : 0.08
% 2.79/1.41  BG Simplification    : 0.02
% 2.79/1.41  Subsumption          : 0.05
% 2.79/1.41  Abstraction          : 0.02
% 2.79/1.41  MUC search           : 0.00
% 2.79/1.41  Cooper               : 0.00
% 2.79/1.41  Total                : 0.68
% 2.79/1.41  Index Insertion      : 0.00
% 2.79/1.41  Index Deletion       : 0.00
% 2.79/1.41  Index Matching       : 0.00
% 2.79/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
