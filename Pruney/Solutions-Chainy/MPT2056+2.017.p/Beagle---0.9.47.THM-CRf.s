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
% DateTime   : Thu Dec  3 10:31:27 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 114 expanded)
%              Number of leaves         :   44 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  137 ( 275 expanded)
%              Number of equality atoms :   27 (  46 expanded)
%              Maximal formula depth    :   15 (   4 average)
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

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_48,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_86,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_mcart_1)).

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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_48,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_44,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_42,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_40,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

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
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_108,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r1_xboole_0(A_61,B_62)
      | ~ r2_hidden(C_63,k3_xboole_0(A_61,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_125,plain,(
    ! [A_64,B_65] :
      ( ~ r1_xboole_0(A_64,B_65)
      | k3_xboole_0(A_64,B_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_108])).

tff(c_138,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_125])).

tff(c_216,plain,(
    ! [A_69,B_70] : k5_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = k4_xboole_0(A_69,B_70) ),
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
    ! [A_99,B_100] :
      ( k3_xboole_0(k1_tarski(A_99),B_100) = k1_xboole_0
      | r2_hidden(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_16,c_125])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_234,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_216])).

tff(c_507,plain,(
    ! [B_100,A_99] :
      ( k4_xboole_0(B_100,k1_tarski(A_99)) = k5_xboole_0(B_100,k1_xboole_0)
      | r2_hidden(A_99,B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_498,c_234])).

tff(c_551,plain,(
    ! [B_100,A_99] :
      ( k4_xboole_0(B_100,k1_tarski(A_99)) = B_100
      | r2_hidden(A_99,B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_507])).

tff(c_348,plain,(
    ! [A_79,B_80,C_81] :
      ( k7_subset_1(A_79,B_80,C_81) = k4_xboole_0(B_80,C_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_351,plain,(
    ! [C_81] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',C_81) = k4_xboole_0('#skF_5',C_81) ),
    inference(resolution,[status(thm)],[c_38,c_348])).

tff(c_684,plain,(
    ! [A_109,B_110] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_109))),B_110,k1_tarski(k1_xboole_0)) = k2_yellow19(A_109,k3_yellow19(A_109,k2_struct_0(A_109),B_110))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_109)))))
      | ~ v13_waybel_0(B_110,k3_yellow_1(k2_struct_0(A_109)))
      | ~ v2_waybel_0(B_110,k3_yellow_1(k2_struct_0(A_109)))
      | v1_xboole_0(B_110)
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

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
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_691,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_690,c_36])).

tff(c_699,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_691])).

tff(c_34,plain,(
    ! [C_48,B_46,A_42] :
      ( ~ v1_xboole_0(C_48)
      | ~ r2_hidden(C_48,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_42))))
      | ~ v13_waybel_0(B_46,k3_yellow_1(A_42))
      | ~ v2_waybel_0(B_46,k3_yellow_1(A_42))
      | ~ v1_subset_1(B_46,u1_struct_0(k3_yellow_1(A_42)))
      | v1_xboole_0(B_46)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_701,plain,(
    ! [A_42] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_42))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_42))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_42))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_42)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_699,c_34])).

tff(c_704,plain,(
    ! [A_42] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_42))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_42))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_42))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_42)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_701])).

tff(c_814,plain,(
    ! [A_126] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_126))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_126))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_126))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_126)))
      | v1_xboole_0(A_126) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_704])).

tff(c_817,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_814])).

tff(c_820,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_817])).

tff(c_28,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(k2_struct_0(A_37))
      | ~ l1_struct_0(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_823,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_820,c_28])).

tff(c_826,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_823])).

tff(c_828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_826])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.38  
% 2.82/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.38  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 2.82/1.38  
% 2.82/1.38  %Foreground sorts:
% 2.82/1.38  
% 2.82/1.38  
% 2.82/1.38  %Background operators:
% 2.82/1.38  
% 2.82/1.38  
% 2.82/1.38  %Foreground operators:
% 2.82/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.82/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.82/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.38  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.82/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.38  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.82/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.38  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.82/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.82/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.38  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.82/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.82/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.82/1.38  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.82/1.38  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.82/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.82/1.38  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.82/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.38  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.82/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.38  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.82/1.38  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.82/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.82/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.82/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.82/1.38  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.82/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.38  
% 2.82/1.40  tff(f_154, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 2.82/1.40  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.82/1.40  tff(f_46, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.82/1.40  tff(f_48, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.82/1.40  tff(f_86, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_mcart_1)).
% 2.82/1.40  tff(f_42, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.82/1.40  tff(f_44, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.82/1.40  tff(f_53, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.82/1.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.82/1.40  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.82/1.40  tff(f_113, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 2.82/1.40  tff(f_134, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 2.82/1.40  tff(f_94, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.82/1.40  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.82/1.40  tff(c_48, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.82/1.40  tff(c_44, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.82/1.40  tff(c_42, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.82/1.40  tff(c_40, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.82/1.40  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.82/1.40  tff(c_46, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.82/1.40  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.82/1.40  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.82/1.40  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.82/1.40  tff(c_26, plain, (![A_19]: (r2_hidden('#skF_3'(A_19), A_19) | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.82/1.40  tff(c_108, plain, (![A_61, B_62, C_63]: (~r1_xboole_0(A_61, B_62) | ~r2_hidden(C_63, k3_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.82/1.40  tff(c_125, plain, (![A_64, B_65]: (~r1_xboole_0(A_64, B_65) | k3_xboole_0(A_64, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_108])).
% 2.82/1.40  tff(c_138, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_125])).
% 2.82/1.40  tff(c_216, plain, (![A_69, B_70]: (k5_xboole_0(A_69, k3_xboole_0(A_69, B_70))=k4_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.82/1.40  tff(c_228, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_138, c_216])).
% 2.82/1.40  tff(c_237, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_228])).
% 2.82/1.40  tff(c_16, plain, (![A_12, B_13]: (r1_xboole_0(k1_tarski(A_12), B_13) | r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.82/1.40  tff(c_498, plain, (![A_99, B_100]: (k3_xboole_0(k1_tarski(A_99), B_100)=k1_xboole_0 | r2_hidden(A_99, B_100))), inference(resolution, [status(thm)], [c_16, c_125])).
% 2.82/1.40  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.82/1.40  tff(c_234, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_216])).
% 2.82/1.40  tff(c_507, plain, (![B_100, A_99]: (k4_xboole_0(B_100, k1_tarski(A_99))=k5_xboole_0(B_100, k1_xboole_0) | r2_hidden(A_99, B_100))), inference(superposition, [status(thm), theory('equality')], [c_498, c_234])).
% 2.82/1.40  tff(c_551, plain, (![B_100, A_99]: (k4_xboole_0(B_100, k1_tarski(A_99))=B_100 | r2_hidden(A_99, B_100))), inference(demodulation, [status(thm), theory('equality')], [c_237, c_507])).
% 2.82/1.40  tff(c_348, plain, (![A_79, B_80, C_81]: (k7_subset_1(A_79, B_80, C_81)=k4_xboole_0(B_80, C_81) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.82/1.40  tff(c_351, plain, (![C_81]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', C_81)=k4_xboole_0('#skF_5', C_81))), inference(resolution, [status(thm)], [c_38, c_348])).
% 2.82/1.40  tff(c_684, plain, (![A_109, B_110]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_109))), B_110, k1_tarski(k1_xboole_0))=k2_yellow19(A_109, k3_yellow19(A_109, k2_struct_0(A_109), B_110)) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_109))))) | ~v13_waybel_0(B_110, k3_yellow_1(k2_struct_0(A_109))) | ~v2_waybel_0(B_110, k3_yellow_1(k2_struct_0(A_109))) | v1_xboole_0(B_110) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.82/1.40  tff(c_686, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_38, c_684])).
% 2.82/1.40  tff(c_689, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_40, c_351, c_686])).
% 2.82/1.40  tff(c_690, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_689])).
% 2.82/1.40  tff(c_36, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.82/1.40  tff(c_691, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_690, c_36])).
% 2.82/1.40  tff(c_699, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_551, c_691])).
% 2.82/1.40  tff(c_34, plain, (![C_48, B_46, A_42]: (~v1_xboole_0(C_48) | ~r2_hidden(C_48, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_42)))) | ~v13_waybel_0(B_46, k3_yellow_1(A_42)) | ~v2_waybel_0(B_46, k3_yellow_1(A_42)) | ~v1_subset_1(B_46, u1_struct_0(k3_yellow_1(A_42))) | v1_xboole_0(B_46) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.82/1.40  tff(c_701, plain, (![A_42]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_42)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_42)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_42)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_42))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_699, c_34])).
% 2.82/1.40  tff(c_704, plain, (![A_42]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_42)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_42)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_42)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_42))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_701])).
% 2.82/1.40  tff(c_814, plain, (![A_126]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_126)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_126)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_126)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_126))) | v1_xboole_0(A_126))), inference(negUnitSimplification, [status(thm)], [c_46, c_704])).
% 2.82/1.40  tff(c_817, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_814])).
% 2.82/1.40  tff(c_820, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_817])).
% 2.82/1.40  tff(c_28, plain, (![A_37]: (~v1_xboole_0(k2_struct_0(A_37)) | ~l1_struct_0(A_37) | v2_struct_0(A_37))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.82/1.40  tff(c_823, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_820, c_28])).
% 2.82/1.40  tff(c_826, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_823])).
% 2.82/1.40  tff(c_828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_826])).
% 2.82/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.40  
% 2.82/1.40  Inference rules
% 2.82/1.40  ----------------------
% 2.82/1.40  #Ref     : 0
% 2.82/1.40  #Sup     : 176
% 2.82/1.40  #Fact    : 0
% 2.82/1.40  #Define  : 0
% 2.82/1.40  #Split   : 0
% 2.82/1.40  #Chain   : 0
% 2.82/1.40  #Close   : 0
% 2.82/1.40  
% 2.82/1.40  Ordering : KBO
% 2.82/1.40  
% 2.82/1.40  Simplification rules
% 2.82/1.40  ----------------------
% 2.82/1.40  #Subsume      : 41
% 2.82/1.40  #Demod        : 45
% 2.82/1.40  #Tautology    : 96
% 2.82/1.40  #SimpNegUnit  : 21
% 2.82/1.40  #BackRed      : 1
% 2.82/1.40  
% 2.82/1.40  #Partial instantiations: 0
% 2.82/1.40  #Strategies tried      : 1
% 2.82/1.40  
% 2.82/1.40  Timing (in seconds)
% 2.82/1.40  ----------------------
% 2.82/1.40  Preprocessing        : 0.33
% 2.82/1.40  Parsing              : 0.18
% 2.82/1.40  CNF conversion       : 0.02
% 2.82/1.40  Main loop            : 0.30
% 2.82/1.40  Inferencing          : 0.12
% 2.82/1.40  Reduction            : 0.10
% 2.82/1.40  Demodulation         : 0.07
% 2.82/1.40  BG Simplification    : 0.02
% 2.82/1.40  Subsumption          : 0.05
% 2.82/1.40  Abstraction          : 0.02
% 2.82/1.40  MUC search           : 0.00
% 2.82/1.40  Cooper               : 0.00
% 2.82/1.40  Total                : 0.67
% 2.82/1.40  Index Insertion      : 0.00
% 2.82/1.40  Index Deletion       : 0.00
% 2.82/1.40  Index Matching       : 0.00
% 2.82/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
