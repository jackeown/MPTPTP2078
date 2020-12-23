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
% DateTime   : Thu Dec  3 10:31:30 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 111 expanded)
%              Number of leaves         :   41 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  138 ( 269 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_61,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_40,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_80,axiom,(
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

tff(f_101,axiom,(
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

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_64,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_68,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_64])).

tff(c_121,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(u1_struct_0(A_41))
      | ~ l1_struct_0(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_124,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_121])).

tff(c_126,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_1'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_124])).

tff(c_127,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_126])).

tff(c_38,plain,(
    v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_36,plain,(
    v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_34,plain,(
    v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,(
    ! [A_35,B_36] :
      ( k3_xboole_0(A_35,B_36) = k1_xboole_0
      | ~ r1_xboole_0(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_82])).

tff(c_152,plain,(
    ! [A_48,B_49] : k5_xboole_0(A_48,k3_xboole_0(A_48,B_49)) = k4_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_164,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_152])).

tff(c_167,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_164])).

tff(c_91,plain,(
    ! [A_37,B_38] :
      ( r1_xboole_0(k1_tarski(A_37),B_38)
      | r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_136,plain,(
    ! [B_44,A_45] :
      ( r1_xboole_0(B_44,k1_tarski(A_45))
      | r2_hidden(A_45,B_44) ) ),
    inference(resolution,[status(thm)],[c_91,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_234,plain,(
    ! [B_59,A_60] :
      ( k3_xboole_0(B_59,k1_tarski(A_60)) = k1_xboole_0
      | r2_hidden(A_60,B_59) ) ),
    inference(resolution,[status(thm)],[c_136,c_2])).

tff(c_10,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_246,plain,(
    ! [B_59,A_60] :
      ( k4_xboole_0(B_59,k1_tarski(A_60)) = k5_xboole_0(B_59,k1_xboole_0)
      | r2_hidden(A_60,B_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_10])).

tff(c_265,plain,(
    ! [B_59,A_60] :
      ( k4_xboole_0(B_59,k1_tarski(A_60)) = B_59
      | r2_hidden(A_60,B_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_246])).

tff(c_218,plain,(
    ! [A_54,B_55,C_56] :
      ( k7_subset_1(A_54,B_55,C_56) = k4_xboole_0(B_55,C_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_221,plain,(
    ! [C_56] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',C_56) = k4_xboole_0('#skF_2',C_56) ),
    inference(resolution,[status(thm)],[c_32,c_218])).

tff(c_328,plain,(
    ! [A_69,B_70] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_69))),B_70,k1_tarski(k1_xboole_0)) = k2_yellow19(A_69,k3_yellow19(A_69,k2_struct_0(A_69),B_70))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_69)))))
      | ~ v13_waybel_0(B_70,k3_yellow_1(k2_struct_0(A_69)))
      | ~ v2_waybel_0(B_70,k3_yellow_1(k2_struct_0(A_69)))
      | v1_xboole_0(B_70)
      | ~ l1_struct_0(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_330,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))),'#skF_2',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2'))
    | ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | v1_xboole_0('#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_328])).

tff(c_333,plain,
    ( k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_34,c_221,c_330])).

tff(c_334,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) = k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_40,c_333])).

tff(c_30,plain,(
    k2_yellow19('#skF_1',k3_yellow19('#skF_1',k2_struct_0('#skF_1'),'#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_335,plain,(
    k4_xboole_0('#skF_2',k1_tarski(k1_xboole_0)) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_30])).

tff(c_343,plain,(
    r2_hidden(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_335])).

tff(c_28,plain,(
    ! [C_26,B_24,A_20] :
      ( ~ v1_xboole_0(C_26)
      | ~ r2_hidden(C_26,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_20))))
      | ~ v13_waybel_0(B_24,k3_yellow_1(A_20))
      | ~ v2_waybel_0(B_24,k3_yellow_1(A_20))
      | ~ v1_subset_1(B_24,u1_struct_0(k3_yellow_1(A_20)))
      | v1_xboole_0(B_24)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_345,plain,(
    ! [A_20] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_20))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_20))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_20))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_20)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_343,c_28])).

tff(c_348,plain,(
    ! [A_20] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_20))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_20))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_20))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_20)))
      | v1_xboole_0('#skF_2')
      | v1_xboole_0(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_345])).

tff(c_350,plain,(
    ! [A_71] :
      ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_71))))
      | ~ v13_waybel_0('#skF_2',k3_yellow_1(A_71))
      | ~ v2_waybel_0('#skF_2',k3_yellow_1(A_71))
      | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(A_71)))
      | v1_xboole_0(A_71) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_348])).

tff(c_353,plain,
    ( ~ v13_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v2_waybel_0('#skF_2',k3_yellow_1(k2_struct_0('#skF_1')))
    | ~ v1_subset_1('#skF_2',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))
    | v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_350])).

tff(c_356,plain,(
    v1_xboole_0(k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_353])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:01 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.31  
% 1.98/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.31  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_2 > #skF_1
% 1.98/1.31  
% 1.98/1.31  %Foreground sorts:
% 1.98/1.31  
% 1.98/1.31  
% 1.98/1.31  %Background operators:
% 1.98/1.31  
% 1.98/1.31  
% 1.98/1.31  %Foreground operators:
% 1.98/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.98/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.31  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 1.98/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.31  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.98/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.98/1.31  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.98/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.31  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 1.98/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.98/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.31  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.31  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 1.98/1.31  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.31  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 1.98/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.98/1.31  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 1.98/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.31  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 1.98/1.31  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 1.98/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.98/1.31  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 1.98/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.31  
% 2.36/1.33  tff(f_121, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 2.36/1.33  tff(f_53, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.36/1.33  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.36/1.33  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.36/1.33  tff(f_38, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.36/1.33  tff(f_40, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.36/1.33  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.36/1.33  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.36/1.33  tff(f_45, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.36/1.33  tff(f_34, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.36/1.33  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.36/1.33  tff(f_80, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 2.36/1.33  tff(f_101, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 2.36/1.33  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.36/1.33  tff(c_42, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.36/1.33  tff(c_64, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.36/1.33  tff(c_68, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_64])).
% 2.36/1.33  tff(c_121, plain, (![A_41]: (~v1_xboole_0(u1_struct_0(A_41)) | ~l1_struct_0(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.36/1.33  tff(c_124, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_68, c_121])).
% 2.36/1.33  tff(c_126, plain, (~v1_xboole_0(k2_struct_0('#skF_1')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_124])).
% 2.36/1.33  tff(c_127, plain, (~v1_xboole_0(k2_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_126])).
% 2.36/1.33  tff(c_38, plain, (v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.36/1.33  tff(c_36, plain, (v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.36/1.33  tff(c_34, plain, (v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.36/1.33  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.36/1.33  tff(c_40, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.36/1.33  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.36/1.33  tff(c_12, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.36/1.33  tff(c_14, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.36/1.33  tff(c_82, plain, (![A_35, B_36]: (k3_xboole_0(A_35, B_36)=k1_xboole_0 | ~r1_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.33  tff(c_90, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_82])).
% 2.36/1.33  tff(c_152, plain, (![A_48, B_49]: (k5_xboole_0(A_48, k3_xboole_0(A_48, B_49))=k4_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.36/1.33  tff(c_164, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_90, c_152])).
% 2.36/1.33  tff(c_167, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_164])).
% 2.36/1.33  tff(c_91, plain, (![A_37, B_38]: (r1_xboole_0(k1_tarski(A_37), B_38) | r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.36/1.33  tff(c_8, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.36/1.33  tff(c_136, plain, (![B_44, A_45]: (r1_xboole_0(B_44, k1_tarski(A_45)) | r2_hidden(A_45, B_44))), inference(resolution, [status(thm)], [c_91, c_8])).
% 2.36/1.33  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.33  tff(c_234, plain, (![B_59, A_60]: (k3_xboole_0(B_59, k1_tarski(A_60))=k1_xboole_0 | r2_hidden(A_60, B_59))), inference(resolution, [status(thm)], [c_136, c_2])).
% 2.36/1.33  tff(c_10, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.36/1.33  tff(c_246, plain, (![B_59, A_60]: (k4_xboole_0(B_59, k1_tarski(A_60))=k5_xboole_0(B_59, k1_xboole_0) | r2_hidden(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_234, c_10])).
% 2.36/1.33  tff(c_265, plain, (![B_59, A_60]: (k4_xboole_0(B_59, k1_tarski(A_60))=B_59 | r2_hidden(A_60, B_59))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_246])).
% 2.36/1.33  tff(c_218, plain, (![A_54, B_55, C_56]: (k7_subset_1(A_54, B_55, C_56)=k4_xboole_0(B_55, C_56) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.36/1.33  tff(c_221, plain, (![C_56]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))), '#skF_2', C_56)=k4_xboole_0('#skF_2', C_56))), inference(resolution, [status(thm)], [c_32, c_218])).
% 2.36/1.33  tff(c_328, plain, (![A_69, B_70]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_69))), B_70, k1_tarski(k1_xboole_0))=k2_yellow19(A_69, k3_yellow19(A_69, k2_struct_0(A_69), B_70)) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_69))))) | ~v13_waybel_0(B_70, k3_yellow_1(k2_struct_0(A_69))) | ~v2_waybel_0(B_70, k3_yellow_1(k2_struct_0(A_69))) | v1_xboole_0(B_70) | ~l1_struct_0(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.36/1.33  tff(c_330, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1'))), '#skF_2', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2')) | ~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | v1_xboole_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_32, c_328])).
% 2.36/1.33  tff(c_333, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_34, c_221, c_330])).
% 2.36/1.33  tff(c_334, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))=k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_44, c_40, c_333])).
% 2.36/1.33  tff(c_30, plain, (k2_yellow19('#skF_1', k3_yellow19('#skF_1', k2_struct_0('#skF_1'), '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.36/1.33  tff(c_335, plain, (k4_xboole_0('#skF_2', k1_tarski(k1_xboole_0))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_334, c_30])).
% 2.36/1.33  tff(c_343, plain, (r2_hidden(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_265, c_335])).
% 2.36/1.33  tff(c_28, plain, (![C_26, B_24, A_20]: (~v1_xboole_0(C_26) | ~r2_hidden(C_26, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_20)))) | ~v13_waybel_0(B_24, k3_yellow_1(A_20)) | ~v2_waybel_0(B_24, k3_yellow_1(A_20)) | ~v1_subset_1(B_24, u1_struct_0(k3_yellow_1(A_20))) | v1_xboole_0(B_24) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.36/1.33  tff(c_345, plain, (![A_20]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_20)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_20)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_20)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_20))) | v1_xboole_0('#skF_2') | v1_xboole_0(A_20))), inference(resolution, [status(thm)], [c_343, c_28])).
% 2.36/1.33  tff(c_348, plain, (![A_20]: (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_20)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_20)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_20)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_20))) | v1_xboole_0('#skF_2') | v1_xboole_0(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_345])).
% 2.36/1.33  tff(c_350, plain, (![A_71]: (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_71)))) | ~v13_waybel_0('#skF_2', k3_yellow_1(A_71)) | ~v2_waybel_0('#skF_2', k3_yellow_1(A_71)) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(A_71))) | v1_xboole_0(A_71))), inference(negUnitSimplification, [status(thm)], [c_40, c_348])).
% 2.36/1.33  tff(c_353, plain, (~v13_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v2_waybel_0('#skF_2', k3_yellow_1(k2_struct_0('#skF_1'))) | ~v1_subset_1('#skF_2', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_1')))) | v1_xboole_0(k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_350])).
% 2.36/1.33  tff(c_356, plain, (v1_xboole_0(k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_353])).
% 2.36/1.33  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_356])).
% 2.36/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.33  
% 2.36/1.33  Inference rules
% 2.36/1.33  ----------------------
% 2.36/1.33  #Ref     : 0
% 2.36/1.33  #Sup     : 71
% 2.36/1.33  #Fact    : 0
% 2.36/1.33  #Define  : 0
% 2.36/1.33  #Split   : 0
% 2.36/1.33  #Chain   : 0
% 2.36/1.33  #Close   : 0
% 2.36/1.33  
% 2.36/1.33  Ordering : KBO
% 2.36/1.33  
% 2.36/1.33  Simplification rules
% 2.36/1.33  ----------------------
% 2.36/1.33  #Subsume      : 4
% 2.36/1.33  #Demod        : 17
% 2.36/1.33  #Tautology    : 48
% 2.36/1.33  #SimpNegUnit  : 4
% 2.36/1.33  #BackRed      : 1
% 2.36/1.33  
% 2.36/1.33  #Partial instantiations: 0
% 2.36/1.33  #Strategies tried      : 1
% 2.36/1.33  
% 2.36/1.33  Timing (in seconds)
% 2.36/1.33  ----------------------
% 2.36/1.33  Preprocessing        : 0.31
% 2.36/1.33  Parsing              : 0.17
% 2.36/1.33  CNF conversion       : 0.02
% 2.36/1.33  Main loop            : 0.19
% 2.36/1.33  Inferencing          : 0.08
% 2.36/1.33  Reduction            : 0.06
% 2.36/1.33  Demodulation         : 0.04
% 2.36/1.33  BG Simplification    : 0.01
% 2.36/1.33  Subsumption          : 0.03
% 2.36/1.33  Abstraction          : 0.01
% 2.36/1.33  MUC search           : 0.00
% 2.36/1.33  Cooper               : 0.00
% 2.36/1.33  Total                : 0.54
% 2.36/1.33  Index Insertion      : 0.00
% 2.36/1.33  Index Deletion       : 0.00
% 2.36/1.33  Index Matching       : 0.00
% 2.36/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
