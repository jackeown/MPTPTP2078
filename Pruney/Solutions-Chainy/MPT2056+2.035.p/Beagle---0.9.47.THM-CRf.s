%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:30 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 104 expanded)
%              Number of leaves         :   42 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  129 ( 257 expanded)
%              Number of equality atoms :   20 (  35 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_95,axiom,(
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

tff(f_116,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_48,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_87,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_91,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_87])).

tff(c_96,plain,(
    ! [A_47] :
      ( ~ v1_xboole_0(u1_struct_0(A_47))
      | ~ l1_struct_0(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_99,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_96])).

tff(c_101,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_99])).

tff(c_102,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_101])).

tff(c_44,plain,(
    v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_42,plain,(
    v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_40,plain,(
    v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_67,plain,(
    ! [A_39,B_40] : r1_xboole_0(k4_xboole_0(A_39,B_40),B_40) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_67])).

tff(c_12,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_138,plain,(
    ! [A_55,B_56,C_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | ~ r2_hidden(C_57,k3_xboole_0(A_55,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_145,plain,(
    ! [A_12,C_57] :
      ( ~ r1_xboole_0(A_12,k1_xboole_0)
      | ~ r2_hidden(C_57,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_138])).

tff(c_149,plain,(
    ! [C_58] : ~ r2_hidden(C_58,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_145])).

tff(c_154,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_149])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,k1_tarski(B_19)) = A_18
      | r2_hidden(B_19,A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_309,plain,(
    ! [A_72,B_73,C_74] :
      ( k7_subset_1(A_72,B_73,C_74) = k4_xboole_0(B_73,C_74)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_312,plain,(
    ! [C_74] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',C_74) = k4_xboole_0('#skF_4',C_74) ),
    inference(resolution,[status(thm)],[c_38,c_309])).

tff(c_436,plain,(
    ! [A_92,B_93] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_92))),B_93,k1_tarski(k1_xboole_0)) = k2_yellow19(A_92,k3_yellow19(A_92,k2_struct_0(A_92),B_93))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_92)))))
      | ~ v13_waybel_0(B_93,k3_yellow_1(k2_struct_0(A_92)))
      | ~ v2_waybel_0(B_93,k3_yellow_1(k2_struct_0(A_92)))
      | v1_xboole_0(B_93)
      | ~ l1_struct_0(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_438,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_436])).

tff(c_441,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_40,c_312,c_438])).

tff(c_442,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_46,c_441])).

tff(c_36,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_680,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_442,c_36])).

tff(c_688,plain,(
    r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_680])).

tff(c_34,plain,(
    ! [C_35,B_33,A_29] :
      ( ~ v1_xboole_0(C_35)
      | ~ r2_hidden(C_35,B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_29))))
      | ~ v13_waybel_0(B_33,k3_yellow_1(A_29))
      | ~ v2_waybel_0(B_33,k3_yellow_1(A_29))
      | ~ v1_subset_1(B_33,u1_struct_0(k3_yellow_1(A_29)))
      | v1_xboole_0(B_33)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_690,plain,(
    ! [A_29] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_29))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_29))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_29))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_29)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_29) ) ),
    inference(resolution,[status(thm)],[c_688,c_34])).

tff(c_696,plain,(
    ! [A_29] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_29))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_29))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_29))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_29)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_690])).

tff(c_838,plain,(
    ! [A_122] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_122))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_122))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_122))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_122)))
      | v1_xboole_0(A_122) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_696])).

tff(c_841,plain,
    ( ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_838])).

tff(c_844,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_841])).

tff(c_846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_844])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.44  
% 2.82/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.45  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.82/1.45  
% 2.82/1.45  %Foreground sorts:
% 2.82/1.45  
% 2.82/1.45  
% 2.82/1.45  %Background operators:
% 2.82/1.45  
% 2.82/1.45  
% 2.82/1.45  %Foreground operators:
% 2.82/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.82/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.45  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 2.82/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.45  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.82/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.82/1.45  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.82/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.82/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.82/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.45  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 2.82/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.82/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.82/1.45  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.82/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.45  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 2.82/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.82/1.45  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 2.82/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.82/1.45  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 2.82/1.45  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 2.82/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.82/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.82/1.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.82/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.45  
% 2.82/1.46  tff(f_136, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 2.82/1.46  tff(f_68, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.82/1.46  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.82/1.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.82/1.46  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.82/1.46  tff(f_55, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.82/1.46  tff(f_49, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.82/1.46  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.82/1.46  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.82/1.46  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.82/1.46  tff(f_95, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 2.82/1.46  tff(f_116, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 2.82/1.46  tff(c_50, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.82/1.46  tff(c_48, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.82/1.46  tff(c_87, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.82/1.46  tff(c_91, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_87])).
% 2.82/1.46  tff(c_96, plain, (![A_47]: (~v1_xboole_0(u1_struct_0(A_47)) | ~l1_struct_0(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.82/1.46  tff(c_99, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_91, c_96])).
% 2.82/1.46  tff(c_101, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_99])).
% 2.82/1.46  tff(c_102, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_101])).
% 2.82/1.46  tff(c_44, plain, (v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.82/1.46  tff(c_42, plain, (v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.82/1.46  tff(c_40, plain, (v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.82/1.46  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.82/1.46  tff(c_46, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.82/1.46  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.46  tff(c_14, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.82/1.46  tff(c_67, plain, (![A_39, B_40]: (r1_xboole_0(k4_xboole_0(A_39, B_40), B_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.82/1.46  tff(c_70, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_67])).
% 2.82/1.46  tff(c_12, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.82/1.46  tff(c_138, plain, (![A_55, B_56, C_57]: (~r1_xboole_0(A_55, B_56) | ~r2_hidden(C_57, k3_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.82/1.46  tff(c_145, plain, (![A_12, C_57]: (~r1_xboole_0(A_12, k1_xboole_0) | ~r2_hidden(C_57, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_138])).
% 2.82/1.46  tff(c_149, plain, (![C_58]: (~r2_hidden(C_58, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_145])).
% 2.82/1.46  tff(c_154, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_149])).
% 2.82/1.46  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k1_tarski(B_19))=A_18 | r2_hidden(B_19, A_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.82/1.46  tff(c_309, plain, (![A_72, B_73, C_74]: (k7_subset_1(A_72, B_73, C_74)=k4_xboole_0(B_73, C_74) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.82/1.46  tff(c_312, plain, (![C_74]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', C_74)=k4_xboole_0('#skF_4', C_74))), inference(resolution, [status(thm)], [c_38, c_309])).
% 2.82/1.46  tff(c_436, plain, (![A_92, B_93]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_92))), B_93, k1_tarski(k1_xboole_0))=k2_yellow19(A_92, k3_yellow19(A_92, k2_struct_0(A_92), B_93)) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_92))))) | ~v13_waybel_0(B_93, k3_yellow_1(k2_struct_0(A_92))) | ~v2_waybel_0(B_93, k3_yellow_1(k2_struct_0(A_92))) | v1_xboole_0(B_93) | ~l1_struct_0(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.82/1.46  tff(c_438, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_436])).
% 2.82/1.46  tff(c_441, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_40, c_312, c_438])).
% 2.82/1.46  tff(c_442, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_50, c_46, c_441])).
% 2.82/1.46  tff(c_36, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.82/1.46  tff(c_680, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_442, c_36])).
% 2.82/1.46  tff(c_688, plain, (r2_hidden(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22, c_680])).
% 2.82/1.46  tff(c_34, plain, (![C_35, B_33, A_29]: (~v1_xboole_0(C_35) | ~r2_hidden(C_35, B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_29)))) | ~v13_waybel_0(B_33, k3_yellow_1(A_29)) | ~v2_waybel_0(B_33, k3_yellow_1(A_29)) | ~v1_subset_1(B_33, u1_struct_0(k3_yellow_1(A_29))) | v1_xboole_0(B_33) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.82/1.46  tff(c_690, plain, (![A_29]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_29)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_29)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_29)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_29))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_29))), inference(resolution, [status(thm)], [c_688, c_34])).
% 2.82/1.46  tff(c_696, plain, (![A_29]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_29)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_29)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_29)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_29))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_29))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_690])).
% 2.82/1.46  tff(c_838, plain, (![A_122]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_122)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_122)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_122)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_122))) | v1_xboole_0(A_122))), inference(negUnitSimplification, [status(thm)], [c_46, c_696])).
% 2.82/1.46  tff(c_841, plain, (~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_38, c_838])).
% 2.82/1.46  tff(c_844, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_841])).
% 2.82/1.46  tff(c_846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_844])).
% 2.82/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.46  
% 2.82/1.46  Inference rules
% 2.82/1.46  ----------------------
% 2.82/1.46  #Ref     : 0
% 2.82/1.46  #Sup     : 188
% 2.82/1.46  #Fact    : 0
% 2.82/1.46  #Define  : 0
% 2.82/1.46  #Split   : 0
% 2.82/1.46  #Chain   : 0
% 2.82/1.46  #Close   : 0
% 2.82/1.46  
% 2.82/1.46  Ordering : KBO
% 2.82/1.46  
% 2.82/1.46  Simplification rules
% 2.82/1.46  ----------------------
% 2.82/1.46  #Subsume      : 32
% 2.82/1.46  #Demod        : 118
% 2.82/1.46  #Tautology    : 96
% 2.82/1.46  #SimpNegUnit  : 8
% 2.82/1.46  #BackRed      : 1
% 2.82/1.46  
% 2.82/1.46  #Partial instantiations: 0
% 2.82/1.46  #Strategies tried      : 1
% 2.82/1.46  
% 2.82/1.46  Timing (in seconds)
% 2.82/1.46  ----------------------
% 3.10/1.46  Preprocessing        : 0.34
% 3.10/1.47  Parsing              : 0.18
% 3.10/1.47  CNF conversion       : 0.02
% 3.10/1.47  Main loop            : 0.35
% 3.10/1.47  Inferencing          : 0.14
% 3.10/1.47  Reduction            : 0.12
% 3.10/1.47  Demodulation         : 0.09
% 3.10/1.47  BG Simplification    : 0.02
% 3.10/1.47  Subsumption          : 0.05
% 3.10/1.47  Abstraction          : 0.02
% 3.10/1.47  MUC search           : 0.00
% 3.10/1.47  Cooper               : 0.00
% 3.10/1.47  Total                : 0.72
% 3.10/1.47  Index Insertion      : 0.00
% 3.10/1.47  Index Deletion       : 0.00
% 3.10/1.47  Index Matching       : 0.00
% 3.10/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
