%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:27 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 114 expanded)
%              Number of leaves         :   45 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  136 ( 259 expanded)
%              Number of equality atoms :   32 (  50 expanded)
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

tff(f_143,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_52,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_56,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_123,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_50,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_44,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_42,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_141,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k4_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_171,plain,(
    ! [B_54] : k3_xboole_0(k1_xboole_0,B_54) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_20])).

tff(c_189,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_171])).

tff(c_253,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_262,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = k4_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_253])).

tff(c_274,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_262])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(k1_tarski(A_18),B_19)
      | r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_3'(A_23),A_23)
      | k1_xboole_0 = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_227,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,k3_xboole_0(A_56,B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_420,plain,(
    ! [A_73,B_74] :
      ( ~ r1_xboole_0(A_73,B_74)
      | k3_xboole_0(A_73,B_74) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_227])).

tff(c_854,plain,(
    ! [A_108,B_109] :
      ( k3_xboole_0(k1_tarski(A_108),B_109) = k1_xboole_0
      | r2_hidden(A_108,B_109) ) ),
    inference(resolution,[status(thm)],[c_22,c_420])).

tff(c_271,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_253])).

tff(c_863,plain,(
    ! [B_109,A_108] :
      ( k4_xboole_0(B_109,k1_tarski(A_108)) = k5_xboole_0(B_109,k1_xboole_0)
      | r2_hidden(A_108,B_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_271])).

tff(c_1094,plain,(
    ! [B_115,A_116] :
      ( k4_xboole_0(B_115,k1_tarski(A_116)) = B_115
      | r2_hidden(A_116,B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_863])).

tff(c_411,plain,(
    ! [A_68,B_69,C_70] :
      ( k7_subset_1(A_68,B_69,C_70) = k4_xboole_0(B_69,C_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_414,plain,(
    ! [C_70] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',C_70) = k4_xboole_0('#skF_5',C_70) ),
    inference(resolution,[status(thm)],[c_40,c_411])).

tff(c_628,plain,(
    ! [A_94,B_95] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_94))),B_95,k1_tarski(k1_xboole_0)) = k2_yellow19(A_94,k3_yellow19(A_94,k2_struct_0(A_94),B_95))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_94)))))
      | ~ v13_waybel_0(B_95,k3_yellow_1(k2_struct_0(A_94)))
      | ~ v2_waybel_0(B_95,k3_yellow_1(k2_struct_0(A_94)))
      | v1_xboole_0(B_95)
      | ~ l1_struct_0(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_630,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_628])).

tff(c_633,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44,c_42,c_414,c_630])).

tff(c_634,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_48,c_633])).

tff(c_38,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_713,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_38])).

tff(c_1124,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1094,c_713])).

tff(c_36,plain,(
    ! [C_36,B_34,A_30] :
      ( ~ v1_xboole_0(C_36)
      | ~ r2_hidden(C_36,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30))))
      | ~ v13_waybel_0(B_34,k3_yellow_1(A_30))
      | ~ v2_waybel_0(B_34,k3_yellow_1(A_30))
      | ~ v1_subset_1(B_34,u1_struct_0(k3_yellow_1(A_30)))
      | v1_xboole_0(B_34)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1132,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_30))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_30))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_30)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_1124,c_36])).

tff(c_1138,plain,(
    ! [A_30] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_30))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_30))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_30)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1132])).

tff(c_1264,plain,(
    ! [A_123] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_123))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_123))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_123))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_123)))
      | v1_xboole_0(A_123) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1138])).

tff(c_1267,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_40,c_1264])).

tff(c_1270,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_1267])).

tff(c_30,plain,(
    ! [A_25] :
      ( ~ v1_xboole_0(k2_struct_0(A_25))
      | ~ l1_struct_0(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1273,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1270,c_30])).

tff(c_1279,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1273])).

tff(c_1281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:10:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.45  
% 3.00/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.45  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 3.00/1.45  
% 3.00/1.45  %Foreground sorts:
% 3.00/1.45  
% 3.00/1.45  
% 3.00/1.45  %Background operators:
% 3.00/1.45  
% 3.00/1.45  
% 3.00/1.45  %Foreground operators:
% 3.00/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.00/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.45  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.00/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.45  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.00/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.00/1.45  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.00/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.00/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.00/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.45  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.00/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.00/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.00/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.00/1.45  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.00/1.45  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.00/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.00/1.45  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.00/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.45  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.00/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.00/1.45  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.00/1.45  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.00/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.00/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.00/1.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.00/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.00/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.45  
% 3.14/1.47  tff(f_143, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.14/1.47  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.14/1.47  tff(f_52, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.14/1.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.14/1.47  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.14/1.47  tff(f_56, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.14/1.47  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.14/1.47  tff(f_61, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.14/1.47  tff(f_75, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.14/1.47  tff(f_48, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.14/1.47  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.14/1.47  tff(f_102, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 3.14/1.47  tff(f_123, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 3.14/1.47  tff(f_83, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.14/1.47  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.14/1.47  tff(c_50, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.14/1.47  tff(c_46, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.14/1.47  tff(c_44, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.14/1.47  tff(c_42, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.14/1.47  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.14/1.47  tff(c_48, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.14/1.47  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.14/1.47  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.14/1.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.14/1.47  tff(c_141, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k4_xboole_0(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.14/1.47  tff(c_20, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.14/1.47  tff(c_171, plain, (![B_54]: (k3_xboole_0(k1_xboole_0, B_54)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_141, c_20])).
% 3.14/1.47  tff(c_189, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_171])).
% 3.14/1.47  tff(c_253, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.14/1.47  tff(c_262, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=k4_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_189, c_253])).
% 3.14/1.47  tff(c_274, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_262])).
% 3.14/1.47  tff(c_22, plain, (![A_18, B_19]: (r1_xboole_0(k1_tarski(A_18), B_19) | r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.14/1.47  tff(c_28, plain, (![A_23]: (r2_hidden('#skF_3'(A_23), A_23) | k1_xboole_0=A_23)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.14/1.47  tff(c_227, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, k3_xboole_0(A_56, B_57)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.14/1.47  tff(c_420, plain, (![A_73, B_74]: (~r1_xboole_0(A_73, B_74) | k3_xboole_0(A_73, B_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_227])).
% 3.14/1.47  tff(c_854, plain, (![A_108, B_109]: (k3_xboole_0(k1_tarski(A_108), B_109)=k1_xboole_0 | r2_hidden(A_108, B_109))), inference(resolution, [status(thm)], [c_22, c_420])).
% 3.14/1.47  tff(c_271, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_253])).
% 3.14/1.47  tff(c_863, plain, (![B_109, A_108]: (k4_xboole_0(B_109, k1_tarski(A_108))=k5_xboole_0(B_109, k1_xboole_0) | r2_hidden(A_108, B_109))), inference(superposition, [status(thm), theory('equality')], [c_854, c_271])).
% 3.14/1.47  tff(c_1094, plain, (![B_115, A_116]: (k4_xboole_0(B_115, k1_tarski(A_116))=B_115 | r2_hidden(A_116, B_115))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_863])).
% 3.14/1.47  tff(c_411, plain, (![A_68, B_69, C_70]: (k7_subset_1(A_68, B_69, C_70)=k4_xboole_0(B_69, C_70) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.14/1.47  tff(c_414, plain, (![C_70]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', C_70)=k4_xboole_0('#skF_5', C_70))), inference(resolution, [status(thm)], [c_40, c_411])).
% 3.14/1.47  tff(c_628, plain, (![A_94, B_95]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_94))), B_95, k1_tarski(k1_xboole_0))=k2_yellow19(A_94, k3_yellow19(A_94, k2_struct_0(A_94), B_95)) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_94))))) | ~v13_waybel_0(B_95, k3_yellow_1(k2_struct_0(A_94))) | ~v2_waybel_0(B_95, k3_yellow_1(k2_struct_0(A_94))) | v1_xboole_0(B_95) | ~l1_struct_0(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.14/1.47  tff(c_630, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_628])).
% 3.14/1.47  tff(c_633, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44, c_42, c_414, c_630])).
% 3.14/1.47  tff(c_634, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_52, c_48, c_633])).
% 3.14/1.47  tff(c_38, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.14/1.47  tff(c_713, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_634, c_38])).
% 3.14/1.47  tff(c_1124, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1094, c_713])).
% 3.14/1.47  tff(c_36, plain, (![C_36, B_34, A_30]: (~v1_xboole_0(C_36) | ~r2_hidden(C_36, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30)))) | ~v13_waybel_0(B_34, k3_yellow_1(A_30)) | ~v2_waybel_0(B_34, k3_yellow_1(A_30)) | ~v1_subset_1(B_34, u1_struct_0(k3_yellow_1(A_30))) | v1_xboole_0(B_34) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.14/1.47  tff(c_1132, plain, (![A_30]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_30)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_30)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_30))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_30))), inference(resolution, [status(thm)], [c_1124, c_36])).
% 3.14/1.47  tff(c_1138, plain, (![A_30]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_30)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_30)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_30))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1132])).
% 3.14/1.47  tff(c_1264, plain, (![A_123]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_123)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_123)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_123)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_123))) | v1_xboole_0(A_123))), inference(negUnitSimplification, [status(thm)], [c_48, c_1138])).
% 3.14/1.47  tff(c_1267, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_1264])).
% 3.14/1.47  tff(c_1270, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_1267])).
% 3.14/1.47  tff(c_30, plain, (![A_25]: (~v1_xboole_0(k2_struct_0(A_25)) | ~l1_struct_0(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.47  tff(c_1273, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1270, c_30])).
% 3.14/1.47  tff(c_1279, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1273])).
% 3.14/1.47  tff(c_1281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1279])).
% 3.14/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.47  
% 3.14/1.47  Inference rules
% 3.14/1.47  ----------------------
% 3.14/1.47  #Ref     : 0
% 3.14/1.47  #Sup     : 287
% 3.14/1.47  #Fact    : 0
% 3.14/1.47  #Define  : 0
% 3.14/1.47  #Split   : 1
% 3.14/1.47  #Chain   : 0
% 3.14/1.47  #Close   : 0
% 3.14/1.47  
% 3.14/1.47  Ordering : KBO
% 3.14/1.47  
% 3.14/1.47  Simplification rules
% 3.14/1.47  ----------------------
% 3.14/1.47  #Subsume      : 81
% 3.14/1.47  #Demod        : 109
% 3.14/1.47  #Tautology    : 142
% 3.14/1.47  #SimpNegUnit  : 19
% 3.14/1.47  #BackRed      : 1
% 3.14/1.47  
% 3.14/1.47  #Partial instantiations: 0
% 3.14/1.47  #Strategies tried      : 1
% 3.14/1.47  
% 3.14/1.47  Timing (in seconds)
% 3.14/1.47  ----------------------
% 3.14/1.47  Preprocessing        : 0.33
% 3.14/1.47  Parsing              : 0.18
% 3.14/1.47  CNF conversion       : 0.02
% 3.14/1.47  Main loop            : 0.38
% 3.14/1.47  Inferencing          : 0.15
% 3.14/1.47  Reduction            : 0.13
% 3.14/1.47  Demodulation         : 0.09
% 3.14/1.47  BG Simplification    : 0.02
% 3.14/1.47  Subsumption          : 0.06
% 3.14/1.47  Abstraction          : 0.02
% 3.14/1.47  MUC search           : 0.00
% 3.14/1.47  Cooper               : 0.00
% 3.14/1.47  Total                : 0.75
% 3.14/1.47  Index Insertion      : 0.00
% 3.14/1.47  Index Deletion       : 0.00
% 3.14/1.47  Index Matching       : 0.00
% 3.14/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
