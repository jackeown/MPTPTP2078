%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:29 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 118 expanded)
%              Number of leaves         :   50 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  145 ( 273 expanded)
%              Number of equality atoms :   30 (  45 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_153,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_54,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_56,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_58,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_112,axiom,(
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

tff(f_133,axiom,(
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

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_56,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_101,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_105,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_101])).

tff(c_137,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(u1_struct_0(A_60))
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_140,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_137])).

tff(c_142,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_140])).

tff(c_143,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_142])).

tff(c_52,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_50,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_48,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_16,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_234,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k4_xboole_0(B_77,A_76)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_243,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = k2_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_234])).

tff(c_246,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_243])).

tff(c_144,plain,(
    ! [A_61,B_62] :
      ( r1_xboole_0(k1_tarski(A_61),B_62)
      | r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r1_xboole_0(B_6,A_5)
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_147,plain,(
    ! [B_62,A_61] :
      ( r1_xboole_0(B_62,k1_tarski(A_61))
      | r2_hidden(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_144,c_8])).

tff(c_32,plain,(
    ! [A_27] :
      ( r2_hidden('#skF_3'(A_27),A_27)
      | k1_xboole_0 = A_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_148,plain,(
    ! [A_63,B_64,C_65] :
      ( ~ r1_xboole_0(A_63,B_64)
      | ~ r2_hidden(C_65,k3_xboole_0(A_63,B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_168,plain,(
    ! [A_70,B_71] :
      ( ~ r1_xboole_0(A_70,B_71)
      | k3_xboole_0(A_70,B_71) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_148])).

tff(c_328,plain,(
    ! [B_88,A_89] :
      ( k3_xboole_0(B_88,k1_tarski(A_89)) = k1_xboole_0
      | r2_hidden(A_89,B_88) ) ),
    inference(resolution,[status(thm)],[c_147,c_168])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_344,plain,(
    ! [B_88,A_89] :
      ( k4_xboole_0(B_88,k1_tarski(A_89)) = k5_xboole_0(B_88,k1_xboole_0)
      | r2_hidden(A_89,B_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_14])).

tff(c_370,plain,(
    ! [B_88,A_89] :
      ( k4_xboole_0(B_88,k1_tarski(A_89)) = B_88
      | r2_hidden(A_89,B_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_344])).

tff(c_324,plain,(
    ! [A_85,B_86,C_87] :
      ( k7_subset_1(A_85,B_86,C_87) = k4_xboole_0(B_86,C_87)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_327,plain,(
    ! [C_87] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',C_87) = k4_xboole_0('#skF_5',C_87) ),
    inference(resolution,[status(thm)],[c_46,c_324])).

tff(c_487,plain,(
    ! [A_100,B_101] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_100))),B_101,k1_tarski(k1_xboole_0)) = k2_yellow19(A_100,k3_yellow19(A_100,k2_struct_0(A_100),B_101))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_100)))))
      | ~ v13_waybel_0(B_101,k3_yellow_1(k2_struct_0(A_100)))
      | ~ v2_waybel_0(B_101,k3_yellow_1(k2_struct_0(A_100)))
      | v1_xboole_0(B_101)
      | ~ l1_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_489,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_487])).

tff(c_492,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50,c_48,c_327,c_489])).

tff(c_493,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_54,c_492])).

tff(c_44,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_547,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_44])).

tff(c_555,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_547])).

tff(c_42,plain,(
    ! [C_41,B_39,A_35] :
      ( ~ v1_xboole_0(C_41)
      | ~ r2_hidden(C_41,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35))))
      | ~ v13_waybel_0(B_39,k3_yellow_1(A_35))
      | ~ v2_waybel_0(B_39,k3_yellow_1(A_35))
      | ~ v1_subset_1(B_39,u1_struct_0(k3_yellow_1(A_35)))
      | v1_xboole_0(B_39)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_557,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_35))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_35))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_35)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_555,c_42])).

tff(c_563,plain,(
    ! [A_35] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_35))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_35))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_35)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_557])).

tff(c_613,plain,(
    ! [A_107] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_107))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_107))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_107))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_107)))
      | v1_xboole_0(A_107) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_563])).

tff(c_616,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_46,c_613])).

tff(c_619,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_616])).

tff(c_621,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_143,c_619])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:03:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.92  
% 3.20/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.93  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 3.53/1.93  
% 3.53/1.93  %Foreground sorts:
% 3.53/1.93  
% 3.53/1.93  
% 3.53/1.93  %Background operators:
% 3.53/1.93  
% 3.53/1.93  
% 3.53/1.93  %Foreground operators:
% 3.53/1.93  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.53/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.93  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.53/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.93  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.53/1.93  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.53/1.93  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.53/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.53/1.93  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.53/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.93  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.53/1.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.53/1.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.53/1.93  tff('#skF_5', type, '#skF_5': $i).
% 3.53/1.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.53/1.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.53/1.93  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.53/1.93  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.53/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.93  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.53/1.93  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.53/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.93  tff('#skF_4', type, '#skF_4': $i).
% 3.53/1.93  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.53/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.53/1.93  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.53/1.93  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.53/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.53/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.53/1.93  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.53/1.93  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.53/1.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.53/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.93  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.53/1.93  
% 3.53/1.95  tff(f_153, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 3.53/1.95  tff(f_85, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.53/1.95  tff(f_93, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.53/1.95  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.53/1.95  tff(f_54, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.53/1.95  tff(f_56, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.53/1.95  tff(f_58, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.53/1.95  tff(f_65, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.53/1.95  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.53/1.95  tff(f_81, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.53/1.95  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.53/1.95  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.53/1.95  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.53/1.95  tff(f_112, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 3.53/1.95  tff(f_133, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 3.53/1.95  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.53/1.95  tff(c_56, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.53/1.95  tff(c_101, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.53/1.95  tff(c_105, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_101])).
% 3.53/1.95  tff(c_137, plain, (![A_60]: (~v1_xboole_0(u1_struct_0(A_60)) | ~l1_struct_0(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.53/1.95  tff(c_140, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_105, c_137])).
% 3.53/1.95  tff(c_142, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_140])).
% 3.53/1.95  tff(c_143, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_142])).
% 3.53/1.95  tff(c_52, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.53/1.95  tff(c_50, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.53/1.95  tff(c_48, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.53/1.95  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.53/1.95  tff(c_54, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.53/1.95  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.53/1.95  tff(c_16, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.53/1.95  tff(c_18, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.53/1.95  tff(c_234, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k4_xboole_0(B_77, A_76))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.53/1.95  tff(c_243, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=k2_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_234])).
% 3.53/1.95  tff(c_246, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_243])).
% 3.53/1.95  tff(c_144, plain, (![A_61, B_62]: (r1_xboole_0(k1_tarski(A_61), B_62) | r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.53/1.95  tff(c_8, plain, (![B_6, A_5]: (r1_xboole_0(B_6, A_5) | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.53/1.95  tff(c_147, plain, (![B_62, A_61]: (r1_xboole_0(B_62, k1_tarski(A_61)) | r2_hidden(A_61, B_62))), inference(resolution, [status(thm)], [c_144, c_8])).
% 3.53/1.95  tff(c_32, plain, (![A_27]: (r2_hidden('#skF_3'(A_27), A_27) | k1_xboole_0=A_27)), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.53/1.95  tff(c_148, plain, (![A_63, B_64, C_65]: (~r1_xboole_0(A_63, B_64) | ~r2_hidden(C_65, k3_xboole_0(A_63, B_64)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.53/1.95  tff(c_168, plain, (![A_70, B_71]: (~r1_xboole_0(A_70, B_71) | k3_xboole_0(A_70, B_71)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_148])).
% 3.53/1.95  tff(c_328, plain, (![B_88, A_89]: (k3_xboole_0(B_88, k1_tarski(A_89))=k1_xboole_0 | r2_hidden(A_89, B_88))), inference(resolution, [status(thm)], [c_147, c_168])).
% 3.53/1.95  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.53/1.95  tff(c_344, plain, (![B_88, A_89]: (k4_xboole_0(B_88, k1_tarski(A_89))=k5_xboole_0(B_88, k1_xboole_0) | r2_hidden(A_89, B_88))), inference(superposition, [status(thm), theory('equality')], [c_328, c_14])).
% 3.53/1.95  tff(c_370, plain, (![B_88, A_89]: (k4_xboole_0(B_88, k1_tarski(A_89))=B_88 | r2_hidden(A_89, B_88))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_344])).
% 3.53/1.95  tff(c_324, plain, (![A_85, B_86, C_87]: (k7_subset_1(A_85, B_86, C_87)=k4_xboole_0(B_86, C_87) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.53/1.95  tff(c_327, plain, (![C_87]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', C_87)=k4_xboole_0('#skF_5', C_87))), inference(resolution, [status(thm)], [c_46, c_324])).
% 3.53/1.95  tff(c_487, plain, (![A_100, B_101]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_100))), B_101, k1_tarski(k1_xboole_0))=k2_yellow19(A_100, k3_yellow19(A_100, k2_struct_0(A_100), B_101)) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_100))))) | ~v13_waybel_0(B_101, k3_yellow_1(k2_struct_0(A_100))) | ~v2_waybel_0(B_101, k3_yellow_1(k2_struct_0(A_100))) | v1_xboole_0(B_101) | ~l1_struct_0(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.53/1.95  tff(c_489, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_487])).
% 3.53/1.95  tff(c_492, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50, c_48, c_327, c_489])).
% 3.53/1.95  tff(c_493, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_58, c_54, c_492])).
% 3.53/1.95  tff(c_44, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.53/1.95  tff(c_547, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_493, c_44])).
% 3.53/1.95  tff(c_555, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_370, c_547])).
% 3.53/1.95  tff(c_42, plain, (![C_41, B_39, A_35]: (~v1_xboole_0(C_41) | ~r2_hidden(C_41, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35)))) | ~v13_waybel_0(B_39, k3_yellow_1(A_35)) | ~v2_waybel_0(B_39, k3_yellow_1(A_35)) | ~v1_subset_1(B_39, u1_struct_0(k3_yellow_1(A_35))) | v1_xboole_0(B_39) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.53/1.95  tff(c_557, plain, (![A_35]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_35)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_35)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_35))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_555, c_42])).
% 3.53/1.95  tff(c_563, plain, (![A_35]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_35)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_35)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_35))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_557])).
% 3.53/1.95  tff(c_613, plain, (![A_107]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_107)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_107)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_107)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_107))) | v1_xboole_0(A_107))), inference(negUnitSimplification, [status(thm)], [c_54, c_563])).
% 3.53/1.95  tff(c_616, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_613])).
% 3.53/1.95  tff(c_619, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_616])).
% 3.53/1.95  tff(c_621, plain, $false, inference(negUnitSimplification, [status(thm)], [c_143, c_619])).
% 3.53/1.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.95  
% 3.53/1.95  Inference rules
% 3.53/1.95  ----------------------
% 3.53/1.95  #Ref     : 0
% 3.53/1.95  #Sup     : 125
% 3.53/1.95  #Fact    : 0
% 3.53/1.95  #Define  : 0
% 3.53/1.95  #Split   : 1
% 3.53/1.95  #Chain   : 0
% 3.53/1.95  #Close   : 0
% 3.53/1.95  
% 3.53/1.95  Ordering : KBO
% 3.53/1.95  
% 3.53/1.95  Simplification rules
% 3.53/1.95  ----------------------
% 3.53/1.95  #Subsume      : 15
% 3.53/1.95  #Demod        : 28
% 3.53/1.95  #Tautology    : 76
% 3.53/1.95  #SimpNegUnit  : 6
% 3.53/1.95  #BackRed      : 1
% 3.53/1.95  
% 3.53/1.95  #Partial instantiations: 0
% 3.53/1.95  #Strategies tried      : 1
% 3.53/1.95  
% 3.53/1.95  Timing (in seconds)
% 3.53/1.95  ----------------------
% 3.53/1.96  Preprocessing        : 0.58
% 3.53/1.96  Parsing              : 0.32
% 3.53/1.96  CNF conversion       : 0.04
% 3.53/1.96  Main loop            : 0.45
% 3.53/1.96  Inferencing          : 0.18
% 3.53/1.96  Reduction            : 0.13
% 3.53/1.96  Demodulation         : 0.09
% 3.53/1.96  BG Simplification    : 0.03
% 3.53/1.96  Subsumption          : 0.08
% 3.53/1.96  Abstraction          : 0.03
% 3.53/1.96  MUC search           : 0.00
% 3.53/1.96  Cooper               : 0.00
% 3.53/1.96  Total                : 1.09
% 3.53/1.96  Index Insertion      : 0.00
% 3.53/1.96  Index Deletion       : 0.00
% 3.53/1.96  Index Matching       : 0.00
% 3.53/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
