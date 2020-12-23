%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:25 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 133 expanded)
%              Number of leaves         :   50 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  167 ( 300 expanded)
%              Number of equality atoms :   38 (  56 expanded)
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

tff(f_152,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_41,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_67,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_111,axiom,(
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

tff(f_132,axiom,(
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

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_62,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_142,plain,(
    ! [A_55] :
      ( u1_struct_0(A_55) = k2_struct_0(A_55)
      | ~ l1_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_146,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_142])).

tff(c_152,plain,(
    ! [A_58] :
      ( ~ v1_xboole_0(u1_struct_0(A_58))
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_155,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_152])).

tff(c_157,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_155])).

tff(c_158,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_157])).

tff(c_58,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_56,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_54,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_14,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [A_22] : k4_xboole_0(A_22,k1_xboole_0) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_182,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k4_xboole_0(A_62,B_63)) = k3_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    ! [A_25] : k4_xboole_0(k1_xboole_0,A_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_224,plain,(
    ! [B_67] : k3_xboole_0(k1_xboole_0,B_67) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_34])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_269,plain,(
    ! [B_70] : k3_xboole_0(B_70,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_2])).

tff(c_26,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_274,plain,(
    ! [B_70] : k5_xboole_0(B_70,k1_xboole_0) = k4_xboole_0(B_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_26])).

tff(c_301,plain,(
    ! [B_70] : k5_xboole_0(B_70,k1_xboole_0) = B_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_274])).

tff(c_36,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(k1_tarski(A_26),B_27)
      | r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_212,plain,(
    ! [A_64,B_65,C_66] :
      ( ~ r1_xboole_0(A_64,B_65)
      | ~ r2_hidden(C_66,k3_xboole_0(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_467,plain,(
    ! [A_88,B_89] :
      ( ~ r1_xboole_0(A_88,B_89)
      | v1_xboole_0(k3_xboole_0(A_88,B_89)) ) ),
    inference(resolution,[status(thm)],[c_6,c_212])).

tff(c_393,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_2'(A_76,B_77),A_76)
      | r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_426,plain,(
    ! [A_79,B_80] :
      ( ~ v1_xboole_0(A_79)
      | r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_393,c_4])).

tff(c_28,plain,(
    ! [A_21] : r1_tarski(k1_xboole_0,A_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_159,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_168,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_28,c_159])).

tff(c_433,plain,(
    ! [A_79] :
      ( k1_xboole_0 = A_79
      | ~ v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_426,c_168])).

tff(c_716,plain,(
    ! [A_117,B_118] :
      ( k3_xboole_0(A_117,B_118) = k1_xboole_0
      | ~ r1_xboole_0(A_117,B_118) ) ),
    inference(resolution,[status(thm)],[c_467,c_433])).

tff(c_940,plain,(
    ! [A_137,B_138] :
      ( k3_xboole_0(k1_tarski(A_137),B_138) = k1_xboole_0
      | r2_hidden(A_137,B_138) ) ),
    inference(resolution,[status(thm)],[c_36,c_716])).

tff(c_250,plain,(
    ! [A_68,B_69] : k5_xboole_0(A_68,k3_xboole_0(A_68,B_69)) = k4_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_265,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_250])).

tff(c_955,plain,(
    ! [B_138,A_137] :
      ( k4_xboole_0(B_138,k1_tarski(A_137)) = k5_xboole_0(B_138,k1_xboole_0)
      | r2_hidden(A_137,B_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_940,c_265])).

tff(c_1261,plain,(
    ! [B_150,A_151] :
      ( k4_xboole_0(B_150,k1_tarski(A_151)) = B_150
      | r2_hidden(A_151,B_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_955])).

tff(c_578,plain,(
    ! [A_98,B_99,C_100] :
      ( k7_subset_1(A_98,B_99,C_100) = k4_xboole_0(B_99,C_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_581,plain,(
    ! [C_100] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',C_100) = k4_xboole_0('#skF_5',C_100) ),
    inference(resolution,[status(thm)],[c_52,c_578])).

tff(c_768,plain,(
    ! [A_122,B_123] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_122))),B_123,k1_tarski(k1_xboole_0)) = k2_yellow19(A_122,k3_yellow19(A_122,k2_struct_0(A_122),B_123))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_122)))))
      | ~ v13_waybel_0(B_123,k3_yellow_1(k2_struct_0(A_122)))
      | ~ v2_waybel_0(B_123,k3_yellow_1(k2_struct_0(A_122)))
      | v1_xboole_0(B_123)
      | ~ l1_struct_0(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_770,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_768])).

tff(c_773,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_54,c_581,c_770])).

tff(c_774,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_60,c_773])).

tff(c_50,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_935,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_50])).

tff(c_1291,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1261,c_935])).

tff(c_48,plain,(
    ! [C_43,B_41,A_37] :
      ( ~ v1_xboole_0(C_43)
      | ~ r2_hidden(C_43,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_37))))
      | ~ v13_waybel_0(B_41,k3_yellow_1(A_37))
      | ~ v2_waybel_0(B_41,k3_yellow_1(A_37))
      | ~ v1_subset_1(B_41,u1_struct_0(k3_yellow_1(A_37)))
      | v1_xboole_0(B_41)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1299,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_37))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_37))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_37))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_37)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_1291,c_48])).

tff(c_1307,plain,(
    ! [A_37] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_37))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_37))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_37))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_37)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1299])).

tff(c_1404,plain,(
    ! [A_156] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_156))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_156))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_156))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_156)))
      | v1_xboole_0(A_156) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1307])).

tff(c_1407,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_1404])).

tff(c_1410,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1407])).

tff(c_1412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_158,c_1410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:55:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.61  
% 3.00/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.61  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 3.00/1.61  
% 3.00/1.61  %Foreground sorts:
% 3.00/1.61  
% 3.00/1.61  
% 3.00/1.61  %Background operators:
% 3.00/1.61  
% 3.00/1.61  
% 3.00/1.61  %Foreground operators:
% 3.00/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.00/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.61  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.00/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.61  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.00/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.00/1.61  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.00/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.00/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.00/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.61  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.00/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.00/1.61  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.00/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.00/1.61  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.00/1.61  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.00/1.61  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.00/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.00/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.00/1.61  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.00/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.00/1.61  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.00/1.61  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.00/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.00/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.00/1.61  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.00/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.00/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.00/1.61  
% 3.00/1.63  tff(f_152, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.00/1.63  tff(f_84, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.00/1.63  tff(f_92, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.00/1.63  tff(f_41, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.00/1.63  tff(f_67, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.00/1.63  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.00/1.63  tff(f_71, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.00/1.63  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.00/1.63  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.00/1.63  tff(f_76, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.00/1.63  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.00/1.63  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.00/1.63  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.00/1.63  tff(f_65, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.00/1.63  tff(f_61, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.00/1.63  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.00/1.63  tff(f_111, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 3.00/1.63  tff(f_132, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 3.00/1.63  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.00/1.63  tff(c_62, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.00/1.63  tff(c_142, plain, (![A_55]: (u1_struct_0(A_55)=k2_struct_0(A_55) | ~l1_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.00/1.63  tff(c_146, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_142])).
% 3.00/1.63  tff(c_152, plain, (![A_58]: (~v1_xboole_0(u1_struct_0(A_58)) | ~l1_struct_0(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.00/1.63  tff(c_155, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_146, c_152])).
% 3.00/1.63  tff(c_157, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_155])).
% 3.00/1.63  tff(c_158, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_157])).
% 3.00/1.63  tff(c_58, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.00/1.63  tff(c_56, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.00/1.63  tff(c_54, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.00/1.63  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.00/1.63  tff(c_60, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.00/1.63  tff(c_14, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.00/1.63  tff(c_30, plain, (![A_22]: (k4_xboole_0(A_22, k1_xboole_0)=A_22)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.00/1.63  tff(c_182, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k4_xboole_0(A_62, B_63))=k3_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.00/1.63  tff(c_34, plain, (![A_25]: (k4_xboole_0(k1_xboole_0, A_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.00/1.63  tff(c_224, plain, (![B_67]: (k3_xboole_0(k1_xboole_0, B_67)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_182, c_34])).
% 3.00/1.63  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.00/1.63  tff(c_269, plain, (![B_70]: (k3_xboole_0(B_70, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_224, c_2])).
% 3.00/1.63  tff(c_26, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.00/1.63  tff(c_274, plain, (![B_70]: (k5_xboole_0(B_70, k1_xboole_0)=k4_xboole_0(B_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_269, c_26])).
% 3.00/1.63  tff(c_301, plain, (![B_70]: (k5_xboole_0(B_70, k1_xboole_0)=B_70)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_274])).
% 3.00/1.63  tff(c_36, plain, (![A_26, B_27]: (r1_xboole_0(k1_tarski(A_26), B_27) | r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.00/1.63  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.00/1.63  tff(c_212, plain, (![A_64, B_65, C_66]: (~r1_xboole_0(A_64, B_65) | ~r2_hidden(C_66, k3_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.00/1.63  tff(c_467, plain, (![A_88, B_89]: (~r1_xboole_0(A_88, B_89) | v1_xboole_0(k3_xboole_0(A_88, B_89)))), inference(resolution, [status(thm)], [c_6, c_212])).
% 3.00/1.63  tff(c_393, plain, (![A_76, B_77]: (r2_hidden('#skF_2'(A_76, B_77), A_76) | r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.00/1.63  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.00/1.63  tff(c_426, plain, (![A_79, B_80]: (~v1_xboole_0(A_79) | r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_393, c_4])).
% 3.00/1.63  tff(c_28, plain, (![A_21]: (r1_tarski(k1_xboole_0, A_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.00/1.63  tff(c_159, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.00/1.63  tff(c_168, plain, (![A_21]: (k1_xboole_0=A_21 | ~r1_tarski(A_21, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_159])).
% 3.00/1.63  tff(c_433, plain, (![A_79]: (k1_xboole_0=A_79 | ~v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_426, c_168])).
% 3.00/1.63  tff(c_716, plain, (![A_117, B_118]: (k3_xboole_0(A_117, B_118)=k1_xboole_0 | ~r1_xboole_0(A_117, B_118))), inference(resolution, [status(thm)], [c_467, c_433])).
% 3.00/1.63  tff(c_940, plain, (![A_137, B_138]: (k3_xboole_0(k1_tarski(A_137), B_138)=k1_xboole_0 | r2_hidden(A_137, B_138))), inference(resolution, [status(thm)], [c_36, c_716])).
% 3.00/1.63  tff(c_250, plain, (![A_68, B_69]: (k5_xboole_0(A_68, k3_xboole_0(A_68, B_69))=k4_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.00/1.63  tff(c_265, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_250])).
% 3.00/1.63  tff(c_955, plain, (![B_138, A_137]: (k4_xboole_0(B_138, k1_tarski(A_137))=k5_xboole_0(B_138, k1_xboole_0) | r2_hidden(A_137, B_138))), inference(superposition, [status(thm), theory('equality')], [c_940, c_265])).
% 3.00/1.63  tff(c_1261, plain, (![B_150, A_151]: (k4_xboole_0(B_150, k1_tarski(A_151))=B_150 | r2_hidden(A_151, B_150))), inference(demodulation, [status(thm), theory('equality')], [c_301, c_955])).
% 3.00/1.63  tff(c_578, plain, (![A_98, B_99, C_100]: (k7_subset_1(A_98, B_99, C_100)=k4_xboole_0(B_99, C_100) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.00/1.63  tff(c_581, plain, (![C_100]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', C_100)=k4_xboole_0('#skF_5', C_100))), inference(resolution, [status(thm)], [c_52, c_578])).
% 3.00/1.63  tff(c_768, plain, (![A_122, B_123]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_122))), B_123, k1_tarski(k1_xboole_0))=k2_yellow19(A_122, k3_yellow19(A_122, k2_struct_0(A_122), B_123)) | ~m1_subset_1(B_123, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_122))))) | ~v13_waybel_0(B_123, k3_yellow_1(k2_struct_0(A_122))) | ~v2_waybel_0(B_123, k3_yellow_1(k2_struct_0(A_122))) | v1_xboole_0(B_123) | ~l1_struct_0(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.00/1.63  tff(c_770, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_768])).
% 3.00/1.63  tff(c_773, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_54, c_581, c_770])).
% 3.00/1.63  tff(c_774, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_64, c_60, c_773])).
% 3.00/1.63  tff(c_50, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.00/1.63  tff(c_935, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_774, c_50])).
% 3.00/1.63  tff(c_1291, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1261, c_935])).
% 3.00/1.63  tff(c_48, plain, (![C_43, B_41, A_37]: (~v1_xboole_0(C_43) | ~r2_hidden(C_43, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_37)))) | ~v13_waybel_0(B_41, k3_yellow_1(A_37)) | ~v2_waybel_0(B_41, k3_yellow_1(A_37)) | ~v1_subset_1(B_41, u1_struct_0(k3_yellow_1(A_37))) | v1_xboole_0(B_41) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.00/1.63  tff(c_1299, plain, (![A_37]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_37)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_37)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_37)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_37))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_1291, c_48])).
% 3.00/1.63  tff(c_1307, plain, (![A_37]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_37)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_37)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_37)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_37))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1299])).
% 3.00/1.63  tff(c_1404, plain, (![A_156]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_156)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_156)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_156)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_156))) | v1_xboole_0(A_156))), inference(negUnitSimplification, [status(thm)], [c_60, c_1307])).
% 3.00/1.63  tff(c_1407, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_52, c_1404])).
% 3.00/1.63  tff(c_1410, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1407])).
% 3.00/1.63  tff(c_1412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_158, c_1410])).
% 3.00/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.63  
% 3.00/1.63  Inference rules
% 3.00/1.63  ----------------------
% 3.00/1.63  #Ref     : 0
% 3.00/1.63  #Sup     : 315
% 3.00/1.63  #Fact    : 0
% 3.00/1.63  #Define  : 0
% 3.00/1.63  #Split   : 1
% 3.00/1.63  #Chain   : 0
% 3.00/1.63  #Close   : 0
% 3.00/1.63  
% 3.00/1.63  Ordering : KBO
% 3.00/1.63  
% 3.00/1.63  Simplification rules
% 3.00/1.63  ----------------------
% 3.00/1.63  #Subsume      : 79
% 3.00/1.63  #Demod        : 104
% 3.00/1.63  #Tautology    : 141
% 3.00/1.63  #SimpNegUnit  : 18
% 3.00/1.63  #BackRed      : 1
% 3.00/1.63  
% 3.00/1.63  #Partial instantiations: 0
% 3.00/1.63  #Strategies tried      : 1
% 3.00/1.63  
% 3.00/1.63  Timing (in seconds)
% 3.00/1.63  ----------------------
% 3.37/1.63  Preprocessing        : 0.45
% 3.37/1.63  Parsing              : 0.26
% 3.37/1.63  CNF conversion       : 0.02
% 3.37/1.63  Main loop            : 0.40
% 3.37/1.63  Inferencing          : 0.14
% 3.37/1.63  Reduction            : 0.14
% 3.37/1.63  Demodulation         : 0.10
% 3.37/1.63  BG Simplification    : 0.02
% 3.37/1.63  Subsumption          : 0.07
% 3.37/1.63  Abstraction          : 0.02
% 3.37/1.64  MUC search           : 0.00
% 3.37/1.64  Cooper               : 0.00
% 3.37/1.64  Total                : 0.88
% 3.37/1.64  Index Insertion      : 0.00
% 3.37/1.64  Index Deletion       : 0.00
% 3.37/1.64  Index Matching       : 0.00
% 3.37/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
