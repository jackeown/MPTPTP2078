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
% DateTime   : Thu Dec  3 10:31:25 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 134 expanded)
%              Number of leaves         :   49 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  150 ( 288 expanded)
%              Number of equality atoms :   41 (  66 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_tarski > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_149,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_56,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_67,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_48,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_77,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_108,axiom,(
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

tff(f_129,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_54,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_131,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_135,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_131])).

tff(c_153,plain,(
    ! [A_55] :
      ( ~ v1_xboole_0(u1_struct_0(A_55))
      | ~ l1_struct_0(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_156,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_153])).

tff(c_158,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_156])).

tff(c_159,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_158])).

tff(c_50,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_48,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_46,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_160,plain,(
    ! [A_56,B_57] : k1_setfam_1(k2_tarski(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_175,plain,(
    ! [B_58,A_59] : k1_setfam_1(k2_tarski(B_58,A_59)) = k3_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_160])).

tff(c_26,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_181,plain,(
    ! [B_58,A_59] : k3_xboole_0(B_58,A_59) = k3_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_26])).

tff(c_247,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k4_xboole_0(A_64,B_65)) = k3_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_15] : k4_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_277,plain,(
    ! [B_66] : k3_xboole_0(k1_xboole_0,B_66) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_18])).

tff(c_308,plain,(
    ! [B_67] : k3_xboole_0(B_67,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_277])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_322,plain,(
    ! [B_67] : k5_xboole_0(B_67,k1_xboole_0) = k4_xboole_0(B_67,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_12])).

tff(c_340,plain,(
    ! [B_67] : k5_xboole_0(B_67,k1_xboole_0) = B_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_322])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(k1_tarski(A_18),B_19)
      | r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_3'(A_25),A_25)
      | k1_xboole_0 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_345,plain,(
    ! [A_68,B_69,C_70] :
      ( ~ r1_xboole_0(A_68,B_69)
      | ~ r2_hidden(C_70,k3_xboole_0(A_68,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_554,plain,(
    ! [A_89,B_90] :
      ( ~ r1_xboole_0(A_89,B_90)
      | k3_xboole_0(A_89,B_90) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_345])).

tff(c_576,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(k1_tarski(A_18),B_19) = k1_xboole_0
      | r2_hidden(A_18,B_19) ) ),
    inference(resolution,[status(thm)],[c_22,c_554])).

tff(c_207,plain,(
    ! [B_62,A_63] : k3_xboole_0(B_62,A_63) = k3_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_26])).

tff(c_1091,plain,(
    ! [B_120,A_121] : k5_xboole_0(B_120,k3_xboole_0(A_121,B_120)) = k4_xboole_0(B_120,A_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_12])).

tff(c_1107,plain,(
    ! [B_19,A_18] :
      ( k4_xboole_0(B_19,k1_tarski(A_18)) = k5_xboole_0(B_19,k1_xboole_0)
      | r2_hidden(A_18,B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_1091])).

tff(c_1196,plain,(
    ! [B_127,A_128] :
      ( k4_xboole_0(B_127,k1_tarski(A_128)) = B_127
      | r2_hidden(A_128,B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_340,c_1107])).

tff(c_489,plain,(
    ! [A_77,B_78,C_79] :
      ( k7_subset_1(A_77,B_78,C_79) = k4_xboole_0(B_78,C_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_492,plain,(
    ! [C_79] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',C_79) = k4_xboole_0('#skF_5',C_79) ),
    inference(resolution,[status(thm)],[c_44,c_489])).

tff(c_679,plain,(
    ! [A_98,B_99] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_98))),B_99,k1_tarski(k1_xboole_0)) = k2_yellow19(A_98,k3_yellow19(A_98,k2_struct_0(A_98),B_99))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_98)))))
      | ~ v13_waybel_0(B_99,k3_yellow_1(k2_struct_0(A_98)))
      | ~ v2_waybel_0(B_99,k3_yellow_1(k2_struct_0(A_98)))
      | v1_xboole_0(B_99)
      | ~ l1_struct_0(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_681,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_679])).

tff(c_684,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_46,c_492,c_681])).

tff(c_685,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_52,c_684])).

tff(c_42,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_850,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_42])).

tff(c_1226,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1196,c_850])).

tff(c_40,plain,(
    ! [C_39,B_37,A_33] :
      ( ~ v1_xboole_0(C_39)
      | ~ r2_hidden(C_39,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_33))))
      | ~ v13_waybel_0(B_37,k3_yellow_1(A_33))
      | ~ v2_waybel_0(B_37,k3_yellow_1(A_33))
      | ~ v1_subset_1(B_37,u1_struct_0(k3_yellow_1(A_33)))
      | v1_xboole_0(B_37)
      | v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1234,plain,(
    ! [A_33] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_33))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_33))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_33))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_33)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_33) ) ),
    inference(resolution,[status(thm)],[c_1226,c_40])).

tff(c_1240,plain,(
    ! [A_33] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_33))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_33))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_33))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_33)))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1234])).

tff(c_1309,plain,(
    ! [A_133] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_133))))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_133))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_133))
      | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(A_133)))
      | v1_xboole_0(A_133) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1240])).

tff(c_1312,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_44,c_1309])).

tff(c_1315,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_1312])).

tff(c_1317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_1315])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:39:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.49  
% 3.15/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.49  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_tarski > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 3.15/1.49  
% 3.15/1.49  %Foreground sorts:
% 3.15/1.49  
% 3.15/1.49  
% 3.15/1.49  %Background operators:
% 3.15/1.49  
% 3.15/1.49  
% 3.15/1.49  %Foreground operators:
% 3.15/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.49  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.15/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.49  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.15/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.49  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.15/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.15/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.49  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.15/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.15/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.15/1.49  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.15/1.49  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.15/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.49  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.15/1.49  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.49  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.15/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.15/1.49  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.15/1.49  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.15/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.15/1.49  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.15/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.15/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.15/1.49  
% 3.15/1.51  tff(f_149, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_yellow19)).
% 3.15/1.51  tff(f_81, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.15/1.51  tff(f_89, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.15/1.51  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.15/1.51  tff(f_50, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.15/1.51  tff(f_56, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.15/1.51  tff(f_67, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.15/1.51  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.15/1.51  tff(f_54, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.15/1.51  tff(f_48, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.15/1.51  tff(f_61, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.15/1.51  tff(f_77, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.15/1.51  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.15/1.51  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.15/1.51  tff(f_108, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow19)).
% 3.15/1.51  tff(f_129, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_yellow19)).
% 3.15/1.51  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.15/1.51  tff(c_54, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.15/1.51  tff(c_131, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.15/1.51  tff(c_135, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_54, c_131])).
% 3.15/1.51  tff(c_153, plain, (![A_55]: (~v1_xboole_0(u1_struct_0(A_55)) | ~l1_struct_0(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.15/1.51  tff(c_156, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_135, c_153])).
% 3.15/1.51  tff(c_158, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_156])).
% 3.15/1.51  tff(c_159, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_56, c_158])).
% 3.15/1.51  tff(c_50, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.15/1.51  tff(c_48, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.15/1.51  tff(c_46, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.15/1.51  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.15/1.51  tff(c_52, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.15/1.51  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.15/1.51  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.15/1.51  tff(c_20, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.15/1.51  tff(c_160, plain, (![A_56, B_57]: (k1_setfam_1(k2_tarski(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.15/1.51  tff(c_175, plain, (![B_58, A_59]: (k1_setfam_1(k2_tarski(B_58, A_59))=k3_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_20, c_160])).
% 3.15/1.51  tff(c_26, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.15/1.51  tff(c_181, plain, (![B_58, A_59]: (k3_xboole_0(B_58, A_59)=k3_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_175, c_26])).
% 3.15/1.51  tff(c_247, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k4_xboole_0(A_64, B_65))=k3_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.15/1.51  tff(c_18, plain, (![A_15]: (k4_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.15/1.51  tff(c_277, plain, (![B_66]: (k3_xboole_0(k1_xboole_0, B_66)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_247, c_18])).
% 3.15/1.51  tff(c_308, plain, (![B_67]: (k3_xboole_0(B_67, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_181, c_277])).
% 3.15/1.51  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.15/1.51  tff(c_322, plain, (![B_67]: (k5_xboole_0(B_67, k1_xboole_0)=k4_xboole_0(B_67, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_308, c_12])).
% 3.15/1.51  tff(c_340, plain, (![B_67]: (k5_xboole_0(B_67, k1_xboole_0)=B_67)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_322])).
% 3.15/1.51  tff(c_22, plain, (![A_18, B_19]: (r1_xboole_0(k1_tarski(A_18), B_19) | r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.15/1.51  tff(c_30, plain, (![A_25]: (r2_hidden('#skF_3'(A_25), A_25) | k1_xboole_0=A_25)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.15/1.51  tff(c_345, plain, (![A_68, B_69, C_70]: (~r1_xboole_0(A_68, B_69) | ~r2_hidden(C_70, k3_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.15/1.51  tff(c_554, plain, (![A_89, B_90]: (~r1_xboole_0(A_89, B_90) | k3_xboole_0(A_89, B_90)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_345])).
% 3.15/1.51  tff(c_576, plain, (![A_18, B_19]: (k3_xboole_0(k1_tarski(A_18), B_19)=k1_xboole_0 | r2_hidden(A_18, B_19))), inference(resolution, [status(thm)], [c_22, c_554])).
% 3.15/1.51  tff(c_207, plain, (![B_62, A_63]: (k3_xboole_0(B_62, A_63)=k3_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_175, c_26])).
% 3.15/1.51  tff(c_1091, plain, (![B_120, A_121]: (k5_xboole_0(B_120, k3_xboole_0(A_121, B_120))=k4_xboole_0(B_120, A_121))), inference(superposition, [status(thm), theory('equality')], [c_207, c_12])).
% 3.15/1.51  tff(c_1107, plain, (![B_19, A_18]: (k4_xboole_0(B_19, k1_tarski(A_18))=k5_xboole_0(B_19, k1_xboole_0) | r2_hidden(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_576, c_1091])).
% 3.15/1.51  tff(c_1196, plain, (![B_127, A_128]: (k4_xboole_0(B_127, k1_tarski(A_128))=B_127 | r2_hidden(A_128, B_127))), inference(demodulation, [status(thm), theory('equality')], [c_340, c_1107])).
% 3.15/1.51  tff(c_489, plain, (![A_77, B_78, C_79]: (k7_subset_1(A_77, B_78, C_79)=k4_xboole_0(B_78, C_79) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.51  tff(c_492, plain, (![C_79]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', C_79)=k4_xboole_0('#skF_5', C_79))), inference(resolution, [status(thm)], [c_44, c_489])).
% 3.15/1.51  tff(c_679, plain, (![A_98, B_99]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_98))), B_99, k1_tarski(k1_xboole_0))=k2_yellow19(A_98, k3_yellow19(A_98, k2_struct_0(A_98), B_99)) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_98))))) | ~v13_waybel_0(B_99, k3_yellow_1(k2_struct_0(A_98))) | ~v2_waybel_0(B_99, k3_yellow_1(k2_struct_0(A_98))) | v1_xboole_0(B_99) | ~l1_struct_0(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.15/1.51  tff(c_681, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_679])).
% 3.15/1.51  tff(c_684, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_46, c_492, c_681])).
% 3.15/1.51  tff(c_685, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_56, c_52, c_684])).
% 3.15/1.51  tff(c_42, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.15/1.51  tff(c_850, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_685, c_42])).
% 3.15/1.51  tff(c_1226, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1196, c_850])).
% 3.15/1.51  tff(c_40, plain, (![C_39, B_37, A_33]: (~v1_xboole_0(C_39) | ~r2_hidden(C_39, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_33)))) | ~v13_waybel_0(B_37, k3_yellow_1(A_33)) | ~v2_waybel_0(B_37, k3_yellow_1(A_33)) | ~v1_subset_1(B_37, u1_struct_0(k3_yellow_1(A_33))) | v1_xboole_0(B_37) | v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.15/1.51  tff(c_1234, plain, (![A_33]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_33)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_33)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_33)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_33))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_33))), inference(resolution, [status(thm)], [c_1226, c_40])).
% 3.15/1.51  tff(c_1240, plain, (![A_33]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_33)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_33)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_33)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_33))) | v1_xboole_0('#skF_5') | v1_xboole_0(A_33))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1234])).
% 3.15/1.51  tff(c_1309, plain, (![A_133]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_133)))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_133)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_133)) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(A_133))) | v1_xboole_0(A_133))), inference(negUnitSimplification, [status(thm)], [c_52, c_1240])).
% 3.15/1.51  tff(c_1312, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_1309])).
% 3.15/1.51  tff(c_1315, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_1312])).
% 3.15/1.51  tff(c_1317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_1315])).
% 3.15/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.51  
% 3.15/1.51  Inference rules
% 3.15/1.51  ----------------------
% 3.15/1.51  #Ref     : 0
% 3.15/1.51  #Sup     : 292
% 3.15/1.51  #Fact    : 0
% 3.15/1.51  #Define  : 0
% 3.15/1.51  #Split   : 2
% 3.15/1.51  #Chain   : 0
% 3.15/1.51  #Close   : 0
% 3.15/1.51  
% 3.15/1.51  Ordering : KBO
% 3.15/1.51  
% 3.15/1.51  Simplification rules
% 3.15/1.51  ----------------------
% 3.15/1.51  #Subsume      : 67
% 3.15/1.51  #Demod        : 119
% 3.15/1.51  #Tautology    : 157
% 3.15/1.51  #SimpNegUnit  : 17
% 3.15/1.51  #BackRed      : 1
% 3.15/1.51  
% 3.15/1.51  #Partial instantiations: 0
% 3.15/1.51  #Strategies tried      : 1
% 3.15/1.51  
% 3.15/1.51  Timing (in seconds)
% 3.15/1.51  ----------------------
% 3.15/1.51  Preprocessing        : 0.35
% 3.15/1.51  Parsing              : 0.20
% 3.15/1.51  CNF conversion       : 0.02
% 3.15/1.51  Main loop            : 0.38
% 3.15/1.51  Inferencing          : 0.14
% 3.15/1.51  Reduction            : 0.13
% 3.15/1.51  Demodulation         : 0.09
% 3.15/1.51  BG Simplification    : 0.02
% 3.15/1.51  Subsumption          : 0.06
% 3.15/1.51  Abstraction          : 0.02
% 3.15/1.51  MUC search           : 0.00
% 3.15/1.51  Cooper               : 0.00
% 3.15/1.51  Total                : 0.76
% 3.15/1.51  Index Insertion      : 0.00
% 3.15/1.51  Index Deletion       : 0.00
% 3.15/1.51  Index Matching       : 0.00
% 3.15/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
