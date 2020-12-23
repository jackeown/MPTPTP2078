%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:26 EST 2020

% Result     : Theorem 5.75s
% Output     : CNFRefutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 254 expanded)
%              Number of leaves         :   46 ( 110 expanded)
%              Depth                    :   17
%              Number of atoms          :  174 ( 608 expanded)
%              Number of equality atoms :   51 ( 165 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(f_150,negated_conjecture,(
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

tff(f_62,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_68,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_109,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_130,axiom,(
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

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_58,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_54,plain,(
    v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_52,plain,(
    v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_50,plain,(
    v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_24,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_173,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k4_xboole_0(A_64,B_65)) = k3_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_30,plain,(
    ! [A_22] : k4_xboole_0(k1_xboole_0,A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_203,plain,(
    ! [B_66] : k3_xboole_0(k1_xboole_0,B_66) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_30])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_211,plain,(
    ! [B_66] : k3_xboole_0(B_66,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_2])).

tff(c_192,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k3_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_173])).

tff(c_310,plain,(
    ! [A_74] : k4_xboole_0(A_74,A_74) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_192])).

tff(c_28,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_315,plain,(
    ! [A_74] : k4_xboole_0(A_74,k1_xboole_0) = k3_xboole_0(A_74,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_28])).

tff(c_333,plain,(
    ! [A_74] : k3_xboole_0(A_74,A_74) = A_74 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_315])).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k3_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_472,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,B_91)
      | ~ r2_hidden(C_92,B_91)
      | ~ r2_hidden(C_92,A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_906,plain,(
    ! [C_133,B_134,A_135] :
      ( ~ r2_hidden(C_133,B_134)
      | ~ r2_hidden(C_133,A_135)
      | k3_xboole_0(A_135,B_134) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_472])).

tff(c_1199,plain,(
    ! [A_149,A_150] :
      ( ~ r2_hidden('#skF_1'(A_149),A_150)
      | k3_xboole_0(A_150,A_149) != k1_xboole_0
      | v1_xboole_0(A_149) ) ),
    inference(resolution,[status(thm)],[c_6,c_906])).

tff(c_1211,plain,(
    ! [A_3] :
      ( k3_xboole_0(A_3,A_3) != k1_xboole_0
      | v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_1199])).

tff(c_1215,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_1211])).

tff(c_570,plain,(
    ! [A_98,B_99,C_100] :
      ( k7_subset_1(A_98,B_99,C_100) = k4_xboole_0(B_99,C_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_573,plain,(
    ! [C_100] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',C_100) = k4_xboole_0('#skF_4',C_100) ),
    inference(resolution,[status(thm)],[c_48,c_570])).

tff(c_737,plain,(
    ! [A_120,B_121] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_120))),B_121,k1_tarski(k1_xboole_0)) = k2_yellow19(A_120,k3_yellow19(A_120,k2_struct_0(A_120),B_121))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_120)))))
      | ~ v13_waybel_0(B_121,k3_yellow_1(k2_struct_0(A_120)))
      | ~ v2_waybel_0(B_121,k3_yellow_1(k2_struct_0(A_120)))
      | v1_xboole_0(B_121)
      | ~ l1_struct_0(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_739,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_737])).

tff(c_742,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_50,c_573,c_739])).

tff(c_743,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_56,c_742])).

tff(c_46,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_847,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_46])).

tff(c_339,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_348,plain,(
    ! [B_66] : k5_xboole_0(B_66,k1_xboole_0) = k4_xboole_0(B_66,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_339])).

tff(c_360,plain,(
    ! [B_66] : k5_xboole_0(B_66,k1_xboole_0) = B_66 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_348])).

tff(c_286,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_2'(A_70,B_71),B_71)
      | r1_xboole_0(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_152,plain,(
    ! [A_57,B_58] :
      ( r1_xboole_0(k1_tarski(A_57),k1_tarski(B_58))
      | B_58 = A_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_23,B_24] :
      ( ~ r2_hidden(A_23,B_24)
      | ~ r1_xboole_0(k1_tarski(A_23),B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_156,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden(A_57,k1_tarski(B_58))
      | B_58 = A_57 ) ),
    inference(resolution,[status(thm)],[c_152,c_32])).

tff(c_744,plain,(
    ! [A_122,B_123] :
      ( '#skF_2'(A_122,k1_tarski(B_123)) = B_123
      | r1_xboole_0(A_122,k1_tarski(B_123)) ) ),
    inference(resolution,[status(thm)],[c_286,c_156])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4710,plain,(
    ! [A_258,B_259] :
      ( k3_xboole_0(A_258,k1_tarski(B_259)) = k1_xboole_0
      | '#skF_2'(A_258,k1_tarski(B_259)) = B_259 ) ),
    inference(resolution,[status(thm)],[c_744,c_8])).

tff(c_20,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4784,plain,(
    ! [A_258,B_259] :
      ( k4_xboole_0(A_258,k1_tarski(B_259)) = k5_xboole_0(A_258,k1_xboole_0)
      | '#skF_2'(A_258,k1_tarski(B_259)) = B_259 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4710,c_20])).

tff(c_5188,plain,(
    ! [A_266,B_267] :
      ( k4_xboole_0(A_266,k1_tarski(B_267)) = A_266
      | '#skF_2'(A_266,k1_tarski(B_267)) = B_267 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_4784])).

tff(c_5291,plain,(
    '#skF_2'('#skF_4',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_5188,c_847])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_2'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5346,plain,
    ( r2_hidden(k1_xboole_0,'#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5291,c_18])).

tff(c_5365,plain,(
    r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_5346])).

tff(c_5372,plain,(
    k3_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5365,c_8])).

tff(c_5424,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) = k5_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5372,c_20])).

tff(c_5466,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_5424])).

tff(c_5468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_847,c_5466])).

tff(c_5469,plain,(
    r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_5346])).

tff(c_44,plain,(
    ! [C_41,B_39,A_35] :
      ( ~ v1_xboole_0(C_41)
      | ~ r2_hidden(C_41,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35))))
      | ~ v13_waybel_0(B_39,k3_yellow_1(A_35))
      | ~ v2_waybel_0(B_39,k3_yellow_1(A_35))
      | ~ v1_subset_1(B_39,u1_struct_0(k3_yellow_1(A_35)))
      | v1_xboole_0(B_39)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5482,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_35))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_35))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_35)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_5469,c_44])).

tff(c_5495,plain,(
    ! [A_35] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_35))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_35))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_35)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_5482])).

tff(c_5784,plain,(
    ! [A_277] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_277))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_277))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_277))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_277)))
      | v1_xboole_0(A_277) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_5495])).

tff(c_5787,plain,
    ( ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_5784])).

tff(c_5790,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_5787])).

tff(c_38,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(k2_struct_0(A_30))
      | ~ l1_struct_0(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_5797,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5790,c_38])).

tff(c_5802,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5797])).

tff(c_5804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_5802])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:23:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.75/2.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.10  
% 5.75/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.75/2.11  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 5.75/2.11  
% 5.75/2.11  %Foreground sorts:
% 5.75/2.11  
% 5.75/2.11  
% 5.75/2.11  %Background operators:
% 5.75/2.11  
% 5.75/2.11  
% 5.75/2.11  %Foreground operators:
% 5.75/2.11  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.75/2.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.75/2.11  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 5.75/2.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.75/2.11  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 5.75/2.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.75/2.11  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 5.75/2.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.75/2.11  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.75/2.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.75/2.11  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 5.75/2.11  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.75/2.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.75/2.11  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.75/2.11  tff('#skF_3', type, '#skF_3': $i).
% 5.75/2.11  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 5.75/2.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.75/2.11  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.75/2.11  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 5.75/2.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.75/2.11  tff('#skF_4', type, '#skF_4': $i).
% 5.75/2.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.75/2.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.75/2.11  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 5.75/2.11  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 5.75/2.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.75/2.11  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.75/2.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.75/2.11  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.75/2.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.75/2.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.75/2.11  
% 5.84/2.12  tff(f_150, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 5.84/2.12  tff(f_62, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.84/2.12  tff(f_66, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.84/2.12  tff(f_68, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 5.84/2.12  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.84/2.12  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.84/2.12  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.84/2.12  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.84/2.12  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.84/2.12  tff(f_109, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 5.84/2.12  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.84/2.12  tff(f_78, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 5.84/2.12  tff(f_73, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 5.84/2.12  tff(f_130, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 5.84/2.12  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 5.84/2.12  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.84/2.12  tff(c_58, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.84/2.12  tff(c_54, plain, (v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.84/2.12  tff(c_52, plain, (v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.84/2.12  tff(c_50, plain, (v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.84/2.12  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.84/2.12  tff(c_56, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.84/2.12  tff(c_24, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.84/2.12  tff(c_173, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k4_xboole_0(A_64, B_65))=k3_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.84/2.12  tff(c_30, plain, (![A_22]: (k4_xboole_0(k1_xboole_0, A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.84/2.12  tff(c_203, plain, (![B_66]: (k3_xboole_0(k1_xboole_0, B_66)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_173, c_30])).
% 5.84/2.12  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.84/2.12  tff(c_211, plain, (![B_66]: (k3_xboole_0(B_66, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_203, c_2])).
% 5.84/2.12  tff(c_192, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_173])).
% 5.84/2.12  tff(c_310, plain, (![A_74]: (k4_xboole_0(A_74, A_74)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_211, c_192])).
% 5.84/2.12  tff(c_28, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.84/2.12  tff(c_315, plain, (![A_74]: (k4_xboole_0(A_74, k1_xboole_0)=k3_xboole_0(A_74, A_74))), inference(superposition, [status(thm), theory('equality')], [c_310, c_28])).
% 5.84/2.12  tff(c_333, plain, (![A_74]: (k3_xboole_0(A_74, A_74)=A_74)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_315])).
% 5.84/2.12  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.84/2.12  tff(c_10, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k3_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.84/2.12  tff(c_472, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, B_91) | ~r2_hidden(C_92, B_91) | ~r2_hidden(C_92, A_90))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.84/2.12  tff(c_906, plain, (![C_133, B_134, A_135]: (~r2_hidden(C_133, B_134) | ~r2_hidden(C_133, A_135) | k3_xboole_0(A_135, B_134)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_472])).
% 5.84/2.12  tff(c_1199, plain, (![A_149, A_150]: (~r2_hidden('#skF_1'(A_149), A_150) | k3_xboole_0(A_150, A_149)!=k1_xboole_0 | v1_xboole_0(A_149))), inference(resolution, [status(thm)], [c_6, c_906])).
% 5.84/2.12  tff(c_1211, plain, (![A_3]: (k3_xboole_0(A_3, A_3)!=k1_xboole_0 | v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_1199])).
% 5.84/2.12  tff(c_1215, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_333, c_1211])).
% 5.84/2.12  tff(c_570, plain, (![A_98, B_99, C_100]: (k7_subset_1(A_98, B_99, C_100)=k4_xboole_0(B_99, C_100) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.84/2.12  tff(c_573, plain, (![C_100]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', C_100)=k4_xboole_0('#skF_4', C_100))), inference(resolution, [status(thm)], [c_48, c_570])).
% 5.84/2.12  tff(c_737, plain, (![A_120, B_121]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_120))), B_121, k1_tarski(k1_xboole_0))=k2_yellow19(A_120, k3_yellow19(A_120, k2_struct_0(A_120), B_121)) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_120))))) | ~v13_waybel_0(B_121, k3_yellow_1(k2_struct_0(A_120))) | ~v2_waybel_0(B_121, k3_yellow_1(k2_struct_0(A_120))) | v1_xboole_0(B_121) | ~l1_struct_0(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.84/2.12  tff(c_739, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_737])).
% 5.84/2.12  tff(c_742, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_50, c_573, c_739])).
% 5.84/2.12  tff(c_743, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_60, c_56, c_742])).
% 5.84/2.12  tff(c_46, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.84/2.12  tff(c_847, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_743, c_46])).
% 5.84/2.12  tff(c_339, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.84/2.12  tff(c_348, plain, (![B_66]: (k5_xboole_0(B_66, k1_xboole_0)=k4_xboole_0(B_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_211, c_339])).
% 5.84/2.12  tff(c_360, plain, (![B_66]: (k5_xboole_0(B_66, k1_xboole_0)=B_66)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_348])).
% 5.84/2.12  tff(c_286, plain, (![A_70, B_71]: (r2_hidden('#skF_2'(A_70, B_71), B_71) | r1_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.84/2.12  tff(c_152, plain, (![A_57, B_58]: (r1_xboole_0(k1_tarski(A_57), k1_tarski(B_58)) | B_58=A_57)), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.84/2.12  tff(c_32, plain, (![A_23, B_24]: (~r2_hidden(A_23, B_24) | ~r1_xboole_0(k1_tarski(A_23), B_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.84/2.12  tff(c_156, plain, (![A_57, B_58]: (~r2_hidden(A_57, k1_tarski(B_58)) | B_58=A_57)), inference(resolution, [status(thm)], [c_152, c_32])).
% 5.84/2.12  tff(c_744, plain, (![A_122, B_123]: ('#skF_2'(A_122, k1_tarski(B_123))=B_123 | r1_xboole_0(A_122, k1_tarski(B_123)))), inference(resolution, [status(thm)], [c_286, c_156])).
% 5.84/2.12  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.84/2.12  tff(c_4710, plain, (![A_258, B_259]: (k3_xboole_0(A_258, k1_tarski(B_259))=k1_xboole_0 | '#skF_2'(A_258, k1_tarski(B_259))=B_259)), inference(resolution, [status(thm)], [c_744, c_8])).
% 5.84/2.12  tff(c_20, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.84/2.12  tff(c_4784, plain, (![A_258, B_259]: (k4_xboole_0(A_258, k1_tarski(B_259))=k5_xboole_0(A_258, k1_xboole_0) | '#skF_2'(A_258, k1_tarski(B_259))=B_259)), inference(superposition, [status(thm), theory('equality')], [c_4710, c_20])).
% 5.84/2.12  tff(c_5188, plain, (![A_266, B_267]: (k4_xboole_0(A_266, k1_tarski(B_267))=A_266 | '#skF_2'(A_266, k1_tarski(B_267))=B_267)), inference(demodulation, [status(thm), theory('equality')], [c_360, c_4784])).
% 5.84/2.12  tff(c_5291, plain, ('#skF_2'('#skF_4', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_5188, c_847])).
% 5.84/2.12  tff(c_18, plain, (![A_9, B_10]: (r2_hidden('#skF_2'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.84/2.12  tff(c_5346, plain, (r2_hidden(k1_xboole_0, '#skF_4') | r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5291, c_18])).
% 5.84/2.12  tff(c_5365, plain, (r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_5346])).
% 5.84/2.12  tff(c_5372, plain, (k3_xboole_0('#skF_4', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(resolution, [status(thm)], [c_5365, c_8])).
% 5.84/2.12  tff(c_5424, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))=k5_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5372, c_20])).
% 5.84/2.12  tff(c_5466, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_360, c_5424])).
% 5.84/2.12  tff(c_5468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_847, c_5466])).
% 5.84/2.12  tff(c_5469, plain, (r2_hidden(k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_5346])).
% 5.84/2.12  tff(c_44, plain, (![C_41, B_39, A_35]: (~v1_xboole_0(C_41) | ~r2_hidden(C_41, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35)))) | ~v13_waybel_0(B_39, k3_yellow_1(A_35)) | ~v2_waybel_0(B_39, k3_yellow_1(A_35)) | ~v1_subset_1(B_39, u1_struct_0(k3_yellow_1(A_35))) | v1_xboole_0(B_39) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.84/2.12  tff(c_5482, plain, (![A_35]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_35)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_35)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_35))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_5469, c_44])).
% 5.84/2.12  tff(c_5495, plain, (![A_35]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_35)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_35)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_35)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_35))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_5482])).
% 5.84/2.13  tff(c_5784, plain, (![A_277]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_277)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_277)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_277)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_277))) | v1_xboole_0(A_277))), inference(negUnitSimplification, [status(thm)], [c_56, c_5495])).
% 5.84/2.13  tff(c_5787, plain, (~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_5784])).
% 5.84/2.13  tff(c_5790, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_5787])).
% 5.84/2.13  tff(c_38, plain, (![A_30]: (~v1_xboole_0(k2_struct_0(A_30)) | ~l1_struct_0(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.84/2.13  tff(c_5797, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_5790, c_38])).
% 5.84/2.13  tff(c_5802, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_5797])).
% 5.84/2.13  tff(c_5804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_5802])).
% 5.84/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.84/2.13  
% 5.84/2.13  Inference rules
% 5.84/2.13  ----------------------
% 5.84/2.13  #Ref     : 1
% 5.84/2.13  #Sup     : 1448
% 5.84/2.13  #Fact    : 0
% 5.84/2.13  #Define  : 0
% 5.84/2.13  #Split   : 3
% 5.84/2.13  #Chain   : 0
% 5.84/2.13  #Close   : 0
% 5.84/2.13  
% 5.84/2.13  Ordering : KBO
% 5.84/2.13  
% 5.84/2.13  Simplification rules
% 5.84/2.13  ----------------------
% 5.84/2.13  #Subsume      : 441
% 5.84/2.13  #Demod        : 435
% 5.84/2.13  #Tautology    : 611
% 5.84/2.13  #SimpNegUnit  : 16
% 5.84/2.13  #BackRed      : 1
% 5.84/2.13  
% 5.84/2.13  #Partial instantiations: 0
% 5.84/2.13  #Strategies tried      : 1
% 5.84/2.13  
% 5.84/2.13  Timing (in seconds)
% 5.84/2.13  ----------------------
% 5.84/2.13  Preprocessing        : 0.35
% 5.84/2.13  Parsing              : 0.19
% 5.84/2.13  CNF conversion       : 0.02
% 5.84/2.13  Main loop            : 1.00
% 5.84/2.13  Inferencing          : 0.34
% 5.84/2.13  Reduction            : 0.36
% 5.84/2.13  Demodulation         : 0.27
% 5.84/2.13  BG Simplification    : 0.04
% 5.84/2.13  Subsumption          : 0.20
% 5.84/2.13  Abstraction          : 0.05
% 5.84/2.13  MUC search           : 0.00
% 5.84/2.13  Cooper               : 0.00
% 5.84/2.13  Total                : 1.40
% 5.84/2.13  Index Insertion      : 0.00
% 5.84/2.13  Index Deletion       : 0.00
% 5.84/2.13  Index Matching       : 0.00
% 5.84/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
