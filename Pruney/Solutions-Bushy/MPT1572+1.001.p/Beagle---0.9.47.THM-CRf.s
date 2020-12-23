%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1572+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:05 EST 2020

% Result     : Theorem 8.90s
% Output     : CNFRefutation 9.27s
% Verified   : 
% Statistics : Number of formulae       :  414 (1191 expanded)
%              Number of leaves         :   23 ( 368 expanded)
%              Depth                    :   11
%              Number of atoms          : 1580 (6418 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_lattice3 > r2_yellow_0 > r1_yellow_0 > m1_subset_1 > v2_struct_0 > l1_orders_2 > k3_xboole_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( r1_yellow_0(A,B)
             => r1_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) )
            & ( r1_yellow_0(A,k3_xboole_0(B,u1_struct_0(A)))
             => r1_yellow_0(A,B) )
            & ( r2_yellow_0(A,B)
             => r2_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) )
            & ( r2_yellow_0(A,k3_xboole_0(B,u1_struct_0(A)))
             => r2_yellow_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_yellow_0)).

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( ( ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_lattice3(A,B,D)
                <=> r2_lattice3(A,C,D) ) )
            & r1_yellow_0(A,B) )
         => r1_yellow_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_yellow_0)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( ( r2_lattice3(A,B,C)
             => r2_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C) )
            & ( r2_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C)
             => r2_lattice3(A,B,C) )
            & ( r1_lattice3(A,B,C)
             => r1_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C) )
            & ( r1_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C)
             => r1_lattice3(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_yellow_0)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( ( ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r1_lattice3(A,B,D)
                <=> r1_lattice3(A,C,D) ) )
            & r2_yellow_0(A,B) )
         => r2_yellow_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_yellow_0)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_30,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_54,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_4')
    | r2_yellow_0('#skF_3','#skF_5')
    | ~ r1_yellow_0('#skF_3','#skF_6')
    | r1_yellow_0('#skF_3','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_65,plain,(
    ~ r1_yellow_0('#skF_3','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_62,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_4')
    | r2_yellow_0('#skF_3','#skF_5')
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | r1_yellow_0('#skF_3','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_66,plain,(
    ~ r2_yellow_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_64,plain,
    ( r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3')))
    | r2_yellow_0('#skF_3','#skF_5')
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | r1_yellow_0('#skF_3','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_69,plain,(
    r1_yellow_0('#skF_3','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_2,plain,(
    ! [A_1,B_6,C_7] :
      ( m1_subset_1('#skF_1'(A_1,B_6,C_7),u1_struct_0(A_1))
      | r1_yellow_0(A_1,C_7)
      | ~ r1_yellow_0(A_1,B_6)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_98,plain,(
    ! [A_41,B_42,C_43] :
      ( r2_lattice3(A_41,B_42,'#skF_1'(A_41,B_42,C_43))
      | r2_lattice3(A_41,C_43,'#skF_1'(A_41,B_42,C_43))
      | r1_yellow_0(A_41,C_43)
      | ~ r1_yellow_0(A_41,B_42)
      | ~ l1_orders_2(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_17,B_20,C_21] :
      ( r2_lattice3(A_17,B_20,C_21)
      | ~ r2_lattice3(A_17,k3_xboole_0(B_20,u1_struct_0(A_17)),C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_394,plain,(
    ! [A_102,B_103,B_104] :
      ( r2_lattice3(A_102,B_103,'#skF_1'(A_102,B_104,k3_xboole_0(B_103,u1_struct_0(A_102))))
      | ~ m1_subset_1('#skF_1'(A_102,B_104,k3_xboole_0(B_103,u1_struct_0(A_102))),u1_struct_0(A_102))
      | r2_lattice3(A_102,B_104,'#skF_1'(A_102,B_104,k3_xboole_0(B_103,u1_struct_0(A_102))))
      | r1_yellow_0(A_102,k3_xboole_0(B_103,u1_struct_0(A_102)))
      | ~ r1_yellow_0(A_102,B_104)
      | ~ l1_orders_2(A_102)
      | v2_struct_0(A_102) ) ),
    inference(resolution,[status(thm)],[c_98,c_26])).

tff(c_398,plain,(
    ! [A_1,B_103,B_6] :
      ( r2_lattice3(A_1,B_103,'#skF_1'(A_1,B_6,k3_xboole_0(B_103,u1_struct_0(A_1))))
      | r2_lattice3(A_1,B_6,'#skF_1'(A_1,B_6,k3_xboole_0(B_103,u1_struct_0(A_1))))
      | r1_yellow_0(A_1,k3_xboole_0(B_103,u1_struct_0(A_1)))
      | ~ r1_yellow_0(A_1,B_6)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_394])).

tff(c_411,plain,(
    ! [A_1,B_103] :
      ( r1_yellow_0(A_1,k3_xboole_0(B_103,u1_struct_0(A_1)))
      | ~ r1_yellow_0(A_1,B_103)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1)
      | r2_lattice3(A_1,B_103,'#skF_1'(A_1,B_103,k3_xboole_0(B_103,u1_struct_0(A_1)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_398])).

tff(c_439,plain,(
    ! [A_108,B_109] :
      ( r1_yellow_0(A_108,k3_xboole_0(B_109,u1_struct_0(A_108)))
      | ~ r1_yellow_0(A_108,B_109)
      | ~ l1_orders_2(A_108)
      | v2_struct_0(A_108)
      | r2_lattice3(A_108,B_109,'#skF_1'(A_108,B_109,k3_xboole_0(B_109,u1_struct_0(A_108)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_398])).

tff(c_28,plain,(
    ! [A_17,B_20,C_21] :
      ( r2_lattice3(A_17,k3_xboole_0(B_20,u1_struct_0(A_17)),C_21)
      | ~ r2_lattice3(A_17,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_143,plain,(
    ! [A_50,C_51,B_52] :
      ( ~ r2_lattice3(A_50,C_51,'#skF_1'(A_50,B_52,C_51))
      | ~ r2_lattice3(A_50,B_52,'#skF_1'(A_50,B_52,C_51))
      | r1_yellow_0(A_50,C_51)
      | ~ r1_yellow_0(A_50,B_52)
      | ~ l1_orders_2(A_50)
      | v2_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_151,plain,(
    ! [A_17,B_52,B_20] :
      ( ~ r2_lattice3(A_17,B_52,'#skF_1'(A_17,B_52,k3_xboole_0(B_20,u1_struct_0(A_17))))
      | r1_yellow_0(A_17,k3_xboole_0(B_20,u1_struct_0(A_17)))
      | ~ r1_yellow_0(A_17,B_52)
      | ~ r2_lattice3(A_17,B_20,'#skF_1'(A_17,B_52,k3_xboole_0(B_20,u1_struct_0(A_17))))
      | ~ m1_subset_1('#skF_1'(A_17,B_52,k3_xboole_0(B_20,u1_struct_0(A_17))),u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_28,c_143])).

tff(c_475,plain,(
    ! [A_116,B_117] :
      ( ~ r2_lattice3(A_116,B_117,'#skF_1'(A_116,B_117,k3_xboole_0(B_117,u1_struct_0(A_116))))
      | ~ m1_subset_1('#skF_1'(A_116,B_117,k3_xboole_0(B_117,u1_struct_0(A_116))),u1_struct_0(A_116))
      | r1_yellow_0(A_116,k3_xboole_0(B_117,u1_struct_0(A_116)))
      | ~ r1_yellow_0(A_116,B_117)
      | ~ l1_orders_2(A_116)
      | v2_struct_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_439,c_151])).

tff(c_486,plain,(
    ! [A_118,B_119] :
      ( ~ m1_subset_1('#skF_1'(A_118,B_119,k3_xboole_0(B_119,u1_struct_0(A_118))),u1_struct_0(A_118))
      | r1_yellow_0(A_118,k3_xboole_0(B_119,u1_struct_0(A_118)))
      | ~ r1_yellow_0(A_118,B_119)
      | ~ l1_orders_2(A_118)
      | v2_struct_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_411,c_475])).

tff(c_492,plain,(
    ! [A_120,B_121] :
      ( r1_yellow_0(A_120,k3_xboole_0(B_121,u1_struct_0(A_120)))
      | ~ r1_yellow_0(A_120,B_121)
      | ~ l1_orders_2(A_120)
      | v2_struct_0(A_120) ) ),
    inference(resolution,[status(thm)],[c_2,c_486])).

tff(c_48,plain,
    ( r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3')))
    | r2_yellow_0('#skF_3','#skF_5')
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_83,plain,(
    ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_498,plain,
    ( ~ r1_yellow_0('#skF_3','#skF_7')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_492,c_83])).

tff(c_502,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_69,c_498])).

tff(c_504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_502])).

tff(c_505,plain,
    ( r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | r2_yellow_0('#skF_3','#skF_5')
    | r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_507,plain,(
    r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_505])).

tff(c_12,plain,(
    ! [A_9,B_14,C_15] :
      ( m1_subset_1('#skF_2'(A_9,B_14,C_15),u1_struct_0(A_9))
      | r2_yellow_0(A_9,C_15)
      | ~ r2_yellow_0(A_9,B_14)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_560,plain,(
    ! [A_128,B_129,C_130] :
      ( r1_lattice3(A_128,B_129,'#skF_2'(A_128,B_129,C_130))
      | r1_lattice3(A_128,C_130,'#skF_2'(A_128,B_129,C_130))
      | r2_yellow_0(A_128,C_130)
      | ~ r2_yellow_0(A_128,B_129)
      | ~ l1_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [A_17,B_20,C_21] :
      ( r1_lattice3(A_17,B_20,C_21)
      | ~ r1_lattice3(A_17,k3_xboole_0(B_20,u1_struct_0(A_17)),C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_781,plain,(
    ! [A_175,B_176,C_177] :
      ( r1_lattice3(A_175,B_176,'#skF_2'(A_175,k3_xboole_0(B_176,u1_struct_0(A_175)),C_177))
      | ~ m1_subset_1('#skF_2'(A_175,k3_xboole_0(B_176,u1_struct_0(A_175)),C_177),u1_struct_0(A_175))
      | r1_lattice3(A_175,C_177,'#skF_2'(A_175,k3_xboole_0(B_176,u1_struct_0(A_175)),C_177))
      | r2_yellow_0(A_175,C_177)
      | ~ r2_yellow_0(A_175,k3_xboole_0(B_176,u1_struct_0(A_175)))
      | ~ l1_orders_2(A_175)
      | v2_struct_0(A_175) ) ),
    inference(resolution,[status(thm)],[c_560,c_22])).

tff(c_785,plain,(
    ! [A_9,B_176,C_15] :
      ( r1_lattice3(A_9,B_176,'#skF_2'(A_9,k3_xboole_0(B_176,u1_struct_0(A_9)),C_15))
      | r1_lattice3(A_9,C_15,'#skF_2'(A_9,k3_xboole_0(B_176,u1_struct_0(A_9)),C_15))
      | r2_yellow_0(A_9,C_15)
      | ~ r2_yellow_0(A_9,k3_xboole_0(B_176,u1_struct_0(A_9)))
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_781])).

tff(c_798,plain,(
    ! [A_9,B_176] :
      ( r2_yellow_0(A_9,B_176)
      | ~ r2_yellow_0(A_9,k3_xboole_0(B_176,u1_struct_0(A_9)))
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9)
      | r1_lattice3(A_9,B_176,'#skF_2'(A_9,k3_xboole_0(B_176,u1_struct_0(A_9)),B_176)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_785])).

tff(c_24,plain,(
    ! [A_17,B_20,C_21] :
      ( r1_lattice3(A_17,k3_xboole_0(B_20,u1_struct_0(A_17)),C_21)
      | ~ r1_lattice3(A_17,B_20,C_21)
      | ~ m1_subset_1(C_21,u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_819,plain,(
    ! [A_181,B_182] :
      ( r2_yellow_0(A_181,B_182)
      | ~ r2_yellow_0(A_181,k3_xboole_0(B_182,u1_struct_0(A_181)))
      | ~ l1_orders_2(A_181)
      | v2_struct_0(A_181)
      | r1_lattice3(A_181,B_182,'#skF_2'(A_181,k3_xboole_0(B_182,u1_struct_0(A_181)),B_182)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_785])).

tff(c_14,plain,(
    ! [A_9,C_15,B_14] :
      ( ~ r1_lattice3(A_9,C_15,'#skF_2'(A_9,B_14,C_15))
      | ~ r1_lattice3(A_9,B_14,'#skF_2'(A_9,B_14,C_15))
      | r2_yellow_0(A_9,C_15)
      | ~ r2_yellow_0(A_9,B_14)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_828,plain,(
    ! [A_183,B_184] :
      ( ~ r1_lattice3(A_183,k3_xboole_0(B_184,u1_struct_0(A_183)),'#skF_2'(A_183,k3_xboole_0(B_184,u1_struct_0(A_183)),B_184))
      | r2_yellow_0(A_183,B_184)
      | ~ r2_yellow_0(A_183,k3_xboole_0(B_184,u1_struct_0(A_183)))
      | ~ l1_orders_2(A_183)
      | v2_struct_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_819,c_14])).

tff(c_844,plain,(
    ! [A_185,B_186] :
      ( r2_yellow_0(A_185,B_186)
      | ~ r2_yellow_0(A_185,k3_xboole_0(B_186,u1_struct_0(A_185)))
      | ~ r1_lattice3(A_185,B_186,'#skF_2'(A_185,k3_xboole_0(B_186,u1_struct_0(A_185)),B_186))
      | ~ m1_subset_1('#skF_2'(A_185,k3_xboole_0(B_186,u1_struct_0(A_185)),B_186),u1_struct_0(A_185))
      | ~ l1_orders_2(A_185)
      | v2_struct_0(A_185) ) ),
    inference(resolution,[status(thm)],[c_24,c_828])).

tff(c_855,plain,(
    ! [A_187,B_188] :
      ( ~ m1_subset_1('#skF_2'(A_187,k3_xboole_0(B_188,u1_struct_0(A_187)),B_188),u1_struct_0(A_187))
      | r2_yellow_0(A_187,B_188)
      | ~ r2_yellow_0(A_187,k3_xboole_0(B_188,u1_struct_0(A_187)))
      | ~ l1_orders_2(A_187)
      | v2_struct_0(A_187) ) ),
    inference(resolution,[status(thm)],[c_798,c_844])).

tff(c_861,plain,(
    ! [A_189,C_190] :
      ( r2_yellow_0(A_189,C_190)
      | ~ r2_yellow_0(A_189,k3_xboole_0(C_190,u1_struct_0(A_189)))
      | ~ l1_orders_2(A_189)
      | v2_struct_0(A_189) ) ),
    inference(resolution,[status(thm)],[c_12,c_855])).

tff(c_867,plain,
    ( r2_yellow_0('#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_507,c_861])).

tff(c_871,plain,
    ( r2_yellow_0('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_867])).

tff(c_873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_66,c_871])).

tff(c_874,plain,
    ( r2_yellow_0('#skF_3','#skF_5')
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_505])).

tff(c_876,plain,(
    r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_874])).

tff(c_904,plain,(
    ! [A_194,B_195,C_196] :
      ( r2_lattice3(A_194,B_195,'#skF_1'(A_194,B_195,C_196))
      | r2_lattice3(A_194,C_196,'#skF_1'(A_194,B_195,C_196))
      | r1_yellow_0(A_194,C_196)
      | ~ r1_yellow_0(A_194,B_195)
      | ~ l1_orders_2(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1193,plain,(
    ! [A_245,B_246,C_247] :
      ( r2_lattice3(A_245,B_246,'#skF_1'(A_245,k3_xboole_0(B_246,u1_struct_0(A_245)),C_247))
      | ~ m1_subset_1('#skF_1'(A_245,k3_xboole_0(B_246,u1_struct_0(A_245)),C_247),u1_struct_0(A_245))
      | r2_lattice3(A_245,C_247,'#skF_1'(A_245,k3_xboole_0(B_246,u1_struct_0(A_245)),C_247))
      | r1_yellow_0(A_245,C_247)
      | ~ r1_yellow_0(A_245,k3_xboole_0(B_246,u1_struct_0(A_245)))
      | ~ l1_orders_2(A_245)
      | v2_struct_0(A_245) ) ),
    inference(resolution,[status(thm)],[c_904,c_26])).

tff(c_1197,plain,(
    ! [A_1,B_246,C_7] :
      ( r2_lattice3(A_1,B_246,'#skF_1'(A_1,k3_xboole_0(B_246,u1_struct_0(A_1)),C_7))
      | r2_lattice3(A_1,C_7,'#skF_1'(A_1,k3_xboole_0(B_246,u1_struct_0(A_1)),C_7))
      | r1_yellow_0(A_1,C_7)
      | ~ r1_yellow_0(A_1,k3_xboole_0(B_246,u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_1193])).

tff(c_1210,plain,(
    ! [A_1,B_246] :
      ( r1_yellow_0(A_1,B_246)
      | ~ r1_yellow_0(A_1,k3_xboole_0(B_246,u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1)
      | r2_lattice3(A_1,B_246,'#skF_1'(A_1,k3_xboole_0(B_246,u1_struct_0(A_1)),B_246)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1197])).

tff(c_1236,plain,(
    ! [A_254,B_255] :
      ( r1_yellow_0(A_254,B_255)
      | ~ r1_yellow_0(A_254,k3_xboole_0(B_255,u1_struct_0(A_254)))
      | ~ l1_orders_2(A_254)
      | v2_struct_0(A_254)
      | r2_lattice3(A_254,B_255,'#skF_1'(A_254,k3_xboole_0(B_255,u1_struct_0(A_254)),B_255)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1197])).

tff(c_4,plain,(
    ! [A_1,C_7,B_6] :
      ( ~ r2_lattice3(A_1,C_7,'#skF_1'(A_1,B_6,C_7))
      | ~ r2_lattice3(A_1,B_6,'#skF_1'(A_1,B_6,C_7))
      | r1_yellow_0(A_1,C_7)
      | ~ r1_yellow_0(A_1,B_6)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1245,plain,(
    ! [A_256,B_257] :
      ( ~ r2_lattice3(A_256,k3_xboole_0(B_257,u1_struct_0(A_256)),'#skF_1'(A_256,k3_xboole_0(B_257,u1_struct_0(A_256)),B_257))
      | r1_yellow_0(A_256,B_257)
      | ~ r1_yellow_0(A_256,k3_xboole_0(B_257,u1_struct_0(A_256)))
      | ~ l1_orders_2(A_256)
      | v2_struct_0(A_256) ) ),
    inference(resolution,[status(thm)],[c_1236,c_4])).

tff(c_1333,plain,(
    ! [A_272,B_273] :
      ( r1_yellow_0(A_272,B_273)
      | ~ r1_yellow_0(A_272,k3_xboole_0(B_273,u1_struct_0(A_272)))
      | ~ r2_lattice3(A_272,B_273,'#skF_1'(A_272,k3_xboole_0(B_273,u1_struct_0(A_272)),B_273))
      | ~ m1_subset_1('#skF_1'(A_272,k3_xboole_0(B_273,u1_struct_0(A_272)),B_273),u1_struct_0(A_272))
      | ~ l1_orders_2(A_272)
      | v2_struct_0(A_272) ) ),
    inference(resolution,[status(thm)],[c_28,c_1245])).

tff(c_1344,plain,(
    ! [A_274,B_275] :
      ( ~ m1_subset_1('#skF_1'(A_274,k3_xboole_0(B_275,u1_struct_0(A_274)),B_275),u1_struct_0(A_274))
      | r1_yellow_0(A_274,B_275)
      | ~ r1_yellow_0(A_274,k3_xboole_0(B_275,u1_struct_0(A_274)))
      | ~ l1_orders_2(A_274)
      | v2_struct_0(A_274) ) ),
    inference(resolution,[status(thm)],[c_1210,c_1333])).

tff(c_1350,plain,(
    ! [A_276,C_277] :
      ( r1_yellow_0(A_276,C_277)
      | ~ r1_yellow_0(A_276,k3_xboole_0(C_277,u1_struct_0(A_276)))
      | ~ l1_orders_2(A_276)
      | v2_struct_0(A_276) ) ),
    inference(resolution,[status(thm)],[c_2,c_1344])).

tff(c_1356,plain,
    ( r1_yellow_0('#skF_3','#skF_6')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_876,c_1350])).

tff(c_1363,plain,
    ( r1_yellow_0('#skF_3','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1356])).

tff(c_1365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_65,c_1363])).

tff(c_1366,plain,(
    r2_yellow_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_874])).

tff(c_1429,plain,(
    ! [A_287,B_288,C_289] :
      ( r1_lattice3(A_287,B_288,'#skF_2'(A_287,B_288,C_289))
      | r1_lattice3(A_287,C_289,'#skF_2'(A_287,B_288,C_289))
      | r2_yellow_0(A_287,C_289)
      | ~ r2_yellow_0(A_287,B_288)
      | ~ l1_orders_2(A_287)
      | v2_struct_0(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1484,plain,(
    ! [A_298,B_299,B_300] :
      ( r1_lattice3(A_298,B_299,'#skF_2'(A_298,B_300,k3_xboole_0(B_299,u1_struct_0(A_298))))
      | ~ m1_subset_1('#skF_2'(A_298,B_300,k3_xboole_0(B_299,u1_struct_0(A_298))),u1_struct_0(A_298))
      | r1_lattice3(A_298,B_300,'#skF_2'(A_298,B_300,k3_xboole_0(B_299,u1_struct_0(A_298))))
      | r2_yellow_0(A_298,k3_xboole_0(B_299,u1_struct_0(A_298)))
      | ~ r2_yellow_0(A_298,B_300)
      | ~ l1_orders_2(A_298)
      | v2_struct_0(A_298) ) ),
    inference(resolution,[status(thm)],[c_1429,c_22])).

tff(c_1488,plain,(
    ! [A_9,B_299,B_14] :
      ( r1_lattice3(A_9,B_299,'#skF_2'(A_9,B_14,k3_xboole_0(B_299,u1_struct_0(A_9))))
      | r1_lattice3(A_9,B_14,'#skF_2'(A_9,B_14,k3_xboole_0(B_299,u1_struct_0(A_9))))
      | r2_yellow_0(A_9,k3_xboole_0(B_299,u1_struct_0(A_9)))
      | ~ r2_yellow_0(A_9,B_14)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_1484])).

tff(c_1501,plain,(
    ! [A_9,B_299] :
      ( r2_yellow_0(A_9,k3_xboole_0(B_299,u1_struct_0(A_9)))
      | ~ r2_yellow_0(A_9,B_299)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9)
      | r1_lattice3(A_9,B_299,'#skF_2'(A_9,B_299,k3_xboole_0(B_299,u1_struct_0(A_9)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1488])).

tff(c_1407,plain,(
    ! [A_284,C_285,B_286] :
      ( ~ r1_lattice3(A_284,C_285,'#skF_2'(A_284,B_286,C_285))
      | ~ r1_lattice3(A_284,B_286,'#skF_2'(A_284,B_286,C_285))
      | r2_yellow_0(A_284,C_285)
      | ~ r2_yellow_0(A_284,B_286)
      | ~ l1_orders_2(A_284)
      | v2_struct_0(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1601,plain,(
    ! [A_322,B_323,B_324] :
      ( ~ r1_lattice3(A_322,B_323,'#skF_2'(A_322,B_323,k3_xboole_0(B_324,u1_struct_0(A_322))))
      | r2_yellow_0(A_322,k3_xboole_0(B_324,u1_struct_0(A_322)))
      | ~ r2_yellow_0(A_322,B_323)
      | ~ r1_lattice3(A_322,B_324,'#skF_2'(A_322,B_323,k3_xboole_0(B_324,u1_struct_0(A_322))))
      | ~ m1_subset_1('#skF_2'(A_322,B_323,k3_xboole_0(B_324,u1_struct_0(A_322))),u1_struct_0(A_322))
      | ~ l1_orders_2(A_322)
      | v2_struct_0(A_322) ) ),
    inference(resolution,[status(thm)],[c_24,c_1407])).

tff(c_1622,plain,(
    ! [A_325,B_326] :
      ( ~ r1_lattice3(A_325,B_326,'#skF_2'(A_325,B_326,k3_xboole_0(B_326,u1_struct_0(A_325))))
      | ~ m1_subset_1('#skF_2'(A_325,B_326,k3_xboole_0(B_326,u1_struct_0(A_325))),u1_struct_0(A_325))
      | r2_yellow_0(A_325,k3_xboole_0(B_326,u1_struct_0(A_325)))
      | ~ r2_yellow_0(A_325,B_326)
      | ~ l1_orders_2(A_325)
      | v2_struct_0(A_325) ) ),
    inference(resolution,[status(thm)],[c_1501,c_1601])).

tff(c_1633,plain,(
    ! [A_327,B_328] :
      ( ~ m1_subset_1('#skF_2'(A_327,B_328,k3_xboole_0(B_328,u1_struct_0(A_327))),u1_struct_0(A_327))
      | r2_yellow_0(A_327,k3_xboole_0(B_328,u1_struct_0(A_327)))
      | ~ r2_yellow_0(A_327,B_328)
      | ~ l1_orders_2(A_327)
      | v2_struct_0(A_327) ) ),
    inference(resolution,[status(thm)],[c_1501,c_1622])).

tff(c_1639,plain,(
    ! [A_329,B_330] :
      ( r2_yellow_0(A_329,k3_xboole_0(B_330,u1_struct_0(A_329)))
      | ~ r2_yellow_0(A_329,B_330)
      | ~ l1_orders_2(A_329)
      | v2_struct_0(A_329) ) ),
    inference(resolution,[status(thm)],[c_12,c_1633])).

tff(c_1367,plain,(
    ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_874])).

tff(c_875,plain,(
    ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_505])).

tff(c_506,plain,(
    r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_44,plain,
    ( r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3')))
    | ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3')))
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1413,plain,
    ( r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3')))
    | ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3')))
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_44])).

tff(c_1414,plain,(
    ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1367,c_875,c_1413])).

tff(c_1645,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1639,c_1414])).

tff(c_1652,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1366,c_1645])).

tff(c_1654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1652])).

tff(c_1655,plain,
    ( r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | r2_yellow_0('#skF_3','#skF_5')
    | r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2944,plain,(
    r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1655])).

tff(c_3002,plain,(
    ! [A_603,B_604,C_605] :
      ( r1_lattice3(A_603,B_604,'#skF_2'(A_603,B_604,C_605))
      | r1_lattice3(A_603,C_605,'#skF_2'(A_603,B_604,C_605))
      | r2_yellow_0(A_603,C_605)
      | ~ r2_yellow_0(A_603,B_604)
      | ~ l1_orders_2(A_603)
      | v2_struct_0(A_603) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3212,plain,(
    ! [A_651,B_652,C_653] :
      ( r1_lattice3(A_651,B_652,'#skF_2'(A_651,k3_xboole_0(B_652,u1_struct_0(A_651)),C_653))
      | ~ m1_subset_1('#skF_2'(A_651,k3_xboole_0(B_652,u1_struct_0(A_651)),C_653),u1_struct_0(A_651))
      | r1_lattice3(A_651,C_653,'#skF_2'(A_651,k3_xboole_0(B_652,u1_struct_0(A_651)),C_653))
      | r2_yellow_0(A_651,C_653)
      | ~ r2_yellow_0(A_651,k3_xboole_0(B_652,u1_struct_0(A_651)))
      | ~ l1_orders_2(A_651)
      | v2_struct_0(A_651) ) ),
    inference(resolution,[status(thm)],[c_3002,c_22])).

tff(c_3216,plain,(
    ! [A_9,B_652,C_15] :
      ( r1_lattice3(A_9,B_652,'#skF_2'(A_9,k3_xboole_0(B_652,u1_struct_0(A_9)),C_15))
      | r1_lattice3(A_9,C_15,'#skF_2'(A_9,k3_xboole_0(B_652,u1_struct_0(A_9)),C_15))
      | r2_yellow_0(A_9,C_15)
      | ~ r2_yellow_0(A_9,k3_xboole_0(B_652,u1_struct_0(A_9)))
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_3212])).

tff(c_3229,plain,(
    ! [A_9,B_652] :
      ( r2_yellow_0(A_9,B_652)
      | ~ r2_yellow_0(A_9,k3_xboole_0(B_652,u1_struct_0(A_9)))
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9)
      | r1_lattice3(A_9,B_652,'#skF_2'(A_9,k3_xboole_0(B_652,u1_struct_0(A_9)),B_652)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3216])).

tff(c_3250,plain,(
    ! [A_657,B_658] :
      ( r2_yellow_0(A_657,B_658)
      | ~ r2_yellow_0(A_657,k3_xboole_0(B_658,u1_struct_0(A_657)))
      | ~ l1_orders_2(A_657)
      | v2_struct_0(A_657)
      | r1_lattice3(A_657,B_658,'#skF_2'(A_657,k3_xboole_0(B_658,u1_struct_0(A_657)),B_658)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3216])).

tff(c_3259,plain,(
    ! [A_659,B_660] :
      ( ~ r1_lattice3(A_659,k3_xboole_0(B_660,u1_struct_0(A_659)),'#skF_2'(A_659,k3_xboole_0(B_660,u1_struct_0(A_659)),B_660))
      | r2_yellow_0(A_659,B_660)
      | ~ r2_yellow_0(A_659,k3_xboole_0(B_660,u1_struct_0(A_659)))
      | ~ l1_orders_2(A_659)
      | v2_struct_0(A_659) ) ),
    inference(resolution,[status(thm)],[c_3250,c_14])).

tff(c_3275,plain,(
    ! [A_661,B_662] :
      ( r2_yellow_0(A_661,B_662)
      | ~ r2_yellow_0(A_661,k3_xboole_0(B_662,u1_struct_0(A_661)))
      | ~ r1_lattice3(A_661,B_662,'#skF_2'(A_661,k3_xboole_0(B_662,u1_struct_0(A_661)),B_662))
      | ~ m1_subset_1('#skF_2'(A_661,k3_xboole_0(B_662,u1_struct_0(A_661)),B_662),u1_struct_0(A_661))
      | ~ l1_orders_2(A_661)
      | v2_struct_0(A_661) ) ),
    inference(resolution,[status(thm)],[c_24,c_3259])).

tff(c_3286,plain,(
    ! [A_663,B_664] :
      ( ~ m1_subset_1('#skF_2'(A_663,k3_xboole_0(B_664,u1_struct_0(A_663)),B_664),u1_struct_0(A_663))
      | r2_yellow_0(A_663,B_664)
      | ~ r2_yellow_0(A_663,k3_xboole_0(B_664,u1_struct_0(A_663)))
      | ~ l1_orders_2(A_663)
      | v2_struct_0(A_663) ) ),
    inference(resolution,[status(thm)],[c_3229,c_3275])).

tff(c_3292,plain,(
    ! [A_665,C_666] :
      ( r2_yellow_0(A_665,C_666)
      | ~ r2_yellow_0(A_665,k3_xboole_0(C_666,u1_struct_0(A_665)))
      | ~ l1_orders_2(A_665)
      | v2_struct_0(A_665) ) ),
    inference(resolution,[status(thm)],[c_12,c_3286])).

tff(c_3298,plain,
    ( r2_yellow_0('#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2944,c_3292])).

tff(c_3305,plain,
    ( r2_yellow_0('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3298])).

tff(c_3307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_66,c_3305])).

tff(c_3309,plain,(
    ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1655])).

tff(c_3308,plain,
    ( r2_yellow_0('#skF_3','#skF_5')
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1655])).

tff(c_3310,plain,(
    r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3308])).

tff(c_3349,plain,(
    ! [A_682,B_683,C_684] :
      ( r2_lattice3(A_682,B_683,'#skF_1'(A_682,B_683,C_684))
      | r2_lattice3(A_682,C_684,'#skF_1'(A_682,B_683,C_684))
      | r1_yellow_0(A_682,C_684)
      | ~ r1_yellow_0(A_682,B_683)
      | ~ l1_orders_2(A_682)
      | v2_struct_0(A_682) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3673,plain,(
    ! [A_738,B_739,C_740] :
      ( r2_lattice3(A_738,B_739,'#skF_1'(A_738,k3_xboole_0(B_739,u1_struct_0(A_738)),C_740))
      | ~ m1_subset_1('#skF_1'(A_738,k3_xboole_0(B_739,u1_struct_0(A_738)),C_740),u1_struct_0(A_738))
      | r2_lattice3(A_738,C_740,'#skF_1'(A_738,k3_xboole_0(B_739,u1_struct_0(A_738)),C_740))
      | r1_yellow_0(A_738,C_740)
      | ~ r1_yellow_0(A_738,k3_xboole_0(B_739,u1_struct_0(A_738)))
      | ~ l1_orders_2(A_738)
      | v2_struct_0(A_738) ) ),
    inference(resolution,[status(thm)],[c_3349,c_26])).

tff(c_3677,plain,(
    ! [A_1,B_739,C_7] :
      ( r2_lattice3(A_1,B_739,'#skF_1'(A_1,k3_xboole_0(B_739,u1_struct_0(A_1)),C_7))
      | r2_lattice3(A_1,C_7,'#skF_1'(A_1,k3_xboole_0(B_739,u1_struct_0(A_1)),C_7))
      | r1_yellow_0(A_1,C_7)
      | ~ r1_yellow_0(A_1,k3_xboole_0(B_739,u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_3673])).

tff(c_3690,plain,(
    ! [A_1,B_739] :
      ( r1_yellow_0(A_1,B_739)
      | ~ r1_yellow_0(A_1,k3_xboole_0(B_739,u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1)
      | r2_lattice3(A_1,B_739,'#skF_1'(A_1,k3_xboole_0(B_739,u1_struct_0(A_1)),B_739)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3677])).

tff(c_3707,plain,(
    ! [A_744,B_745] :
      ( r1_yellow_0(A_744,B_745)
      | ~ r1_yellow_0(A_744,k3_xboole_0(B_745,u1_struct_0(A_744)))
      | ~ l1_orders_2(A_744)
      | v2_struct_0(A_744)
      | r2_lattice3(A_744,B_745,'#skF_1'(A_744,k3_xboole_0(B_745,u1_struct_0(A_744)),B_745)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3677])).

tff(c_3737,plain,(
    ! [A_749,B_750] :
      ( ~ r2_lattice3(A_749,k3_xboole_0(B_750,u1_struct_0(A_749)),'#skF_1'(A_749,k3_xboole_0(B_750,u1_struct_0(A_749)),B_750))
      | r1_yellow_0(A_749,B_750)
      | ~ r1_yellow_0(A_749,k3_xboole_0(B_750,u1_struct_0(A_749)))
      | ~ l1_orders_2(A_749)
      | v2_struct_0(A_749) ) ),
    inference(resolution,[status(thm)],[c_3707,c_4])).

tff(c_3778,plain,(
    ! [A_757,B_758] :
      ( r1_yellow_0(A_757,B_758)
      | ~ r1_yellow_0(A_757,k3_xboole_0(B_758,u1_struct_0(A_757)))
      | ~ r2_lattice3(A_757,B_758,'#skF_1'(A_757,k3_xboole_0(B_758,u1_struct_0(A_757)),B_758))
      | ~ m1_subset_1('#skF_1'(A_757,k3_xboole_0(B_758,u1_struct_0(A_757)),B_758),u1_struct_0(A_757))
      | ~ l1_orders_2(A_757)
      | v2_struct_0(A_757) ) ),
    inference(resolution,[status(thm)],[c_28,c_3737])).

tff(c_3789,plain,(
    ! [A_759,B_760] :
      ( ~ m1_subset_1('#skF_1'(A_759,k3_xboole_0(B_760,u1_struct_0(A_759)),B_760),u1_struct_0(A_759))
      | r1_yellow_0(A_759,B_760)
      | ~ r1_yellow_0(A_759,k3_xboole_0(B_760,u1_struct_0(A_759)))
      | ~ l1_orders_2(A_759)
      | v2_struct_0(A_759) ) ),
    inference(resolution,[status(thm)],[c_3690,c_3778])).

tff(c_3795,plain,(
    ! [A_761,C_762] :
      ( r1_yellow_0(A_761,C_762)
      | ~ r1_yellow_0(A_761,k3_xboole_0(C_762,u1_struct_0(A_761)))
      | ~ l1_orders_2(A_761)
      | v2_struct_0(A_761) ) ),
    inference(resolution,[status(thm)],[c_2,c_3789])).

tff(c_3801,plain,
    ( r1_yellow_0('#skF_3','#skF_6')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3310,c_3795])).

tff(c_3805,plain,
    ( r1_yellow_0('#skF_3','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3801])).

tff(c_3807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_65,c_3805])).

tff(c_3809,plain,(
    ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_3308])).

tff(c_1656,plain,(
    ~ r1_yellow_0('#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1658,plain,(
    r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1655])).

tff(c_1698,plain,(
    ! [A_349,B_350,C_351] :
      ( r1_lattice3(A_349,B_350,'#skF_2'(A_349,B_350,C_351))
      | r1_lattice3(A_349,C_351,'#skF_2'(A_349,B_350,C_351))
      | r2_yellow_0(A_349,C_351)
      | ~ r2_yellow_0(A_349,B_350)
      | ~ l1_orders_2(A_349)
      | v2_struct_0(A_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2052,plain,(
    ! [A_411,B_412,C_413] :
      ( r1_lattice3(A_411,B_412,'#skF_2'(A_411,k3_xboole_0(B_412,u1_struct_0(A_411)),C_413))
      | ~ m1_subset_1('#skF_2'(A_411,k3_xboole_0(B_412,u1_struct_0(A_411)),C_413),u1_struct_0(A_411))
      | r1_lattice3(A_411,C_413,'#skF_2'(A_411,k3_xboole_0(B_412,u1_struct_0(A_411)),C_413))
      | r2_yellow_0(A_411,C_413)
      | ~ r2_yellow_0(A_411,k3_xboole_0(B_412,u1_struct_0(A_411)))
      | ~ l1_orders_2(A_411)
      | v2_struct_0(A_411) ) ),
    inference(resolution,[status(thm)],[c_1698,c_22])).

tff(c_2056,plain,(
    ! [A_9,B_412,C_15] :
      ( r1_lattice3(A_9,B_412,'#skF_2'(A_9,k3_xboole_0(B_412,u1_struct_0(A_9)),C_15))
      | r1_lattice3(A_9,C_15,'#skF_2'(A_9,k3_xboole_0(B_412,u1_struct_0(A_9)),C_15))
      | r2_yellow_0(A_9,C_15)
      | ~ r2_yellow_0(A_9,k3_xboole_0(B_412,u1_struct_0(A_9)))
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_2052])).

tff(c_2069,plain,(
    ! [A_9,B_412] :
      ( r2_yellow_0(A_9,B_412)
      | ~ r2_yellow_0(A_9,k3_xboole_0(B_412,u1_struct_0(A_9)))
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9)
      | r1_lattice3(A_9,B_412,'#skF_2'(A_9,k3_xboole_0(B_412,u1_struct_0(A_9)),B_412)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2056])).

tff(c_2090,plain,(
    ! [A_417,B_418] :
      ( r2_yellow_0(A_417,B_418)
      | ~ r2_yellow_0(A_417,k3_xboole_0(B_418,u1_struct_0(A_417)))
      | ~ l1_orders_2(A_417)
      | v2_struct_0(A_417)
      | r1_lattice3(A_417,B_418,'#skF_2'(A_417,k3_xboole_0(B_418,u1_struct_0(A_417)),B_418)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2056])).

tff(c_2099,plain,(
    ! [A_419,B_420] :
      ( ~ r1_lattice3(A_419,k3_xboole_0(B_420,u1_struct_0(A_419)),'#skF_2'(A_419,k3_xboole_0(B_420,u1_struct_0(A_419)),B_420))
      | r2_yellow_0(A_419,B_420)
      | ~ r2_yellow_0(A_419,k3_xboole_0(B_420,u1_struct_0(A_419)))
      | ~ l1_orders_2(A_419)
      | v2_struct_0(A_419) ) ),
    inference(resolution,[status(thm)],[c_2090,c_14])).

tff(c_2115,plain,(
    ! [A_421,B_422] :
      ( r2_yellow_0(A_421,B_422)
      | ~ r2_yellow_0(A_421,k3_xboole_0(B_422,u1_struct_0(A_421)))
      | ~ r1_lattice3(A_421,B_422,'#skF_2'(A_421,k3_xboole_0(B_422,u1_struct_0(A_421)),B_422))
      | ~ m1_subset_1('#skF_2'(A_421,k3_xboole_0(B_422,u1_struct_0(A_421)),B_422),u1_struct_0(A_421))
      | ~ l1_orders_2(A_421)
      | v2_struct_0(A_421) ) ),
    inference(resolution,[status(thm)],[c_24,c_2099])).

tff(c_2126,plain,(
    ! [A_423,B_424] :
      ( ~ m1_subset_1('#skF_2'(A_423,k3_xboole_0(B_424,u1_struct_0(A_423)),B_424),u1_struct_0(A_423))
      | r2_yellow_0(A_423,B_424)
      | ~ r2_yellow_0(A_423,k3_xboole_0(B_424,u1_struct_0(A_423)))
      | ~ l1_orders_2(A_423)
      | v2_struct_0(A_423) ) ),
    inference(resolution,[status(thm)],[c_2069,c_2115])).

tff(c_2132,plain,(
    ! [A_425,C_426] :
      ( r2_yellow_0(A_425,C_426)
      | ~ r2_yellow_0(A_425,k3_xboole_0(C_426,u1_struct_0(A_425)))
      | ~ l1_orders_2(A_425)
      | v2_struct_0(A_425) ) ),
    inference(resolution,[status(thm)],[c_12,c_2126])).

tff(c_2138,plain,
    ( r2_yellow_0('#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1658,c_2132])).

tff(c_2142,plain,
    ( r2_yellow_0('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2138])).

tff(c_2144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_66,c_2142])).

tff(c_2145,plain,
    ( r2_yellow_0('#skF_3','#skF_5')
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1655])).

tff(c_2147,plain,(
    r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2145])).

tff(c_2190,plain,(
    ! [A_445,B_446,C_447] :
      ( r2_lattice3(A_445,B_446,'#skF_1'(A_445,B_446,C_447))
      | r2_lattice3(A_445,C_447,'#skF_1'(A_445,B_446,C_447))
      | r1_yellow_0(A_445,C_447)
      | ~ r1_yellow_0(A_445,B_446)
      | ~ l1_orders_2(A_445)
      | v2_struct_0(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2545,plain,(
    ! [A_505,B_506,C_507] :
      ( r2_lattice3(A_505,B_506,'#skF_1'(A_505,k3_xboole_0(B_506,u1_struct_0(A_505)),C_507))
      | ~ m1_subset_1('#skF_1'(A_505,k3_xboole_0(B_506,u1_struct_0(A_505)),C_507),u1_struct_0(A_505))
      | r2_lattice3(A_505,C_507,'#skF_1'(A_505,k3_xboole_0(B_506,u1_struct_0(A_505)),C_507))
      | r1_yellow_0(A_505,C_507)
      | ~ r1_yellow_0(A_505,k3_xboole_0(B_506,u1_struct_0(A_505)))
      | ~ l1_orders_2(A_505)
      | v2_struct_0(A_505) ) ),
    inference(resolution,[status(thm)],[c_2190,c_26])).

tff(c_2549,plain,(
    ! [A_1,B_506,C_7] :
      ( r2_lattice3(A_1,B_506,'#skF_1'(A_1,k3_xboole_0(B_506,u1_struct_0(A_1)),C_7))
      | r2_lattice3(A_1,C_7,'#skF_1'(A_1,k3_xboole_0(B_506,u1_struct_0(A_1)),C_7))
      | r1_yellow_0(A_1,C_7)
      | ~ r1_yellow_0(A_1,k3_xboole_0(B_506,u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_2545])).

tff(c_2563,plain,(
    ! [A_1,B_506] :
      ( r1_yellow_0(A_1,B_506)
      | ~ r1_yellow_0(A_1,k3_xboole_0(B_506,u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1)
      | r2_lattice3(A_1,B_506,'#skF_1'(A_1,k3_xboole_0(B_506,u1_struct_0(A_1)),B_506)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2549])).

tff(c_2584,plain,(
    ! [A_513,B_514] :
      ( r1_yellow_0(A_513,B_514)
      | ~ r1_yellow_0(A_513,k3_xboole_0(B_514,u1_struct_0(A_513)))
      | ~ l1_orders_2(A_513)
      | v2_struct_0(A_513)
      | r2_lattice3(A_513,B_514,'#skF_1'(A_513,k3_xboole_0(B_514,u1_struct_0(A_513)),B_514)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2549])).

tff(c_2593,plain,(
    ! [A_515,B_516] :
      ( ~ r2_lattice3(A_515,k3_xboole_0(B_516,u1_struct_0(A_515)),'#skF_1'(A_515,k3_xboole_0(B_516,u1_struct_0(A_515)),B_516))
      | r1_yellow_0(A_515,B_516)
      | ~ r1_yellow_0(A_515,k3_xboole_0(B_516,u1_struct_0(A_515)))
      | ~ l1_orders_2(A_515)
      | v2_struct_0(A_515) ) ),
    inference(resolution,[status(thm)],[c_2584,c_4])).

tff(c_2609,plain,(
    ! [A_517,B_518] :
      ( r1_yellow_0(A_517,B_518)
      | ~ r1_yellow_0(A_517,k3_xboole_0(B_518,u1_struct_0(A_517)))
      | ~ r2_lattice3(A_517,B_518,'#skF_1'(A_517,k3_xboole_0(B_518,u1_struct_0(A_517)),B_518))
      | ~ m1_subset_1('#skF_1'(A_517,k3_xboole_0(B_518,u1_struct_0(A_517)),B_518),u1_struct_0(A_517))
      | ~ l1_orders_2(A_517)
      | v2_struct_0(A_517) ) ),
    inference(resolution,[status(thm)],[c_28,c_2593])).

tff(c_2620,plain,(
    ! [A_519,B_520] :
      ( ~ m1_subset_1('#skF_1'(A_519,k3_xboole_0(B_520,u1_struct_0(A_519)),B_520),u1_struct_0(A_519))
      | r1_yellow_0(A_519,B_520)
      | ~ r1_yellow_0(A_519,k3_xboole_0(B_520,u1_struct_0(A_519)))
      | ~ l1_orders_2(A_519)
      | v2_struct_0(A_519) ) ),
    inference(resolution,[status(thm)],[c_2563,c_2609])).

tff(c_2626,plain,(
    ! [A_521,C_522] :
      ( r1_yellow_0(A_521,C_522)
      | ~ r1_yellow_0(A_521,k3_xboole_0(C_522,u1_struct_0(A_521)))
      | ~ l1_orders_2(A_521)
      | v2_struct_0(A_521) ) ),
    inference(resolution,[status(thm)],[c_2,c_2620])).

tff(c_2632,plain,
    ( r1_yellow_0('#skF_3','#skF_6')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2147,c_2626])).

tff(c_2636,plain,
    ( r1_yellow_0('#skF_3','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2632])).

tff(c_2638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_65,c_2636])).

tff(c_2639,plain,(
    r2_yellow_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2145])).

tff(c_2711,plain,(
    ! [A_544,B_545,C_546] :
      ( r1_lattice3(A_544,B_545,'#skF_2'(A_544,B_545,C_546))
      | r1_lattice3(A_544,C_546,'#skF_2'(A_544,B_545,C_546))
      | r2_yellow_0(A_544,C_546)
      | ~ r2_yellow_0(A_544,B_545)
      | ~ l1_orders_2(A_544)
      | v2_struct_0(A_544) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2766,plain,(
    ! [A_555,B_556,B_557] :
      ( r1_lattice3(A_555,B_556,'#skF_2'(A_555,B_557,k3_xboole_0(B_556,u1_struct_0(A_555))))
      | ~ m1_subset_1('#skF_2'(A_555,B_557,k3_xboole_0(B_556,u1_struct_0(A_555))),u1_struct_0(A_555))
      | r1_lattice3(A_555,B_557,'#skF_2'(A_555,B_557,k3_xboole_0(B_556,u1_struct_0(A_555))))
      | r2_yellow_0(A_555,k3_xboole_0(B_556,u1_struct_0(A_555)))
      | ~ r2_yellow_0(A_555,B_557)
      | ~ l1_orders_2(A_555)
      | v2_struct_0(A_555) ) ),
    inference(resolution,[status(thm)],[c_2711,c_22])).

tff(c_2770,plain,(
    ! [A_9,B_556,B_14] :
      ( r1_lattice3(A_9,B_556,'#skF_2'(A_9,B_14,k3_xboole_0(B_556,u1_struct_0(A_9))))
      | r1_lattice3(A_9,B_14,'#skF_2'(A_9,B_14,k3_xboole_0(B_556,u1_struct_0(A_9))))
      | r2_yellow_0(A_9,k3_xboole_0(B_556,u1_struct_0(A_9)))
      | ~ r2_yellow_0(A_9,B_14)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_2766])).

tff(c_2783,plain,(
    ! [A_9,B_556] :
      ( r2_yellow_0(A_9,k3_xboole_0(B_556,u1_struct_0(A_9)))
      | ~ r2_yellow_0(A_9,B_556)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9)
      | r1_lattice3(A_9,B_556,'#skF_2'(A_9,B_556,k3_xboole_0(B_556,u1_struct_0(A_9)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2770])).

tff(c_2658,plain,(
    ! [A_535,C_536,B_537] :
      ( ~ r1_lattice3(A_535,C_536,'#skF_2'(A_535,B_537,C_536))
      | ~ r1_lattice3(A_535,B_537,'#skF_2'(A_535,B_537,C_536))
      | r2_yellow_0(A_535,C_536)
      | ~ r2_yellow_0(A_535,B_537)
      | ~ l1_orders_2(A_535)
      | v2_struct_0(A_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2883,plain,(
    ! [A_579,B_580,B_581] :
      ( ~ r1_lattice3(A_579,B_580,'#skF_2'(A_579,B_580,k3_xboole_0(B_581,u1_struct_0(A_579))))
      | r2_yellow_0(A_579,k3_xboole_0(B_581,u1_struct_0(A_579)))
      | ~ r2_yellow_0(A_579,B_580)
      | ~ r1_lattice3(A_579,B_581,'#skF_2'(A_579,B_580,k3_xboole_0(B_581,u1_struct_0(A_579))))
      | ~ m1_subset_1('#skF_2'(A_579,B_580,k3_xboole_0(B_581,u1_struct_0(A_579))),u1_struct_0(A_579))
      | ~ l1_orders_2(A_579)
      | v2_struct_0(A_579) ) ),
    inference(resolution,[status(thm)],[c_24,c_2658])).

tff(c_2904,plain,(
    ! [A_582,B_583] :
      ( ~ r1_lattice3(A_582,B_583,'#skF_2'(A_582,B_583,k3_xboole_0(B_583,u1_struct_0(A_582))))
      | ~ m1_subset_1('#skF_2'(A_582,B_583,k3_xboole_0(B_583,u1_struct_0(A_582))),u1_struct_0(A_582))
      | r2_yellow_0(A_582,k3_xboole_0(B_583,u1_struct_0(A_582)))
      | ~ r2_yellow_0(A_582,B_583)
      | ~ l1_orders_2(A_582)
      | v2_struct_0(A_582) ) ),
    inference(resolution,[status(thm)],[c_2783,c_2883])).

tff(c_2915,plain,(
    ! [A_584,B_585] :
      ( ~ m1_subset_1('#skF_2'(A_584,B_585,k3_xboole_0(B_585,u1_struct_0(A_584))),u1_struct_0(A_584))
      | r2_yellow_0(A_584,k3_xboole_0(B_585,u1_struct_0(A_584)))
      | ~ r2_yellow_0(A_584,B_585)
      | ~ l1_orders_2(A_584)
      | v2_struct_0(A_584) ) ),
    inference(resolution,[status(thm)],[c_2783,c_2904])).

tff(c_2921,plain,(
    ! [A_586,B_587] :
      ( r2_yellow_0(A_586,k3_xboole_0(B_587,u1_struct_0(A_586)))
      | ~ r2_yellow_0(A_586,B_587)
      | ~ l1_orders_2(A_586)
      | v2_struct_0(A_586) ) ),
    inference(resolution,[status(thm)],[c_12,c_2915])).

tff(c_60,plain,
    ( r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3')))
    | ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3')))
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | r1_yellow_0('#skF_3','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1657,plain,(
    ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_2930,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2921,c_1657])).

tff(c_2938,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2639,c_2930])).

tff(c_2940,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2938])).

tff(c_2941,plain,
    ( r1_yellow_0('#skF_3','#skF_7')
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_3810,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3309,c_3809,c_1656,c_2941])).

tff(c_3811,plain,
    ( r1_yellow_0('#skF_3','#skF_7')
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | r2_yellow_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_3813,plain,(
    r2_yellow_0('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3811])).

tff(c_3893,plain,(
    ! [A_790,B_791,C_792] :
      ( r1_lattice3(A_790,B_791,'#skF_2'(A_790,B_791,C_792))
      | r1_lattice3(A_790,C_792,'#skF_2'(A_790,B_791,C_792))
      | r2_yellow_0(A_790,C_792)
      | ~ r2_yellow_0(A_790,B_791)
      | ~ l1_orders_2(A_790)
      | v2_struct_0(A_790) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3918,plain,(
    ! [A_796,B_797,B_798] :
      ( r1_lattice3(A_796,B_797,'#skF_2'(A_796,B_798,k3_xboole_0(B_797,u1_struct_0(A_796))))
      | ~ m1_subset_1('#skF_2'(A_796,B_798,k3_xboole_0(B_797,u1_struct_0(A_796))),u1_struct_0(A_796))
      | r1_lattice3(A_796,B_798,'#skF_2'(A_796,B_798,k3_xboole_0(B_797,u1_struct_0(A_796))))
      | r2_yellow_0(A_796,k3_xboole_0(B_797,u1_struct_0(A_796)))
      | ~ r2_yellow_0(A_796,B_798)
      | ~ l1_orders_2(A_796)
      | v2_struct_0(A_796) ) ),
    inference(resolution,[status(thm)],[c_3893,c_22])).

tff(c_3922,plain,(
    ! [A_9,B_797,B_14] :
      ( r1_lattice3(A_9,B_797,'#skF_2'(A_9,B_14,k3_xboole_0(B_797,u1_struct_0(A_9))))
      | r1_lattice3(A_9,B_14,'#skF_2'(A_9,B_14,k3_xboole_0(B_797,u1_struct_0(A_9))))
      | r2_yellow_0(A_9,k3_xboole_0(B_797,u1_struct_0(A_9)))
      | ~ r2_yellow_0(A_9,B_14)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_3918])).

tff(c_3935,plain,(
    ! [A_9,B_797] :
      ( r2_yellow_0(A_9,k3_xboole_0(B_797,u1_struct_0(A_9)))
      | ~ r2_yellow_0(A_9,B_797)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9)
      | r1_lattice3(A_9,B_797,'#skF_2'(A_9,B_797,k3_xboole_0(B_797,u1_struct_0(A_9)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3922])).

tff(c_3865,plain,(
    ! [A_784,C_785,B_786] :
      ( ~ r1_lattice3(A_784,C_785,'#skF_2'(A_784,B_786,C_785))
      | ~ r1_lattice3(A_784,B_786,'#skF_2'(A_784,B_786,C_785))
      | r2_yellow_0(A_784,C_785)
      | ~ r2_yellow_0(A_784,B_786)
      | ~ l1_orders_2(A_784)
      | v2_struct_0(A_784) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4218,plain,(
    ! [A_850,B_851,B_852] :
      ( ~ r1_lattice3(A_850,B_851,'#skF_2'(A_850,B_851,k3_xboole_0(B_852,u1_struct_0(A_850))))
      | r2_yellow_0(A_850,k3_xboole_0(B_852,u1_struct_0(A_850)))
      | ~ r2_yellow_0(A_850,B_851)
      | ~ r1_lattice3(A_850,B_852,'#skF_2'(A_850,B_851,k3_xboole_0(B_852,u1_struct_0(A_850))))
      | ~ m1_subset_1('#skF_2'(A_850,B_851,k3_xboole_0(B_852,u1_struct_0(A_850))),u1_struct_0(A_850))
      | ~ l1_orders_2(A_850)
      | v2_struct_0(A_850) ) ),
    inference(resolution,[status(thm)],[c_24,c_3865])).

tff(c_4261,plain,(
    ! [A_859,B_860] :
      ( ~ r1_lattice3(A_859,B_860,'#skF_2'(A_859,B_860,k3_xboole_0(B_860,u1_struct_0(A_859))))
      | ~ m1_subset_1('#skF_2'(A_859,B_860,k3_xboole_0(B_860,u1_struct_0(A_859))),u1_struct_0(A_859))
      | r2_yellow_0(A_859,k3_xboole_0(B_860,u1_struct_0(A_859)))
      | ~ r2_yellow_0(A_859,B_860)
      | ~ l1_orders_2(A_859)
      | v2_struct_0(A_859) ) ),
    inference(resolution,[status(thm)],[c_3935,c_4218])).

tff(c_4272,plain,(
    ! [A_861,B_862] :
      ( ~ m1_subset_1('#skF_2'(A_861,B_862,k3_xboole_0(B_862,u1_struct_0(A_861))),u1_struct_0(A_861))
      | r2_yellow_0(A_861,k3_xboole_0(B_862,u1_struct_0(A_861)))
      | ~ r2_yellow_0(A_861,B_862)
      | ~ l1_orders_2(A_861)
      | v2_struct_0(A_861) ) ),
    inference(resolution,[status(thm)],[c_3935,c_4261])).

tff(c_4294,plain,(
    ! [A_866,B_867] :
      ( r2_yellow_0(A_866,k3_xboole_0(B_867,u1_struct_0(A_866)))
      | ~ r2_yellow_0(A_866,B_867)
      | ~ l1_orders_2(A_866)
      | v2_struct_0(A_866) ) ),
    inference(resolution,[status(thm)],[c_12,c_4272])).

tff(c_3812,plain,(
    r2_yellow_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_58,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_4')
    | ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3')))
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | r1_yellow_0('#skF_3','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3815,plain,
    ( ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3')))
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | r1_yellow_0('#skF_3','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3812,c_58])).

tff(c_3816,plain,(
    ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_3815])).

tff(c_4300,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4294,c_3816])).

tff(c_4304,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3813,c_4300])).

tff(c_4306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_4304])).

tff(c_4307,plain,
    ( r1_yellow_0('#skF_3','#skF_7')
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_3815])).

tff(c_4309,plain,(
    r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_4307])).

tff(c_4394,plain,(
    ! [A_895,B_896,C_897] :
      ( r2_lattice3(A_895,B_896,'#skF_1'(A_895,B_896,C_897))
      | r2_lattice3(A_895,C_897,'#skF_1'(A_895,B_896,C_897))
      | r1_yellow_0(A_895,C_897)
      | ~ r1_yellow_0(A_895,B_896)
      | ~ l1_orders_2(A_895)
      | v2_struct_0(A_895) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4675,plain,(
    ! [A_949,B_950,C_951] :
      ( r2_lattice3(A_949,B_950,'#skF_1'(A_949,k3_xboole_0(B_950,u1_struct_0(A_949)),C_951))
      | ~ m1_subset_1('#skF_1'(A_949,k3_xboole_0(B_950,u1_struct_0(A_949)),C_951),u1_struct_0(A_949))
      | r2_lattice3(A_949,C_951,'#skF_1'(A_949,k3_xboole_0(B_950,u1_struct_0(A_949)),C_951))
      | r1_yellow_0(A_949,C_951)
      | ~ r1_yellow_0(A_949,k3_xboole_0(B_950,u1_struct_0(A_949)))
      | ~ l1_orders_2(A_949)
      | v2_struct_0(A_949) ) ),
    inference(resolution,[status(thm)],[c_4394,c_26])).

tff(c_4679,plain,(
    ! [A_1,B_950,C_7] :
      ( r2_lattice3(A_1,B_950,'#skF_1'(A_1,k3_xboole_0(B_950,u1_struct_0(A_1)),C_7))
      | r2_lattice3(A_1,C_7,'#skF_1'(A_1,k3_xboole_0(B_950,u1_struct_0(A_1)),C_7))
      | r1_yellow_0(A_1,C_7)
      | ~ r1_yellow_0(A_1,k3_xboole_0(B_950,u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_4675])).

tff(c_4693,plain,(
    ! [A_1,B_950] :
      ( r1_yellow_0(A_1,B_950)
      | ~ r1_yellow_0(A_1,k3_xboole_0(B_950,u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1)
      | r2_lattice3(A_1,B_950,'#skF_1'(A_1,k3_xboole_0(B_950,u1_struct_0(A_1)),B_950)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_4679])).

tff(c_4714,plain,(
    ! [A_957,B_958] :
      ( r1_yellow_0(A_957,B_958)
      | ~ r1_yellow_0(A_957,k3_xboole_0(B_958,u1_struct_0(A_957)))
      | ~ l1_orders_2(A_957)
      | v2_struct_0(A_957)
      | r2_lattice3(A_957,B_958,'#skF_1'(A_957,k3_xboole_0(B_958,u1_struct_0(A_957)),B_958)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_4679])).

tff(c_4723,plain,(
    ! [A_959,B_960] :
      ( ~ r2_lattice3(A_959,k3_xboole_0(B_960,u1_struct_0(A_959)),'#skF_1'(A_959,k3_xboole_0(B_960,u1_struct_0(A_959)),B_960))
      | r1_yellow_0(A_959,B_960)
      | ~ r1_yellow_0(A_959,k3_xboole_0(B_960,u1_struct_0(A_959)))
      | ~ l1_orders_2(A_959)
      | v2_struct_0(A_959) ) ),
    inference(resolution,[status(thm)],[c_4714,c_4])).

tff(c_4739,plain,(
    ! [A_961,B_962] :
      ( r1_yellow_0(A_961,B_962)
      | ~ r1_yellow_0(A_961,k3_xboole_0(B_962,u1_struct_0(A_961)))
      | ~ r2_lattice3(A_961,B_962,'#skF_1'(A_961,k3_xboole_0(B_962,u1_struct_0(A_961)),B_962))
      | ~ m1_subset_1('#skF_1'(A_961,k3_xboole_0(B_962,u1_struct_0(A_961)),B_962),u1_struct_0(A_961))
      | ~ l1_orders_2(A_961)
      | v2_struct_0(A_961) ) ),
    inference(resolution,[status(thm)],[c_28,c_4723])).

tff(c_4750,plain,(
    ! [A_963,B_964] :
      ( ~ m1_subset_1('#skF_1'(A_963,k3_xboole_0(B_964,u1_struct_0(A_963)),B_964),u1_struct_0(A_963))
      | r1_yellow_0(A_963,B_964)
      | ~ r1_yellow_0(A_963,k3_xboole_0(B_964,u1_struct_0(A_963)))
      | ~ l1_orders_2(A_963)
      | v2_struct_0(A_963) ) ),
    inference(resolution,[status(thm)],[c_4693,c_4739])).

tff(c_4756,plain,(
    ! [A_965,C_966] :
      ( r1_yellow_0(A_965,C_966)
      | ~ r1_yellow_0(A_965,k3_xboole_0(C_966,u1_struct_0(A_965)))
      | ~ l1_orders_2(A_965)
      | v2_struct_0(A_965) ) ),
    inference(resolution,[status(thm)],[c_2,c_4750])).

tff(c_4762,plain,
    ( r1_yellow_0('#skF_3','#skF_6')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4309,c_4756])).

tff(c_4766,plain,
    ( r1_yellow_0('#skF_3','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4762])).

tff(c_4768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_65,c_4766])).

tff(c_4769,plain,(
    r1_yellow_0('#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_4307])).

tff(c_4824,plain,(
    ! [A_988,B_989,C_990] :
      ( r2_lattice3(A_988,B_989,'#skF_1'(A_988,B_989,C_990))
      | r2_lattice3(A_988,C_990,'#skF_1'(A_988,B_989,C_990))
      | r1_yellow_0(A_988,C_990)
      | ~ r1_yellow_0(A_988,B_989)
      | ~ l1_orders_2(A_988)
      | v2_struct_0(A_988) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4876,plain,(
    ! [A_997,B_998,B_999] :
      ( r2_lattice3(A_997,B_998,'#skF_1'(A_997,B_999,k3_xboole_0(B_998,u1_struct_0(A_997))))
      | ~ m1_subset_1('#skF_1'(A_997,B_999,k3_xboole_0(B_998,u1_struct_0(A_997))),u1_struct_0(A_997))
      | r2_lattice3(A_997,B_999,'#skF_1'(A_997,B_999,k3_xboole_0(B_998,u1_struct_0(A_997))))
      | r1_yellow_0(A_997,k3_xboole_0(B_998,u1_struct_0(A_997)))
      | ~ r1_yellow_0(A_997,B_999)
      | ~ l1_orders_2(A_997)
      | v2_struct_0(A_997) ) ),
    inference(resolution,[status(thm)],[c_4824,c_26])).

tff(c_4880,plain,(
    ! [A_1,B_998,B_6] :
      ( r2_lattice3(A_1,B_998,'#skF_1'(A_1,B_6,k3_xboole_0(B_998,u1_struct_0(A_1))))
      | r2_lattice3(A_1,B_6,'#skF_1'(A_1,B_6,k3_xboole_0(B_998,u1_struct_0(A_1))))
      | r1_yellow_0(A_1,k3_xboole_0(B_998,u1_struct_0(A_1)))
      | ~ r1_yellow_0(A_1,B_6)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_4876])).

tff(c_4893,plain,(
    ! [A_1,B_998] :
      ( r1_yellow_0(A_1,k3_xboole_0(B_998,u1_struct_0(A_1)))
      | ~ r1_yellow_0(A_1,B_998)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1)
      | r2_lattice3(A_1,B_998,'#skF_1'(A_1,B_998,k3_xboole_0(B_998,u1_struct_0(A_1)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_4880])).

tff(c_4805,plain,(
    ! [A_985,C_986,B_987] :
      ( ~ r2_lattice3(A_985,C_986,'#skF_1'(A_985,B_987,C_986))
      | ~ r2_lattice3(A_985,B_987,'#skF_1'(A_985,B_987,C_986))
      | r1_yellow_0(A_985,C_986)
      | ~ r1_yellow_0(A_985,B_987)
      | ~ l1_orders_2(A_985)
      | v2_struct_0(A_985) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5233,plain,(
    ! [A_1059,B_1060,B_1061] :
      ( ~ r2_lattice3(A_1059,B_1060,'#skF_1'(A_1059,B_1060,k3_xboole_0(B_1061,u1_struct_0(A_1059))))
      | r1_yellow_0(A_1059,k3_xboole_0(B_1061,u1_struct_0(A_1059)))
      | ~ r1_yellow_0(A_1059,B_1060)
      | ~ r2_lattice3(A_1059,B_1061,'#skF_1'(A_1059,B_1060,k3_xboole_0(B_1061,u1_struct_0(A_1059))))
      | ~ m1_subset_1('#skF_1'(A_1059,B_1060,k3_xboole_0(B_1061,u1_struct_0(A_1059))),u1_struct_0(A_1059))
      | ~ l1_orders_2(A_1059)
      | v2_struct_0(A_1059) ) ),
    inference(resolution,[status(thm)],[c_28,c_4805])).

tff(c_5280,plain,(
    ! [A_1068,B_1069] :
      ( ~ r2_lattice3(A_1068,B_1069,'#skF_1'(A_1068,B_1069,k3_xboole_0(B_1069,u1_struct_0(A_1068))))
      | ~ m1_subset_1('#skF_1'(A_1068,B_1069,k3_xboole_0(B_1069,u1_struct_0(A_1068))),u1_struct_0(A_1068))
      | r1_yellow_0(A_1068,k3_xboole_0(B_1069,u1_struct_0(A_1068)))
      | ~ r1_yellow_0(A_1068,B_1069)
      | ~ l1_orders_2(A_1068)
      | v2_struct_0(A_1068) ) ),
    inference(resolution,[status(thm)],[c_4893,c_5233])).

tff(c_5295,plain,(
    ! [A_1070,B_1071] :
      ( ~ m1_subset_1('#skF_1'(A_1070,B_1071,k3_xboole_0(B_1071,u1_struct_0(A_1070))),u1_struct_0(A_1070))
      | r1_yellow_0(A_1070,k3_xboole_0(B_1071,u1_struct_0(A_1070)))
      | ~ r1_yellow_0(A_1070,B_1071)
      | ~ l1_orders_2(A_1070)
      | v2_struct_0(A_1070) ) ),
    inference(resolution,[status(thm)],[c_4893,c_5280])).

tff(c_5301,plain,(
    ! [A_1072,B_1073] :
      ( r1_yellow_0(A_1072,k3_xboole_0(B_1073,u1_struct_0(A_1072)))
      | ~ r1_yellow_0(A_1072,B_1073)
      | ~ l1_orders_2(A_1072)
      | v2_struct_0(A_1072) ) ),
    inference(resolution,[status(thm)],[c_2,c_5295])).

tff(c_4770,plain,(
    ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_4307])).

tff(c_4308,plain,(
    r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_3815])).

tff(c_42,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_4')
    | ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3')))
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_4796,plain,
    ( r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4308,c_3812,c_42])).

tff(c_4797,plain,(
    ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_4770,c_4796])).

tff(c_5307,plain,
    ( ~ r1_yellow_0('#skF_3','#skF_7')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5301,c_4797])).

tff(c_5314,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_4769,c_5307])).

tff(c_5316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_5314])).

tff(c_5317,plain,
    ( r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | r1_yellow_0('#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_3811])).

tff(c_5319,plain,(
    r1_yellow_0('#skF_3','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_5317])).

tff(c_5364,plain,(
    ! [A_1092,B_1093,C_1094] :
      ( r2_lattice3(A_1092,B_1093,'#skF_1'(A_1092,B_1093,C_1094))
      | r2_lattice3(A_1092,C_1094,'#skF_1'(A_1092,B_1093,C_1094))
      | r1_yellow_0(A_1092,C_1094)
      | ~ r1_yellow_0(A_1092,B_1093)
      | ~ l1_orders_2(A_1092)
      | v2_struct_0(A_1092) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5502,plain,(
    ! [A_1121,B_1122,B_1123] :
      ( r2_lattice3(A_1121,B_1122,'#skF_1'(A_1121,B_1123,k3_xboole_0(B_1122,u1_struct_0(A_1121))))
      | ~ m1_subset_1('#skF_1'(A_1121,B_1123,k3_xboole_0(B_1122,u1_struct_0(A_1121))),u1_struct_0(A_1121))
      | r2_lattice3(A_1121,B_1123,'#skF_1'(A_1121,B_1123,k3_xboole_0(B_1122,u1_struct_0(A_1121))))
      | r1_yellow_0(A_1121,k3_xboole_0(B_1122,u1_struct_0(A_1121)))
      | ~ r1_yellow_0(A_1121,B_1123)
      | ~ l1_orders_2(A_1121)
      | v2_struct_0(A_1121) ) ),
    inference(resolution,[status(thm)],[c_5364,c_26])).

tff(c_5506,plain,(
    ! [A_1,B_1122,B_6] :
      ( r2_lattice3(A_1,B_1122,'#skF_1'(A_1,B_6,k3_xboole_0(B_1122,u1_struct_0(A_1))))
      | r2_lattice3(A_1,B_6,'#skF_1'(A_1,B_6,k3_xboole_0(B_1122,u1_struct_0(A_1))))
      | r1_yellow_0(A_1,k3_xboole_0(B_1122,u1_struct_0(A_1)))
      | ~ r1_yellow_0(A_1,B_6)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_5502])).

tff(c_5544,plain,(
    ! [A_1,B_1122] :
      ( r1_yellow_0(A_1,k3_xboole_0(B_1122,u1_struct_0(A_1)))
      | ~ r1_yellow_0(A_1,B_1122)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1)
      | r2_lattice3(A_1,B_1122,'#skF_1'(A_1,B_1122,k3_xboole_0(B_1122,u1_struct_0(A_1)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_5506])).

tff(c_5565,plain,(
    ! [A_1131,B_1132] :
      ( r1_yellow_0(A_1131,k3_xboole_0(B_1132,u1_struct_0(A_1131)))
      | ~ r1_yellow_0(A_1131,B_1132)
      | ~ l1_orders_2(A_1131)
      | v2_struct_0(A_1131)
      | r2_lattice3(A_1131,B_1132,'#skF_1'(A_1131,B_1132,k3_xboole_0(B_1132,u1_struct_0(A_1131)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_5506])).

tff(c_5409,plain,(
    ! [A_1101,C_1102,B_1103] :
      ( ~ r2_lattice3(A_1101,C_1102,'#skF_1'(A_1101,B_1103,C_1102))
      | ~ r2_lattice3(A_1101,B_1103,'#skF_1'(A_1101,B_1103,C_1102))
      | r1_yellow_0(A_1101,C_1102)
      | ~ r1_yellow_0(A_1101,B_1103)
      | ~ l1_orders_2(A_1101)
      | v2_struct_0(A_1101) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5417,plain,(
    ! [A_17,B_1103,B_20] :
      ( ~ r2_lattice3(A_17,B_1103,'#skF_1'(A_17,B_1103,k3_xboole_0(B_20,u1_struct_0(A_17))))
      | r1_yellow_0(A_17,k3_xboole_0(B_20,u1_struct_0(A_17)))
      | ~ r1_yellow_0(A_17,B_1103)
      | ~ r2_lattice3(A_17,B_20,'#skF_1'(A_17,B_1103,k3_xboole_0(B_20,u1_struct_0(A_17))))
      | ~ m1_subset_1('#skF_1'(A_17,B_1103,k3_xboole_0(B_20,u1_struct_0(A_17))),u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_28,c_5409])).

tff(c_5574,plain,(
    ! [A_1133,B_1134] :
      ( ~ r2_lattice3(A_1133,B_1134,'#skF_1'(A_1133,B_1134,k3_xboole_0(B_1134,u1_struct_0(A_1133))))
      | ~ m1_subset_1('#skF_1'(A_1133,B_1134,k3_xboole_0(B_1134,u1_struct_0(A_1133))),u1_struct_0(A_1133))
      | r1_yellow_0(A_1133,k3_xboole_0(B_1134,u1_struct_0(A_1133)))
      | ~ r1_yellow_0(A_1133,B_1134)
      | ~ l1_orders_2(A_1133)
      | v2_struct_0(A_1133) ) ),
    inference(resolution,[status(thm)],[c_5565,c_5417])).

tff(c_5585,plain,(
    ! [A_1135,B_1136] :
      ( ~ m1_subset_1('#skF_1'(A_1135,B_1136,k3_xboole_0(B_1136,u1_struct_0(A_1135))),u1_struct_0(A_1135))
      | r1_yellow_0(A_1135,k3_xboole_0(B_1136,u1_struct_0(A_1135)))
      | ~ r1_yellow_0(A_1135,B_1136)
      | ~ l1_orders_2(A_1135)
      | v2_struct_0(A_1135) ) ),
    inference(resolution,[status(thm)],[c_5544,c_5574])).

tff(c_5591,plain,(
    ! [A_1137,B_1138] :
      ( r1_yellow_0(A_1137,k3_xboole_0(B_1138,u1_struct_0(A_1137)))
      | ~ r1_yellow_0(A_1137,B_1138)
      | ~ l1_orders_2(A_1137)
      | v2_struct_0(A_1137) ) ),
    inference(resolution,[status(thm)],[c_2,c_5585])).

tff(c_5318,plain,(
    ~ r2_yellow_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_3811])).

tff(c_46,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_4')
    | r2_yellow_0('#skF_3','#skF_5')
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_5328,plain,
    ( r2_yellow_0('#skF_3','#skF_5')
    | r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3812,c_46])).

tff(c_5329,plain,
    ( r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3')))
    | ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_5318,c_5328])).

tff(c_5330,plain,(
    ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_5329])).

tff(c_5594,plain,
    ( ~ r1_yellow_0('#skF_3','#skF_7')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5591,c_5330])).

tff(c_5597,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_5319,c_5594])).

tff(c_5599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_5597])).

tff(c_5600,plain,(
    r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_5329])).

tff(c_5682,plain,(
    ! [A_1160,B_1161,C_1162] :
      ( r2_lattice3(A_1160,B_1161,'#skF_1'(A_1160,B_1161,C_1162))
      | r2_lattice3(A_1160,C_1162,'#skF_1'(A_1160,B_1161,C_1162))
      | r1_yellow_0(A_1160,C_1162)
      | ~ r1_yellow_0(A_1160,B_1161)
      | ~ l1_orders_2(A_1160)
      | v2_struct_0(A_1160) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5785,plain,(
    ! [A_1180,B_1181,C_1182] :
      ( r2_lattice3(A_1180,B_1181,'#skF_1'(A_1180,k3_xboole_0(B_1181,u1_struct_0(A_1180)),C_1182))
      | ~ m1_subset_1('#skF_1'(A_1180,k3_xboole_0(B_1181,u1_struct_0(A_1180)),C_1182),u1_struct_0(A_1180))
      | r2_lattice3(A_1180,C_1182,'#skF_1'(A_1180,k3_xboole_0(B_1181,u1_struct_0(A_1180)),C_1182))
      | r1_yellow_0(A_1180,C_1182)
      | ~ r1_yellow_0(A_1180,k3_xboole_0(B_1181,u1_struct_0(A_1180)))
      | ~ l1_orders_2(A_1180)
      | v2_struct_0(A_1180) ) ),
    inference(resolution,[status(thm)],[c_5682,c_26])).

tff(c_5789,plain,(
    ! [A_1,B_1181,C_7] :
      ( r2_lattice3(A_1,B_1181,'#skF_1'(A_1,k3_xboole_0(B_1181,u1_struct_0(A_1)),C_7))
      | r2_lattice3(A_1,C_7,'#skF_1'(A_1,k3_xboole_0(B_1181,u1_struct_0(A_1)),C_7))
      | r1_yellow_0(A_1,C_7)
      | ~ r1_yellow_0(A_1,k3_xboole_0(B_1181,u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_5785])).

tff(c_5811,plain,(
    ! [A_1,B_1181] :
      ( r1_yellow_0(A_1,B_1181)
      | ~ r1_yellow_0(A_1,k3_xboole_0(B_1181,u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1)
      | r2_lattice3(A_1,B_1181,'#skF_1'(A_1,k3_xboole_0(B_1181,u1_struct_0(A_1)),B_1181)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_5789])).

tff(c_5832,plain,(
    ! [A_1188,B_1189] :
      ( r1_yellow_0(A_1188,B_1189)
      | ~ r1_yellow_0(A_1188,k3_xboole_0(B_1189,u1_struct_0(A_1188)))
      | ~ l1_orders_2(A_1188)
      | v2_struct_0(A_1188)
      | r2_lattice3(A_1188,B_1189,'#skF_1'(A_1188,k3_xboole_0(B_1189,u1_struct_0(A_1188)),B_1189)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_5789])).

tff(c_5858,plain,(
    ! [A_1193,B_1194] :
      ( ~ r2_lattice3(A_1193,k3_xboole_0(B_1194,u1_struct_0(A_1193)),'#skF_1'(A_1193,k3_xboole_0(B_1194,u1_struct_0(A_1193)),B_1194))
      | r1_yellow_0(A_1193,B_1194)
      | ~ r1_yellow_0(A_1193,k3_xboole_0(B_1194,u1_struct_0(A_1193)))
      | ~ l1_orders_2(A_1193)
      | v2_struct_0(A_1193) ) ),
    inference(resolution,[status(thm)],[c_5832,c_4])).

tff(c_5910,plain,(
    ! [A_1207,B_1208] :
      ( r1_yellow_0(A_1207,B_1208)
      | ~ r1_yellow_0(A_1207,k3_xboole_0(B_1208,u1_struct_0(A_1207)))
      | ~ r2_lattice3(A_1207,B_1208,'#skF_1'(A_1207,k3_xboole_0(B_1208,u1_struct_0(A_1207)),B_1208))
      | ~ m1_subset_1('#skF_1'(A_1207,k3_xboole_0(B_1208,u1_struct_0(A_1207)),B_1208),u1_struct_0(A_1207))
      | ~ l1_orders_2(A_1207)
      | v2_struct_0(A_1207) ) ),
    inference(resolution,[status(thm)],[c_28,c_5858])).

tff(c_5921,plain,(
    ! [A_1209,B_1210] :
      ( ~ m1_subset_1('#skF_1'(A_1209,k3_xboole_0(B_1210,u1_struct_0(A_1209)),B_1210),u1_struct_0(A_1209))
      | r1_yellow_0(A_1209,B_1210)
      | ~ r1_yellow_0(A_1209,k3_xboole_0(B_1210,u1_struct_0(A_1209)))
      | ~ l1_orders_2(A_1209)
      | v2_struct_0(A_1209) ) ),
    inference(resolution,[status(thm)],[c_5811,c_5910])).

tff(c_5932,plain,(
    ! [A_1214,C_1215] :
      ( r1_yellow_0(A_1214,C_1215)
      | ~ r1_yellow_0(A_1214,k3_xboole_0(C_1215,u1_struct_0(A_1214)))
      | ~ l1_orders_2(A_1214)
      | v2_struct_0(A_1214) ) ),
    inference(resolution,[status(thm)],[c_2,c_5921])).

tff(c_5938,plain,
    ( r1_yellow_0('#skF_3','#skF_6')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5600,c_5932])).

tff(c_5945,plain,
    ( r1_yellow_0('#skF_3','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_5938])).

tff(c_5947,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_65,c_5945])).

tff(c_5948,plain,(
    r1_yellow_0('#skF_3',k3_xboole_0('#skF_6',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_5317])).

tff(c_6001,plain,(
    ! [A_1237,B_1238,C_1239] :
      ( r2_lattice3(A_1237,B_1238,'#skF_1'(A_1237,B_1238,C_1239))
      | r2_lattice3(A_1237,C_1239,'#skF_1'(A_1237,B_1238,C_1239))
      | r1_yellow_0(A_1237,C_1239)
      | ~ r1_yellow_0(A_1237,B_1238)
      | ~ l1_orders_2(A_1237)
      | v2_struct_0(A_1237) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6108,plain,(
    ! [A_1257,B_1258,C_1259] :
      ( r2_lattice3(A_1257,B_1258,'#skF_1'(A_1257,k3_xboole_0(B_1258,u1_struct_0(A_1257)),C_1259))
      | ~ m1_subset_1('#skF_1'(A_1257,k3_xboole_0(B_1258,u1_struct_0(A_1257)),C_1259),u1_struct_0(A_1257))
      | r2_lattice3(A_1257,C_1259,'#skF_1'(A_1257,k3_xboole_0(B_1258,u1_struct_0(A_1257)),C_1259))
      | r1_yellow_0(A_1257,C_1259)
      | ~ r1_yellow_0(A_1257,k3_xboole_0(B_1258,u1_struct_0(A_1257)))
      | ~ l1_orders_2(A_1257)
      | v2_struct_0(A_1257) ) ),
    inference(resolution,[status(thm)],[c_6001,c_26])).

tff(c_6112,plain,(
    ! [A_1,B_1258,C_7] :
      ( r2_lattice3(A_1,B_1258,'#skF_1'(A_1,k3_xboole_0(B_1258,u1_struct_0(A_1)),C_7))
      | r2_lattice3(A_1,C_7,'#skF_1'(A_1,k3_xboole_0(B_1258,u1_struct_0(A_1)),C_7))
      | r1_yellow_0(A_1,C_7)
      | ~ r1_yellow_0(A_1,k3_xboole_0(B_1258,u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_6108])).

tff(c_6125,plain,(
    ! [A_1,B_1258] :
      ( r1_yellow_0(A_1,B_1258)
      | ~ r1_yellow_0(A_1,k3_xboole_0(B_1258,u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1)
      | r2_lattice3(A_1,B_1258,'#skF_1'(A_1,k3_xboole_0(B_1258,u1_struct_0(A_1)),B_1258)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_6112])).

tff(c_6146,plain,(
    ! [A_1263,B_1264] :
      ( r1_yellow_0(A_1263,B_1264)
      | ~ r1_yellow_0(A_1263,k3_xboole_0(B_1264,u1_struct_0(A_1263)))
      | ~ l1_orders_2(A_1263)
      | v2_struct_0(A_1263)
      | r2_lattice3(A_1263,B_1264,'#skF_1'(A_1263,k3_xboole_0(B_1264,u1_struct_0(A_1263)),B_1264)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_6112])).

tff(c_6155,plain,(
    ! [A_1265,B_1266] :
      ( ~ r2_lattice3(A_1265,k3_xboole_0(B_1266,u1_struct_0(A_1265)),'#skF_1'(A_1265,k3_xboole_0(B_1266,u1_struct_0(A_1265)),B_1266))
      | r1_yellow_0(A_1265,B_1266)
      | ~ r1_yellow_0(A_1265,k3_xboole_0(B_1266,u1_struct_0(A_1265)))
      | ~ l1_orders_2(A_1265)
      | v2_struct_0(A_1265) ) ),
    inference(resolution,[status(thm)],[c_6146,c_4])).

tff(c_6189,plain,(
    ! [A_1273,B_1274] :
      ( r1_yellow_0(A_1273,B_1274)
      | ~ r1_yellow_0(A_1273,k3_xboole_0(B_1274,u1_struct_0(A_1273)))
      | ~ r2_lattice3(A_1273,B_1274,'#skF_1'(A_1273,k3_xboole_0(B_1274,u1_struct_0(A_1273)),B_1274))
      | ~ m1_subset_1('#skF_1'(A_1273,k3_xboole_0(B_1274,u1_struct_0(A_1273)),B_1274),u1_struct_0(A_1273))
      | ~ l1_orders_2(A_1273)
      | v2_struct_0(A_1273) ) ),
    inference(resolution,[status(thm)],[c_28,c_6155])).

tff(c_6200,plain,(
    ! [A_1275,B_1276] :
      ( ~ m1_subset_1('#skF_1'(A_1275,k3_xboole_0(B_1276,u1_struct_0(A_1275)),B_1276),u1_struct_0(A_1275))
      | r1_yellow_0(A_1275,B_1276)
      | ~ r1_yellow_0(A_1275,k3_xboole_0(B_1276,u1_struct_0(A_1275)))
      | ~ l1_orders_2(A_1275)
      | v2_struct_0(A_1275) ) ),
    inference(resolution,[status(thm)],[c_6125,c_6189])).

tff(c_6211,plain,(
    ! [A_1280,C_1281] :
      ( r1_yellow_0(A_1280,C_1281)
      | ~ r1_yellow_0(A_1280,k3_xboole_0(C_1281,u1_struct_0(A_1280)))
      | ~ l1_orders_2(A_1280)
      | v2_struct_0(A_1280) ) ),
    inference(resolution,[status(thm)],[c_2,c_6200])).

tff(c_6217,plain,
    ( r1_yellow_0('#skF_3','#skF_6')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_5948,c_6211])).

tff(c_6221,plain,
    ( r1_yellow_0('#skF_3','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6217])).

tff(c_6223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_65,c_6221])).

tff(c_6224,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_4')
    | r1_yellow_0('#skF_3','#skF_7')
    | r2_yellow_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_6226,plain,(
    ~ r2_yellow_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6224])).

tff(c_6225,plain,(
    r1_yellow_0('#skF_3','#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_56,plain,
    ( r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3')))
    | r2_yellow_0('#skF_3','#skF_5')
    | ~ r1_yellow_0('#skF_3','#skF_6')
    | r1_yellow_0('#skF_3','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6228,plain,
    ( r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3')))
    | r2_yellow_0('#skF_3','#skF_5')
    | r1_yellow_0('#skF_3','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6225,c_56])).

tff(c_6229,plain,(
    r1_yellow_0('#skF_3','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_6228])).

tff(c_6314,plain,(
    ! [A_1309,B_1310,C_1311] :
      ( r2_lattice3(A_1309,B_1310,'#skF_1'(A_1309,B_1310,C_1311))
      | r2_lattice3(A_1309,C_1311,'#skF_1'(A_1309,B_1310,C_1311))
      | r1_yellow_0(A_1309,C_1311)
      | ~ r1_yellow_0(A_1309,B_1310)
      | ~ l1_orders_2(A_1309)
      | v2_struct_0(A_1309) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6339,plain,(
    ! [A_1315,B_1316,B_1317] :
      ( r2_lattice3(A_1315,B_1316,'#skF_1'(A_1315,B_1317,k3_xboole_0(B_1316,u1_struct_0(A_1315))))
      | ~ m1_subset_1('#skF_1'(A_1315,B_1317,k3_xboole_0(B_1316,u1_struct_0(A_1315))),u1_struct_0(A_1315))
      | r2_lattice3(A_1315,B_1317,'#skF_1'(A_1315,B_1317,k3_xboole_0(B_1316,u1_struct_0(A_1315))))
      | r1_yellow_0(A_1315,k3_xboole_0(B_1316,u1_struct_0(A_1315)))
      | ~ r1_yellow_0(A_1315,B_1317)
      | ~ l1_orders_2(A_1315)
      | v2_struct_0(A_1315) ) ),
    inference(resolution,[status(thm)],[c_6314,c_26])).

tff(c_6343,plain,(
    ! [A_1,B_1316,B_6] :
      ( r2_lattice3(A_1,B_1316,'#skF_1'(A_1,B_6,k3_xboole_0(B_1316,u1_struct_0(A_1))))
      | r2_lattice3(A_1,B_6,'#skF_1'(A_1,B_6,k3_xboole_0(B_1316,u1_struct_0(A_1))))
      | r1_yellow_0(A_1,k3_xboole_0(B_1316,u1_struct_0(A_1)))
      | ~ r1_yellow_0(A_1,B_6)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_6339])).

tff(c_6356,plain,(
    ! [A_1,B_1316] :
      ( r1_yellow_0(A_1,k3_xboole_0(B_1316,u1_struct_0(A_1)))
      | ~ r1_yellow_0(A_1,B_1316)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1)
      | r2_lattice3(A_1,B_1316,'#skF_1'(A_1,B_1316,k3_xboole_0(B_1316,u1_struct_0(A_1)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_6343])).

tff(c_6377,plain,(
    ! [A_1321,B_1322] :
      ( r1_yellow_0(A_1321,k3_xboole_0(B_1322,u1_struct_0(A_1321)))
      | ~ r1_yellow_0(A_1321,B_1322)
      | ~ l1_orders_2(A_1321)
      | v2_struct_0(A_1321)
      | r2_lattice3(A_1321,B_1322,'#skF_1'(A_1321,B_1322,k3_xboole_0(B_1322,u1_struct_0(A_1321)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_6343])).

tff(c_6295,plain,(
    ! [A_1306,C_1307,B_1308] :
      ( ~ r2_lattice3(A_1306,C_1307,'#skF_1'(A_1306,B_1308,C_1307))
      | ~ r2_lattice3(A_1306,B_1308,'#skF_1'(A_1306,B_1308,C_1307))
      | r1_yellow_0(A_1306,C_1307)
      | ~ r1_yellow_0(A_1306,B_1308)
      | ~ l1_orders_2(A_1306)
      | v2_struct_0(A_1306) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6299,plain,(
    ! [A_17,B_1308,B_20] :
      ( ~ r2_lattice3(A_17,B_1308,'#skF_1'(A_17,B_1308,k3_xboole_0(B_20,u1_struct_0(A_17))))
      | r1_yellow_0(A_17,k3_xboole_0(B_20,u1_struct_0(A_17)))
      | ~ r1_yellow_0(A_17,B_1308)
      | ~ r2_lattice3(A_17,B_20,'#skF_1'(A_17,B_1308,k3_xboole_0(B_20,u1_struct_0(A_17))))
      | ~ m1_subset_1('#skF_1'(A_17,B_1308,k3_xboole_0(B_20,u1_struct_0(A_17))),u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_28,c_6295])).

tff(c_6386,plain,(
    ! [A_1323,B_1324] :
      ( ~ r2_lattice3(A_1323,B_1324,'#skF_1'(A_1323,B_1324,k3_xboole_0(B_1324,u1_struct_0(A_1323))))
      | ~ m1_subset_1('#skF_1'(A_1323,B_1324,k3_xboole_0(B_1324,u1_struct_0(A_1323))),u1_struct_0(A_1323))
      | r1_yellow_0(A_1323,k3_xboole_0(B_1324,u1_struct_0(A_1323)))
      | ~ r1_yellow_0(A_1323,B_1324)
      | ~ l1_orders_2(A_1323)
      | v2_struct_0(A_1323) ) ),
    inference(resolution,[status(thm)],[c_6377,c_6299])).

tff(c_6397,plain,(
    ! [A_1325,B_1326] :
      ( ~ m1_subset_1('#skF_1'(A_1325,B_1326,k3_xboole_0(B_1326,u1_struct_0(A_1325))),u1_struct_0(A_1325))
      | r1_yellow_0(A_1325,k3_xboole_0(B_1326,u1_struct_0(A_1325)))
      | ~ r1_yellow_0(A_1325,B_1326)
      | ~ l1_orders_2(A_1325)
      | v2_struct_0(A_1325) ) ),
    inference(resolution,[status(thm)],[c_6356,c_6386])).

tff(c_6403,plain,(
    ! [A_1327,B_1328] :
      ( r1_yellow_0(A_1327,k3_xboole_0(B_1328,u1_struct_0(A_1327)))
      | ~ r1_yellow_0(A_1327,B_1328)
      | ~ l1_orders_2(A_1327)
      | v2_struct_0(A_1327) ) ),
    inference(resolution,[status(thm)],[c_2,c_6397])).

tff(c_40,plain,
    ( r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3')))
    | r2_yellow_0('#skF_3','#skF_5')
    | ~ r1_yellow_0('#skF_3','#skF_6')
    | ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6242,plain,
    ( r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3')))
    | r2_yellow_0('#skF_3','#skF_5')
    | ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6225,c_40])).

tff(c_6243,plain,(
    ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_6242])).

tff(c_6406,plain,
    ( ~ r1_yellow_0('#skF_3','#skF_7')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6403,c_6243])).

tff(c_6409,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6229,c_6406])).

tff(c_6411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6409])).

tff(c_6412,plain,
    ( r2_yellow_0('#skF_3','#skF_5')
    | r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_6242])).

tff(c_6414,plain,(
    r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_6412])).

tff(c_6477,plain,(
    ! [A_1344,B_1345,C_1346] :
      ( r1_lattice3(A_1344,B_1345,'#skF_2'(A_1344,B_1345,C_1346))
      | r1_lattice3(A_1344,C_1346,'#skF_2'(A_1344,B_1345,C_1346))
      | r2_yellow_0(A_1344,C_1346)
      | ~ r2_yellow_0(A_1344,B_1345)
      | ~ l1_orders_2(A_1344)
      | v2_struct_0(A_1344) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6637,plain,(
    ! [A_1379,B_1380,C_1381] :
      ( r1_lattice3(A_1379,B_1380,'#skF_2'(A_1379,k3_xboole_0(B_1380,u1_struct_0(A_1379)),C_1381))
      | ~ m1_subset_1('#skF_2'(A_1379,k3_xboole_0(B_1380,u1_struct_0(A_1379)),C_1381),u1_struct_0(A_1379))
      | r1_lattice3(A_1379,C_1381,'#skF_2'(A_1379,k3_xboole_0(B_1380,u1_struct_0(A_1379)),C_1381))
      | r2_yellow_0(A_1379,C_1381)
      | ~ r2_yellow_0(A_1379,k3_xboole_0(B_1380,u1_struct_0(A_1379)))
      | ~ l1_orders_2(A_1379)
      | v2_struct_0(A_1379) ) ),
    inference(resolution,[status(thm)],[c_6477,c_22])).

tff(c_6641,plain,(
    ! [A_9,B_1380,C_15] :
      ( r1_lattice3(A_9,B_1380,'#skF_2'(A_9,k3_xboole_0(B_1380,u1_struct_0(A_9)),C_15))
      | r1_lattice3(A_9,C_15,'#skF_2'(A_9,k3_xboole_0(B_1380,u1_struct_0(A_9)),C_15))
      | r2_yellow_0(A_9,C_15)
      | ~ r2_yellow_0(A_9,k3_xboole_0(B_1380,u1_struct_0(A_9)))
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_6637])).

tff(c_6655,plain,(
    ! [A_9,B_1380] :
      ( r2_yellow_0(A_9,B_1380)
      | ~ r2_yellow_0(A_9,k3_xboole_0(B_1380,u1_struct_0(A_9)))
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9)
      | r1_lattice3(A_9,B_1380,'#skF_2'(A_9,k3_xboole_0(B_1380,u1_struct_0(A_9)),B_1380)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_6641])).

tff(c_6676,plain,(
    ! [A_1387,B_1388] :
      ( r2_yellow_0(A_1387,B_1388)
      | ~ r2_yellow_0(A_1387,k3_xboole_0(B_1388,u1_struct_0(A_1387)))
      | ~ l1_orders_2(A_1387)
      | v2_struct_0(A_1387)
      | r1_lattice3(A_1387,B_1388,'#skF_2'(A_1387,k3_xboole_0(B_1388,u1_struct_0(A_1387)),B_1388)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_6641])).

tff(c_6685,plain,(
    ! [A_1389,B_1390] :
      ( ~ r1_lattice3(A_1389,k3_xboole_0(B_1390,u1_struct_0(A_1389)),'#skF_2'(A_1389,k3_xboole_0(B_1390,u1_struct_0(A_1389)),B_1390))
      | r2_yellow_0(A_1389,B_1390)
      | ~ r2_yellow_0(A_1389,k3_xboole_0(B_1390,u1_struct_0(A_1389)))
      | ~ l1_orders_2(A_1389)
      | v2_struct_0(A_1389) ) ),
    inference(resolution,[status(thm)],[c_6676,c_14])).

tff(c_6719,plain,(
    ! [A_1397,B_1398] :
      ( r2_yellow_0(A_1397,B_1398)
      | ~ r2_yellow_0(A_1397,k3_xboole_0(B_1398,u1_struct_0(A_1397)))
      | ~ r1_lattice3(A_1397,B_1398,'#skF_2'(A_1397,k3_xboole_0(B_1398,u1_struct_0(A_1397)),B_1398))
      | ~ m1_subset_1('#skF_2'(A_1397,k3_xboole_0(B_1398,u1_struct_0(A_1397)),B_1398),u1_struct_0(A_1397))
      | ~ l1_orders_2(A_1397)
      | v2_struct_0(A_1397) ) ),
    inference(resolution,[status(thm)],[c_24,c_6685])).

tff(c_6735,plain,(
    ! [A_1402,B_1403] :
      ( ~ m1_subset_1('#skF_2'(A_1402,k3_xboole_0(B_1403,u1_struct_0(A_1402)),B_1403),u1_struct_0(A_1402))
      | r2_yellow_0(A_1402,B_1403)
      | ~ r2_yellow_0(A_1402,k3_xboole_0(B_1403,u1_struct_0(A_1402)))
      | ~ l1_orders_2(A_1402)
      | v2_struct_0(A_1402) ) ),
    inference(resolution,[status(thm)],[c_6655,c_6719])).

tff(c_6741,plain,(
    ! [A_1404,C_1405] :
      ( r2_yellow_0(A_1404,C_1405)
      | ~ r2_yellow_0(A_1404,k3_xboole_0(C_1405,u1_struct_0(A_1404)))
      | ~ l1_orders_2(A_1404)
      | v2_struct_0(A_1404) ) ),
    inference(resolution,[status(thm)],[c_12,c_6735])).

tff(c_6747,plain,
    ( r2_yellow_0('#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6414,c_6741])).

tff(c_6751,plain,
    ( r2_yellow_0('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6747])).

tff(c_6753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6226,c_6751])).

tff(c_6754,plain,(
    r2_yellow_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_6412])).

tff(c_6827,plain,(
    ! [A_1424,B_1425,C_1426] :
      ( r1_lattice3(A_1424,B_1425,'#skF_2'(A_1424,B_1425,C_1426))
      | r1_lattice3(A_1424,C_1426,'#skF_2'(A_1424,B_1425,C_1426))
      | r2_yellow_0(A_1424,C_1426)
      | ~ r2_yellow_0(A_1424,B_1425)
      | ~ l1_orders_2(A_1424)
      | v2_struct_0(A_1424) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6851,plain,(
    ! [A_1430,B_1431,B_1432] :
      ( r1_lattice3(A_1430,B_1431,'#skF_2'(A_1430,B_1432,k3_xboole_0(B_1431,u1_struct_0(A_1430))))
      | ~ m1_subset_1('#skF_2'(A_1430,B_1432,k3_xboole_0(B_1431,u1_struct_0(A_1430))),u1_struct_0(A_1430))
      | r1_lattice3(A_1430,B_1432,'#skF_2'(A_1430,B_1432,k3_xboole_0(B_1431,u1_struct_0(A_1430))))
      | r2_yellow_0(A_1430,k3_xboole_0(B_1431,u1_struct_0(A_1430)))
      | ~ r2_yellow_0(A_1430,B_1432)
      | ~ l1_orders_2(A_1430)
      | v2_struct_0(A_1430) ) ),
    inference(resolution,[status(thm)],[c_6827,c_22])).

tff(c_6855,plain,(
    ! [A_9,B_1431,B_14] :
      ( r1_lattice3(A_9,B_1431,'#skF_2'(A_9,B_14,k3_xboole_0(B_1431,u1_struct_0(A_9))))
      | r1_lattice3(A_9,B_14,'#skF_2'(A_9,B_14,k3_xboole_0(B_1431,u1_struct_0(A_9))))
      | r2_yellow_0(A_9,k3_xboole_0(B_1431,u1_struct_0(A_9)))
      | ~ r2_yellow_0(A_9,B_14)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_6851])).

tff(c_6868,plain,(
    ! [A_9,B_1431] :
      ( r2_yellow_0(A_9,k3_xboole_0(B_1431,u1_struct_0(A_9)))
      | ~ r2_yellow_0(A_9,B_1431)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9)
      | r1_lattice3(A_9,B_1431,'#skF_2'(A_9,B_1431,k3_xboole_0(B_1431,u1_struct_0(A_9)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_6855])).

tff(c_6808,plain,(
    ! [A_1421,C_1422,B_1423] :
      ( ~ r1_lattice3(A_1421,C_1422,'#skF_2'(A_1421,B_1423,C_1422))
      | ~ r1_lattice3(A_1421,B_1423,'#skF_2'(A_1421,B_1423,C_1422))
      | r2_yellow_0(A_1421,C_1422)
      | ~ r2_yellow_0(A_1421,B_1423)
      | ~ l1_orders_2(A_1421)
      | v2_struct_0(A_1421) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6891,plain,(
    ! [A_1438,B_1439,B_1440] :
      ( ~ r1_lattice3(A_1438,B_1439,'#skF_2'(A_1438,B_1439,k3_xboole_0(B_1440,u1_struct_0(A_1438))))
      | r2_yellow_0(A_1438,k3_xboole_0(B_1440,u1_struct_0(A_1438)))
      | ~ r2_yellow_0(A_1438,B_1439)
      | ~ r1_lattice3(A_1438,B_1440,'#skF_2'(A_1438,B_1439,k3_xboole_0(B_1440,u1_struct_0(A_1438))))
      | ~ m1_subset_1('#skF_2'(A_1438,B_1439,k3_xboole_0(B_1440,u1_struct_0(A_1438))),u1_struct_0(A_1438))
      | ~ l1_orders_2(A_1438)
      | v2_struct_0(A_1438) ) ),
    inference(resolution,[status(thm)],[c_24,c_6808])).

tff(c_6908,plain,(
    ! [A_1441,B_1442] :
      ( ~ r1_lattice3(A_1441,B_1442,'#skF_2'(A_1441,B_1442,k3_xboole_0(B_1442,u1_struct_0(A_1441))))
      | ~ m1_subset_1('#skF_2'(A_1441,B_1442,k3_xboole_0(B_1442,u1_struct_0(A_1441))),u1_struct_0(A_1441))
      | r2_yellow_0(A_1441,k3_xboole_0(B_1442,u1_struct_0(A_1441)))
      | ~ r2_yellow_0(A_1441,B_1442)
      | ~ l1_orders_2(A_1441)
      | v2_struct_0(A_1441) ) ),
    inference(resolution,[status(thm)],[c_6868,c_6891])).

tff(c_6919,plain,(
    ! [A_1443,B_1444] :
      ( ~ m1_subset_1('#skF_2'(A_1443,B_1444,k3_xboole_0(B_1444,u1_struct_0(A_1443))),u1_struct_0(A_1443))
      | r2_yellow_0(A_1443,k3_xboole_0(B_1444,u1_struct_0(A_1443)))
      | ~ r2_yellow_0(A_1443,B_1444)
      | ~ l1_orders_2(A_1443)
      | v2_struct_0(A_1443) ) ),
    inference(resolution,[status(thm)],[c_6868,c_6908])).

tff(c_6925,plain,(
    ! [A_1445,B_1446] :
      ( r2_yellow_0(A_1445,k3_xboole_0(B_1446,u1_struct_0(A_1445)))
      | ~ r2_yellow_0(A_1445,B_1446)
      | ~ l1_orders_2(A_1445)
      | v2_struct_0(A_1445) ) ),
    inference(resolution,[status(thm)],[c_12,c_6919])).

tff(c_6755,plain,(
    ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_6412])).

tff(c_6413,plain,(
    r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_6242])).

tff(c_36,plain,
    ( r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3')))
    | ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3')))
    | ~ r1_yellow_0('#skF_3','#skF_6')
    | ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6778,plain,
    ( r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3')))
    | ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6413,c_6225,c_36])).

tff(c_6779,plain,(
    ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6755,c_6778])).

tff(c_6928,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6925,c_6779])).

tff(c_6934,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6754,c_6928])).

tff(c_6936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6934])).

tff(c_6937,plain,
    ( r2_yellow_0('#skF_3','#skF_5')
    | r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_6228])).

tff(c_6939,plain,(
    r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_6937])).

tff(c_6989,plain,(
    ! [A_1465,B_1466,C_1467] :
      ( r1_lattice3(A_1465,B_1466,'#skF_2'(A_1465,B_1466,C_1467))
      | r1_lattice3(A_1465,C_1467,'#skF_2'(A_1465,B_1466,C_1467))
      | r2_yellow_0(A_1465,C_1467)
      | ~ r2_yellow_0(A_1465,B_1466)
      | ~ l1_orders_2(A_1465)
      | v2_struct_0(A_1465) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_7192,plain,(
    ! [A_1507,B_1508,C_1509] :
      ( r1_lattice3(A_1507,B_1508,'#skF_2'(A_1507,k3_xboole_0(B_1508,u1_struct_0(A_1507)),C_1509))
      | ~ m1_subset_1('#skF_2'(A_1507,k3_xboole_0(B_1508,u1_struct_0(A_1507)),C_1509),u1_struct_0(A_1507))
      | r1_lattice3(A_1507,C_1509,'#skF_2'(A_1507,k3_xboole_0(B_1508,u1_struct_0(A_1507)),C_1509))
      | r2_yellow_0(A_1507,C_1509)
      | ~ r2_yellow_0(A_1507,k3_xboole_0(B_1508,u1_struct_0(A_1507)))
      | ~ l1_orders_2(A_1507)
      | v2_struct_0(A_1507) ) ),
    inference(resolution,[status(thm)],[c_6989,c_22])).

tff(c_7196,plain,(
    ! [A_9,B_1508,C_15] :
      ( r1_lattice3(A_9,B_1508,'#skF_2'(A_9,k3_xboole_0(B_1508,u1_struct_0(A_9)),C_15))
      | r1_lattice3(A_9,C_15,'#skF_2'(A_9,k3_xboole_0(B_1508,u1_struct_0(A_9)),C_15))
      | r2_yellow_0(A_9,C_15)
      | ~ r2_yellow_0(A_9,k3_xboole_0(B_1508,u1_struct_0(A_9)))
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_7192])).

tff(c_7209,plain,(
    ! [A_9,B_1508] :
      ( r2_yellow_0(A_9,B_1508)
      | ~ r2_yellow_0(A_9,k3_xboole_0(B_1508,u1_struct_0(A_9)))
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9)
      | r1_lattice3(A_9,B_1508,'#skF_2'(A_9,k3_xboole_0(B_1508,u1_struct_0(A_9)),B_1508)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_7196])).

tff(c_7230,plain,(
    ! [A_1513,B_1514] :
      ( r2_yellow_0(A_1513,B_1514)
      | ~ r2_yellow_0(A_1513,k3_xboole_0(B_1514,u1_struct_0(A_1513)))
      | ~ l1_orders_2(A_1513)
      | v2_struct_0(A_1513)
      | r1_lattice3(A_1513,B_1514,'#skF_2'(A_1513,k3_xboole_0(B_1514,u1_struct_0(A_1513)),B_1514)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_7196])).

tff(c_7239,plain,(
    ! [A_1515,B_1516] :
      ( ~ r1_lattice3(A_1515,k3_xboole_0(B_1516,u1_struct_0(A_1515)),'#skF_2'(A_1515,k3_xboole_0(B_1516,u1_struct_0(A_1515)),B_1516))
      | r2_yellow_0(A_1515,B_1516)
      | ~ r2_yellow_0(A_1515,k3_xboole_0(B_1516,u1_struct_0(A_1515)))
      | ~ l1_orders_2(A_1515)
      | v2_struct_0(A_1515) ) ),
    inference(resolution,[status(thm)],[c_7230,c_14])).

tff(c_7272,plain,(
    ! [A_1523,B_1524] :
      ( r2_yellow_0(A_1523,B_1524)
      | ~ r2_yellow_0(A_1523,k3_xboole_0(B_1524,u1_struct_0(A_1523)))
      | ~ r1_lattice3(A_1523,B_1524,'#skF_2'(A_1523,k3_xboole_0(B_1524,u1_struct_0(A_1523)),B_1524))
      | ~ m1_subset_1('#skF_2'(A_1523,k3_xboole_0(B_1524,u1_struct_0(A_1523)),B_1524),u1_struct_0(A_1523))
      | ~ l1_orders_2(A_1523)
      | v2_struct_0(A_1523) ) ),
    inference(resolution,[status(thm)],[c_24,c_7239])).

tff(c_7283,plain,(
    ! [A_1525,B_1526] :
      ( ~ m1_subset_1('#skF_2'(A_1525,k3_xboole_0(B_1526,u1_struct_0(A_1525)),B_1526),u1_struct_0(A_1525))
      | r2_yellow_0(A_1525,B_1526)
      | ~ r2_yellow_0(A_1525,k3_xboole_0(B_1526,u1_struct_0(A_1525)))
      | ~ l1_orders_2(A_1525)
      | v2_struct_0(A_1525) ) ),
    inference(resolution,[status(thm)],[c_7209,c_7272])).

tff(c_7294,plain,(
    ! [A_1530,C_1531] :
      ( r2_yellow_0(A_1530,C_1531)
      | ~ r2_yellow_0(A_1530,k3_xboole_0(C_1531,u1_struct_0(A_1530)))
      | ~ l1_orders_2(A_1530)
      | v2_struct_0(A_1530) ) ),
    inference(resolution,[status(thm)],[c_12,c_7283])).

tff(c_7297,plain,
    ( r2_yellow_0('#skF_3','#skF_4')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6939,c_7294])).

tff(c_7300,plain,
    ( r2_yellow_0('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7297])).

tff(c_7302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_6226,c_7300])).

tff(c_7303,plain,(
    r2_yellow_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_6937])).

tff(c_7398,plain,(
    ! [A_1559,B_1560,C_1561] :
      ( r1_lattice3(A_1559,B_1560,'#skF_2'(A_1559,B_1560,C_1561))
      | r1_lattice3(A_1559,C_1561,'#skF_2'(A_1559,B_1560,C_1561))
      | r2_yellow_0(A_1559,C_1561)
      | ~ r2_yellow_0(A_1559,B_1560)
      | ~ l1_orders_2(A_1559)
      | v2_struct_0(A_1559) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_7423,plain,(
    ! [A_1565,B_1566,B_1567] :
      ( r1_lattice3(A_1565,B_1566,'#skF_2'(A_1565,B_1567,k3_xboole_0(B_1566,u1_struct_0(A_1565))))
      | ~ m1_subset_1('#skF_2'(A_1565,B_1567,k3_xboole_0(B_1566,u1_struct_0(A_1565))),u1_struct_0(A_1565))
      | r1_lattice3(A_1565,B_1567,'#skF_2'(A_1565,B_1567,k3_xboole_0(B_1566,u1_struct_0(A_1565))))
      | r2_yellow_0(A_1565,k3_xboole_0(B_1566,u1_struct_0(A_1565)))
      | ~ r2_yellow_0(A_1565,B_1567)
      | ~ l1_orders_2(A_1565)
      | v2_struct_0(A_1565) ) ),
    inference(resolution,[status(thm)],[c_7398,c_22])).

tff(c_7427,plain,(
    ! [A_9,B_1566,B_14] :
      ( r1_lattice3(A_9,B_1566,'#skF_2'(A_9,B_14,k3_xboole_0(B_1566,u1_struct_0(A_9))))
      | r1_lattice3(A_9,B_14,'#skF_2'(A_9,B_14,k3_xboole_0(B_1566,u1_struct_0(A_9))))
      | r2_yellow_0(A_9,k3_xboole_0(B_1566,u1_struct_0(A_9)))
      | ~ r2_yellow_0(A_9,B_14)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_7423])).

tff(c_7445,plain,(
    ! [A_9,B_1566] :
      ( r2_yellow_0(A_9,k3_xboole_0(B_1566,u1_struct_0(A_9)))
      | ~ r2_yellow_0(A_9,B_1566)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9)
      | r1_lattice3(A_9,B_1566,'#skF_2'(A_9,B_1566,k3_xboole_0(B_1566,u1_struct_0(A_9)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_7427])).

tff(c_7466,plain,(
    ! [A_1574,B_1575] :
      ( r2_yellow_0(A_1574,k3_xboole_0(B_1575,u1_struct_0(A_1574)))
      | ~ r2_yellow_0(A_1574,B_1575)
      | ~ l1_orders_2(A_1574)
      | v2_struct_0(A_1574)
      | r1_lattice3(A_1574,B_1575,'#skF_2'(A_1574,B_1575,k3_xboole_0(B_1575,u1_struct_0(A_1574)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_7427])).

tff(c_7379,plain,(
    ! [A_1556,C_1557,B_1558] :
      ( ~ r1_lattice3(A_1556,C_1557,'#skF_2'(A_1556,B_1558,C_1557))
      | ~ r1_lattice3(A_1556,B_1558,'#skF_2'(A_1556,B_1558,C_1557))
      | r2_yellow_0(A_1556,C_1557)
      | ~ r2_yellow_0(A_1556,B_1558)
      | ~ l1_orders_2(A_1556)
      | v2_struct_0(A_1556) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_7383,plain,(
    ! [A_17,B_1558,B_20] :
      ( ~ r1_lattice3(A_17,B_1558,'#skF_2'(A_17,B_1558,k3_xboole_0(B_20,u1_struct_0(A_17))))
      | r2_yellow_0(A_17,k3_xboole_0(B_20,u1_struct_0(A_17)))
      | ~ r2_yellow_0(A_17,B_1558)
      | ~ r1_lattice3(A_17,B_20,'#skF_2'(A_17,B_1558,k3_xboole_0(B_20,u1_struct_0(A_17))))
      | ~ m1_subset_1('#skF_2'(A_17,B_1558,k3_xboole_0(B_20,u1_struct_0(A_17))),u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_24,c_7379])).

tff(c_7524,plain,(
    ! [A_1583,B_1584] :
      ( ~ r1_lattice3(A_1583,B_1584,'#skF_2'(A_1583,B_1584,k3_xboole_0(B_1584,u1_struct_0(A_1583))))
      | ~ m1_subset_1('#skF_2'(A_1583,B_1584,k3_xboole_0(B_1584,u1_struct_0(A_1583))),u1_struct_0(A_1583))
      | r2_yellow_0(A_1583,k3_xboole_0(B_1584,u1_struct_0(A_1583)))
      | ~ r2_yellow_0(A_1583,B_1584)
      | ~ l1_orders_2(A_1583)
      | v2_struct_0(A_1583) ) ),
    inference(resolution,[status(thm)],[c_7466,c_7383])).

tff(c_7535,plain,(
    ! [A_1585,B_1586] :
      ( ~ m1_subset_1('#skF_2'(A_1585,B_1586,k3_xboole_0(B_1586,u1_struct_0(A_1585))),u1_struct_0(A_1585))
      | r2_yellow_0(A_1585,k3_xboole_0(B_1586,u1_struct_0(A_1585)))
      | ~ r2_yellow_0(A_1585,B_1586)
      | ~ l1_orders_2(A_1585)
      | v2_struct_0(A_1585) ) ),
    inference(resolution,[status(thm)],[c_7445,c_7524])).

tff(c_7546,plain,(
    ! [A_1590,B_1591] :
      ( r2_yellow_0(A_1590,k3_xboole_0(B_1591,u1_struct_0(A_1590)))
      | ~ r2_yellow_0(A_1590,B_1591)
      | ~ l1_orders_2(A_1590)
      | v2_struct_0(A_1590) ) ),
    inference(resolution,[status(thm)],[c_12,c_7535])).

tff(c_6938,plain,(
    ~ r1_yellow_0('#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_6228])).

tff(c_7304,plain,(
    ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_6937])).

tff(c_52,plain,
    ( r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3')))
    | ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3')))
    | ~ r1_yellow_0('#skF_3','#skF_6')
    | r1_yellow_0('#skF_3','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_7321,plain,
    ( r2_yellow_0('#skF_3',k3_xboole_0('#skF_4',u1_struct_0('#skF_3')))
    | ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3')))
    | r1_yellow_0('#skF_3','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6225,c_52])).

tff(c_7322,plain,(
    ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6938,c_7304,c_7321])).

tff(c_7549,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_7546,c_7322])).

tff(c_7555,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7303,c_7549])).

tff(c_7557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_7555])).

tff(c_7558,plain,
    ( r2_yellow_0('#skF_3','#skF_5')
    | r1_yellow_0('#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_6224])).

tff(c_7560,plain,(
    r1_yellow_0('#skF_3','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_7558])).

tff(c_7616,plain,(
    ! [A_1610,B_1611,C_1612] :
      ( r2_lattice3(A_1610,B_1611,'#skF_1'(A_1610,B_1611,C_1612))
      | r2_lattice3(A_1610,C_1612,'#skF_1'(A_1610,B_1611,C_1612))
      | r1_yellow_0(A_1610,C_1612)
      | ~ r1_yellow_0(A_1610,B_1611)
      | ~ l1_orders_2(A_1610)
      | v2_struct_0(A_1610) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7690,plain,(
    ! [A_1628,B_1629,B_1630] :
      ( r2_lattice3(A_1628,B_1629,'#skF_1'(A_1628,B_1630,k3_xboole_0(B_1629,u1_struct_0(A_1628))))
      | ~ m1_subset_1('#skF_1'(A_1628,B_1630,k3_xboole_0(B_1629,u1_struct_0(A_1628))),u1_struct_0(A_1628))
      | r2_lattice3(A_1628,B_1630,'#skF_1'(A_1628,B_1630,k3_xboole_0(B_1629,u1_struct_0(A_1628))))
      | r1_yellow_0(A_1628,k3_xboole_0(B_1629,u1_struct_0(A_1628)))
      | ~ r1_yellow_0(A_1628,B_1630)
      | ~ l1_orders_2(A_1628)
      | v2_struct_0(A_1628) ) ),
    inference(resolution,[status(thm)],[c_7616,c_26])).

tff(c_7694,plain,(
    ! [A_1,B_1629,B_6] :
      ( r2_lattice3(A_1,B_1629,'#skF_1'(A_1,B_6,k3_xboole_0(B_1629,u1_struct_0(A_1))))
      | r2_lattice3(A_1,B_6,'#skF_1'(A_1,B_6,k3_xboole_0(B_1629,u1_struct_0(A_1))))
      | r1_yellow_0(A_1,k3_xboole_0(B_1629,u1_struct_0(A_1)))
      | ~ r1_yellow_0(A_1,B_6)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_7690])).

tff(c_7707,plain,(
    ! [A_1,B_1629] :
      ( r1_yellow_0(A_1,k3_xboole_0(B_1629,u1_struct_0(A_1)))
      | ~ r1_yellow_0(A_1,B_1629)
      | ~ l1_orders_2(A_1)
      | v2_struct_0(A_1)
      | r2_lattice3(A_1,B_1629,'#skF_1'(A_1,B_1629,k3_xboole_0(B_1629,u1_struct_0(A_1)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_7694])).

tff(c_7728,plain,(
    ! [A_1634,B_1635] :
      ( r1_yellow_0(A_1634,k3_xboole_0(B_1635,u1_struct_0(A_1634)))
      | ~ r1_yellow_0(A_1634,B_1635)
      | ~ l1_orders_2(A_1634)
      | v2_struct_0(A_1634)
      | r2_lattice3(A_1634,B_1635,'#skF_1'(A_1634,B_1635,k3_xboole_0(B_1635,u1_struct_0(A_1634)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_7694])).

tff(c_7652,plain,(
    ! [A_1616,C_1617,B_1618] :
      ( ~ r2_lattice3(A_1616,C_1617,'#skF_1'(A_1616,B_1618,C_1617))
      | ~ r2_lattice3(A_1616,B_1618,'#skF_1'(A_1616,B_1618,C_1617))
      | r1_yellow_0(A_1616,C_1617)
      | ~ r1_yellow_0(A_1616,B_1618)
      | ~ l1_orders_2(A_1616)
      | v2_struct_0(A_1616) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7660,plain,(
    ! [A_17,B_1618,B_20] :
      ( ~ r2_lattice3(A_17,B_1618,'#skF_1'(A_17,B_1618,k3_xboole_0(B_20,u1_struct_0(A_17))))
      | r1_yellow_0(A_17,k3_xboole_0(B_20,u1_struct_0(A_17)))
      | ~ r1_yellow_0(A_17,B_1618)
      | ~ r2_lattice3(A_17,B_20,'#skF_1'(A_17,B_1618,k3_xboole_0(B_20,u1_struct_0(A_17))))
      | ~ m1_subset_1('#skF_1'(A_17,B_1618,k3_xboole_0(B_20,u1_struct_0(A_17))),u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_28,c_7652])).

tff(c_7737,plain,(
    ! [A_1636,B_1637] :
      ( ~ r2_lattice3(A_1636,B_1637,'#skF_1'(A_1636,B_1637,k3_xboole_0(B_1637,u1_struct_0(A_1636))))
      | ~ m1_subset_1('#skF_1'(A_1636,B_1637,k3_xboole_0(B_1637,u1_struct_0(A_1636))),u1_struct_0(A_1636))
      | r1_yellow_0(A_1636,k3_xboole_0(B_1637,u1_struct_0(A_1636)))
      | ~ r1_yellow_0(A_1636,B_1637)
      | ~ l1_orders_2(A_1636)
      | v2_struct_0(A_1636) ) ),
    inference(resolution,[status(thm)],[c_7728,c_7660])).

tff(c_7748,plain,(
    ! [A_1638,B_1639] :
      ( ~ m1_subset_1('#skF_1'(A_1638,B_1639,k3_xboole_0(B_1639,u1_struct_0(A_1638))),u1_struct_0(A_1638))
      | r1_yellow_0(A_1638,k3_xboole_0(B_1639,u1_struct_0(A_1638)))
      | ~ r1_yellow_0(A_1638,B_1639)
      | ~ l1_orders_2(A_1638)
      | v2_struct_0(A_1638) ) ),
    inference(resolution,[status(thm)],[c_7707,c_7737])).

tff(c_7759,plain,(
    ! [A_1643,B_1644] :
      ( r1_yellow_0(A_1643,k3_xboole_0(B_1644,u1_struct_0(A_1643)))
      | ~ r1_yellow_0(A_1643,B_1644)
      | ~ l1_orders_2(A_1643)
      | v2_struct_0(A_1643) ) ),
    inference(resolution,[status(thm)],[c_2,c_7748])).

tff(c_7559,plain,(
    r2_yellow_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_6224])).

tff(c_38,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_4')
    | r2_yellow_0('#skF_3','#skF_5')
    | ~ r1_yellow_0('#skF_3','#skF_6')
    | ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_7568,plain,
    ( r2_yellow_0('#skF_3','#skF_5')
    | ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6225,c_7559,c_38])).

tff(c_7569,plain,(
    ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_7568])).

tff(c_7762,plain,
    ( ~ r1_yellow_0('#skF_3','#skF_7')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_7759,c_7569])).

tff(c_7765,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7560,c_7762])).

tff(c_7767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_7765])).

tff(c_7768,plain,(
    r2_yellow_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_7568])).

tff(c_7859,plain,(
    ! [A_1672,B_1673,C_1674] :
      ( r1_lattice3(A_1672,B_1673,'#skF_2'(A_1672,B_1673,C_1674))
      | r1_lattice3(A_1672,C_1674,'#skF_2'(A_1672,B_1673,C_1674))
      | r2_yellow_0(A_1672,C_1674)
      | ~ r2_yellow_0(A_1672,B_1673)
      | ~ l1_orders_2(A_1672)
      | v2_struct_0(A_1672) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_7884,plain,(
    ! [A_1678,B_1679,B_1680] :
      ( r1_lattice3(A_1678,B_1679,'#skF_2'(A_1678,B_1680,k3_xboole_0(B_1679,u1_struct_0(A_1678))))
      | ~ m1_subset_1('#skF_2'(A_1678,B_1680,k3_xboole_0(B_1679,u1_struct_0(A_1678))),u1_struct_0(A_1678))
      | r1_lattice3(A_1678,B_1680,'#skF_2'(A_1678,B_1680,k3_xboole_0(B_1679,u1_struct_0(A_1678))))
      | r2_yellow_0(A_1678,k3_xboole_0(B_1679,u1_struct_0(A_1678)))
      | ~ r2_yellow_0(A_1678,B_1680)
      | ~ l1_orders_2(A_1678)
      | v2_struct_0(A_1678) ) ),
    inference(resolution,[status(thm)],[c_7859,c_22])).

tff(c_7888,plain,(
    ! [A_9,B_1679,B_14] :
      ( r1_lattice3(A_9,B_1679,'#skF_2'(A_9,B_14,k3_xboole_0(B_1679,u1_struct_0(A_9))))
      | r1_lattice3(A_9,B_14,'#skF_2'(A_9,B_14,k3_xboole_0(B_1679,u1_struct_0(A_9))))
      | r2_yellow_0(A_9,k3_xboole_0(B_1679,u1_struct_0(A_9)))
      | ~ r2_yellow_0(A_9,B_14)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_7884])).

tff(c_7901,plain,(
    ! [A_9,B_1679] :
      ( r2_yellow_0(A_9,k3_xboole_0(B_1679,u1_struct_0(A_9)))
      | ~ r2_yellow_0(A_9,B_1679)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9)
      | r1_lattice3(A_9,B_1679,'#skF_2'(A_9,B_1679,k3_xboole_0(B_1679,u1_struct_0(A_9)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_7888])).

tff(c_7804,plain,(
    ! [A_1663,C_1664,B_1665] :
      ( ~ r1_lattice3(A_1663,C_1664,'#skF_2'(A_1663,B_1665,C_1664))
      | ~ r1_lattice3(A_1663,B_1665,'#skF_2'(A_1663,B_1665,C_1664))
      | r2_yellow_0(A_1663,C_1664)
      | ~ r2_yellow_0(A_1663,B_1665)
      | ~ l1_orders_2(A_1663)
      | v2_struct_0(A_1663) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8132,plain,(
    ! [A_1724,B_1725,B_1726] :
      ( ~ r1_lattice3(A_1724,B_1725,'#skF_2'(A_1724,B_1725,k3_xboole_0(B_1726,u1_struct_0(A_1724))))
      | r2_yellow_0(A_1724,k3_xboole_0(B_1726,u1_struct_0(A_1724)))
      | ~ r2_yellow_0(A_1724,B_1725)
      | ~ r1_lattice3(A_1724,B_1726,'#skF_2'(A_1724,B_1725,k3_xboole_0(B_1726,u1_struct_0(A_1724))))
      | ~ m1_subset_1('#skF_2'(A_1724,B_1725,k3_xboole_0(B_1726,u1_struct_0(A_1724))),u1_struct_0(A_1724))
      | ~ l1_orders_2(A_1724)
      | v2_struct_0(A_1724) ) ),
    inference(resolution,[status(thm)],[c_24,c_7804])).

tff(c_8153,plain,(
    ! [A_1727,B_1728] :
      ( ~ r1_lattice3(A_1727,B_1728,'#skF_2'(A_1727,B_1728,k3_xboole_0(B_1728,u1_struct_0(A_1727))))
      | ~ m1_subset_1('#skF_2'(A_1727,B_1728,k3_xboole_0(B_1728,u1_struct_0(A_1727))),u1_struct_0(A_1727))
      | r2_yellow_0(A_1727,k3_xboole_0(B_1728,u1_struct_0(A_1727)))
      | ~ r2_yellow_0(A_1727,B_1728)
      | ~ l1_orders_2(A_1727)
      | v2_struct_0(A_1727) ) ),
    inference(resolution,[status(thm)],[c_7901,c_8132])).

tff(c_8164,plain,(
    ! [A_1729,B_1730] :
      ( ~ m1_subset_1('#skF_2'(A_1729,B_1730,k3_xboole_0(B_1730,u1_struct_0(A_1729))),u1_struct_0(A_1729))
      | r2_yellow_0(A_1729,k3_xboole_0(B_1730,u1_struct_0(A_1729)))
      | ~ r2_yellow_0(A_1729,B_1730)
      | ~ l1_orders_2(A_1729)
      | v2_struct_0(A_1729) ) ),
    inference(resolution,[status(thm)],[c_7901,c_8153])).

tff(c_8170,plain,(
    ! [A_1731,B_1732] :
      ( r2_yellow_0(A_1731,k3_xboole_0(B_1732,u1_struct_0(A_1731)))
      | ~ r2_yellow_0(A_1731,B_1732)
      | ~ l1_orders_2(A_1731)
      | v2_struct_0(A_1731) ) ),
    inference(resolution,[status(thm)],[c_12,c_8164])).

tff(c_7769,plain,(
    r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_7568])).

tff(c_34,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_4')
    | ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3')))
    | ~ r1_yellow_0('#skF_3','#skF_6')
    | ~ r1_yellow_0('#skF_3',k3_xboole_0('#skF_7',u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_7777,plain,(
    ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7769,c_6225,c_7559,c_34])).

tff(c_8176,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8170,c_7777])).

tff(c_8180,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7768,c_8176])).

tff(c_8182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_8180])).

tff(c_8183,plain,(
    r2_yellow_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_7558])).

tff(c_8269,plain,(
    ! [A_1754,B_1755,C_1756] :
      ( r1_lattice3(A_1754,B_1755,'#skF_2'(A_1754,B_1755,C_1756))
      | r1_lattice3(A_1754,C_1756,'#skF_2'(A_1754,B_1755,C_1756))
      | r2_yellow_0(A_1754,C_1756)
      | ~ r2_yellow_0(A_1754,B_1755)
      | ~ l1_orders_2(A_1754)
      | v2_struct_0(A_1754) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8477,plain,(
    ! [A_1802,B_1803,B_1804] :
      ( r1_lattice3(A_1802,B_1803,'#skF_2'(A_1802,B_1804,k3_xboole_0(B_1803,u1_struct_0(A_1802))))
      | ~ m1_subset_1('#skF_2'(A_1802,B_1804,k3_xboole_0(B_1803,u1_struct_0(A_1802))),u1_struct_0(A_1802))
      | r1_lattice3(A_1802,B_1804,'#skF_2'(A_1802,B_1804,k3_xboole_0(B_1803,u1_struct_0(A_1802))))
      | r2_yellow_0(A_1802,k3_xboole_0(B_1803,u1_struct_0(A_1802)))
      | ~ r2_yellow_0(A_1802,B_1804)
      | ~ l1_orders_2(A_1802)
      | v2_struct_0(A_1802) ) ),
    inference(resolution,[status(thm)],[c_8269,c_22])).

tff(c_8481,plain,(
    ! [A_9,B_1803,B_14] :
      ( r1_lattice3(A_9,B_1803,'#skF_2'(A_9,B_14,k3_xboole_0(B_1803,u1_struct_0(A_9))))
      | r1_lattice3(A_9,B_14,'#skF_2'(A_9,B_14,k3_xboole_0(B_1803,u1_struct_0(A_9))))
      | r2_yellow_0(A_9,k3_xboole_0(B_1803,u1_struct_0(A_9)))
      | ~ r2_yellow_0(A_9,B_14)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_8477])).

tff(c_8494,plain,(
    ! [A_9,B_1803] :
      ( r2_yellow_0(A_9,k3_xboole_0(B_1803,u1_struct_0(A_9)))
      | ~ r2_yellow_0(A_9,B_1803)
      | ~ l1_orders_2(A_9)
      | v2_struct_0(A_9)
      | r1_lattice3(A_9,B_1803,'#skF_2'(A_9,B_1803,k3_xboole_0(B_1803,u1_struct_0(A_9)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_8481])).

tff(c_8522,plain,(
    ! [A_1808,B_1809] :
      ( r2_yellow_0(A_1808,k3_xboole_0(B_1809,u1_struct_0(A_1808)))
      | ~ r2_yellow_0(A_1808,B_1809)
      | ~ l1_orders_2(A_1808)
      | v2_struct_0(A_1808)
      | r1_lattice3(A_1808,B_1809,'#skF_2'(A_1808,B_1809,k3_xboole_0(B_1809,u1_struct_0(A_1808)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_8481])).

tff(c_8289,plain,(
    ! [A_1760,C_1761,B_1762] :
      ( ~ r1_lattice3(A_1760,C_1761,'#skF_2'(A_1760,B_1762,C_1761))
      | ~ r1_lattice3(A_1760,B_1762,'#skF_2'(A_1760,B_1762,C_1761))
      | r2_yellow_0(A_1760,C_1761)
      | ~ r2_yellow_0(A_1760,B_1762)
      | ~ l1_orders_2(A_1760)
      | v2_struct_0(A_1760) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8297,plain,(
    ! [A_17,B_1762,B_20] :
      ( ~ r1_lattice3(A_17,B_1762,'#skF_2'(A_17,B_1762,k3_xboole_0(B_20,u1_struct_0(A_17))))
      | r2_yellow_0(A_17,k3_xboole_0(B_20,u1_struct_0(A_17)))
      | ~ r2_yellow_0(A_17,B_1762)
      | ~ r1_lattice3(A_17,B_20,'#skF_2'(A_17,B_1762,k3_xboole_0(B_20,u1_struct_0(A_17))))
      | ~ m1_subset_1('#skF_2'(A_17,B_1762,k3_xboole_0(B_20,u1_struct_0(A_17))),u1_struct_0(A_17))
      | ~ l1_orders_2(A_17)
      | v2_struct_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_24,c_8289])).

tff(c_8599,plain,(
    ! [A_1820,B_1821] :
      ( ~ r1_lattice3(A_1820,B_1821,'#skF_2'(A_1820,B_1821,k3_xboole_0(B_1821,u1_struct_0(A_1820))))
      | ~ m1_subset_1('#skF_2'(A_1820,B_1821,k3_xboole_0(B_1821,u1_struct_0(A_1820))),u1_struct_0(A_1820))
      | r2_yellow_0(A_1820,k3_xboole_0(B_1821,u1_struct_0(A_1820)))
      | ~ r2_yellow_0(A_1820,B_1821)
      | ~ l1_orders_2(A_1820)
      | v2_struct_0(A_1820) ) ),
    inference(resolution,[status(thm)],[c_8522,c_8297])).

tff(c_8626,plain,(
    ! [A_1825,B_1826] :
      ( ~ m1_subset_1('#skF_2'(A_1825,B_1826,k3_xboole_0(B_1826,u1_struct_0(A_1825))),u1_struct_0(A_1825))
      | r2_yellow_0(A_1825,k3_xboole_0(B_1826,u1_struct_0(A_1825)))
      | ~ r2_yellow_0(A_1825,B_1826)
      | ~ l1_orders_2(A_1825)
      | v2_struct_0(A_1825) ) ),
    inference(resolution,[status(thm)],[c_8494,c_8599])).

tff(c_8632,plain,(
    ! [A_1827,B_1828] :
      ( r2_yellow_0(A_1827,k3_xboole_0(B_1828,u1_struct_0(A_1827)))
      | ~ r2_yellow_0(A_1827,B_1828)
      | ~ l1_orders_2(A_1827)
      | v2_struct_0(A_1827) ) ),
    inference(resolution,[status(thm)],[c_12,c_8626])).

tff(c_50,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_4')
    | ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3')))
    | ~ r1_yellow_0('#skF_3','#skF_6')
    | r1_yellow_0('#skF_3','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_8186,plain,
    ( ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3')))
    | r1_yellow_0('#skF_3','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6225,c_7559,c_50])).

tff(c_8187,plain,(
    ~ r2_yellow_0('#skF_3',k3_xboole_0('#skF_5',u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_8186])).

tff(c_8638,plain,
    ( ~ r2_yellow_0('#skF_3','#skF_5')
    | ~ l1_orders_2('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8632,c_8187])).

tff(c_8642,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_8183,c_8638])).

tff(c_8644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_8642])).

tff(c_8645,plain,(
    r1_yellow_0('#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_8186])).

tff(c_8184,plain,(
    ~ r1_yellow_0('#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_7558])).

tff(c_8650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8645,c_8184])).

%------------------------------------------------------------------------------
