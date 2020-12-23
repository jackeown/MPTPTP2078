%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:28 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 203 expanded)
%              Number of leaves         :   43 (  93 expanded)
%              Depth                    :   17
%              Number of atoms          :  162 ( 573 expanded)
%              Number of equality atoms :   32 ( 107 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_147,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_50,axiom,(
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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_106,axiom,(
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

tff(f_64,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_127,axiom,(
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

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_60,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_56,plain,(
    v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_54,plain,(
    v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_52,plain,(
    v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_100,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_108,plain,(
    ! [B_11] : k4_xboole_0(B_11,B_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_100])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_257,plain,(
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | ~ r2_hidden(C_81,B_80)
      | ~ r2_hidden(C_81,A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_289,plain,(
    ! [C_87,B_88,A_89] :
      ( ~ r2_hidden(C_87,B_88)
      | ~ r2_hidden(C_87,A_89)
      | k4_xboole_0(A_89,B_88) != A_89 ) ),
    inference(resolution,[status(thm)],[c_30,c_257])).

tff(c_521,plain,(
    ! [A_117,A_118] :
      ( ~ r2_hidden('#skF_1'(A_117),A_118)
      | k4_xboole_0(A_118,A_117) != A_118
      | v1_xboole_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_4,c_289])).

tff(c_534,plain,(
    ! [A_1] :
      ( k4_xboole_0(A_1,A_1) != A_1
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_521])).

tff(c_538,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_534])).

tff(c_273,plain,(
    ! [A_82,B_83,C_84] :
      ( k7_subset_1(A_82,B_83,C_84) = k4_xboole_0(B_83,C_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_276,plain,(
    ! [C_84] : k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',C_84) = k4_xboole_0('#skF_4',C_84) ),
    inference(resolution,[status(thm)],[c_50,c_273])).

tff(c_452,plain,(
    ! [A_109,B_110] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_109))),B_110,k1_tarski(k1_xboole_0)) = k2_yellow19(A_109,k3_yellow19(A_109,k2_struct_0(A_109),B_110))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_109)))))
      | ~ v13_waybel_0(B_110,k3_yellow_1(k2_struct_0(A_109)))
      | ~ v2_waybel_0(B_110,k3_yellow_1(k2_struct_0(A_109)))
      | v1_xboole_0(B_110)
      | ~ l1_struct_0(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_454,plain,
    ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))),'#skF_4',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4'))
    | ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | v1_xboole_0('#skF_4')
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_452])).

tff(c_457,plain,
    ( k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_52,c_276,c_454])).

tff(c_458,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) = k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_58,c_457])).

tff(c_48,plain,(
    k2_yellow19('#skF_3',k3_yellow19('#skF_3',k2_struct_0('#skF_3'),'#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_559,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_48])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    ! [A_16] : k4_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_87,plain,(
    ! [C_44,B_45] : ~ r2_hidden(C_44,k4_xboole_0(B_45,k1_tarski(C_44))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_90,plain,(
    ! [C_44] : ~ r2_hidden(C_44,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_87])).

tff(c_308,plain,(
    ! [A_91,B_92,C_93] :
      ( r2_hidden(A_91,k4_xboole_0(B_92,k1_tarski(C_93)))
      | C_93 = A_91
      | ~ r2_hidden(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_324,plain,(
    ! [A_91,C_93] :
      ( r2_hidden(A_91,k1_xboole_0)
      | C_93 = A_91
      | ~ r2_hidden(A_91,k1_tarski(C_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_308])).

tff(c_336,plain,(
    ! [C_94,A_95] :
      ( C_94 = A_95
      | ~ r2_hidden(A_95,k1_tarski(C_94)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_324])).

tff(c_359,plain,(
    ! [A_97,C_98] :
      ( '#skF_2'(A_97,k1_tarski(C_98)) = C_98
      | r1_xboole_0(A_97,k1_tarski(C_98)) ) ),
    inference(resolution,[status(thm)],[c_10,c_336])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1342,plain,(
    ! [A_169,C_170] :
      ( k4_xboole_0(A_169,k1_tarski(C_170)) = A_169
      | '#skF_2'(A_169,k1_tarski(C_170)) = C_170 ) ),
    inference(resolution,[status(thm)],[c_359,c_28])).

tff(c_1427,plain,(
    '#skF_2'('#skF_4',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1342,c_559])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1438,plain,
    ( r2_hidden(k1_xboole_0,'#skF_4')
    | r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1427,c_12])).

tff(c_1459,plain,(
    r1_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_1438])).

tff(c_1464,plain,(
    k4_xboole_0('#skF_4',k1_tarski(k1_xboole_0)) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1459,c_28])).

tff(c_1469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_559,c_1464])).

tff(c_1470,plain,(
    r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1438])).

tff(c_46,plain,(
    ! [C_36,B_34,A_30] :
      ( ~ v1_xboole_0(C_36)
      | ~ r2_hidden(C_36,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30))))
      | ~ v13_waybel_0(B_34,k3_yellow_1(A_30))
      | ~ v2_waybel_0(B_34,k3_yellow_1(A_30))
      | ~ v1_subset_1(B_34,u1_struct_0(k3_yellow_1(A_30)))
      | v1_xboole_0(B_34)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1488,plain,(
    ! [A_30] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_30))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_30))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_30)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_30) ) ),
    inference(resolution,[status(thm)],[c_1470,c_46])).

tff(c_1497,plain,(
    ! [A_30] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_30))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_30))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_30)))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_538,c_1488])).

tff(c_1548,plain,(
    ! [A_176] :
      ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_176))))
      | ~ v13_waybel_0('#skF_4',k3_yellow_1(A_176))
      | ~ v2_waybel_0('#skF_4',k3_yellow_1(A_176))
      | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(A_176)))
      | v1_xboole_0(A_176) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1497])).

tff(c_1551,plain,
    ( ~ v13_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v2_waybel_0('#skF_4',k3_yellow_1(k2_struct_0('#skF_3')))
    | ~ v1_subset_1('#skF_4',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_1548])).

tff(c_1554,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1551])).

tff(c_40,plain,(
    ! [A_25] :
      ( ~ v1_xboole_0(k2_struct_0(A_25))
      | ~ l1_struct_0(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1561,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1554,c_40])).

tff(c_1566,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1561])).

tff(c_1568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1566])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:36:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.54  
% 3.46/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.54  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 3.46/1.54  
% 3.46/1.54  %Foreground sorts:
% 3.46/1.54  
% 3.46/1.54  
% 3.46/1.54  %Background operators:
% 3.46/1.54  
% 3.46/1.54  
% 3.46/1.54  %Foreground operators:
% 3.46/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.46/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.54  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.46/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.54  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.46/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.46/1.54  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.46/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.46/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.46/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.46/1.54  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.46/1.54  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.46/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.46/1.54  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.46/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.54  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.46/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.54  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.46/1.54  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.46/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.46/1.54  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.46/1.54  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.46/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.46/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.46/1.54  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.46/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.46/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.54  
% 3.46/1.55  tff(f_147, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.46/1.55  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.46/1.55  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.46/1.55  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.46/1.55  tff(f_68, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.46/1.55  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.46/1.55  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.46/1.55  tff(f_106, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 3.46/1.55  tff(f_64, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.46/1.55  tff(f_75, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.46/1.55  tff(f_127, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 3.46/1.55  tff(f_87, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.46/1.55  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.46/1.55  tff(c_60, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.46/1.55  tff(c_56, plain, (v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.46/1.55  tff(c_54, plain, (v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.46/1.55  tff(c_52, plain, (v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.46/1.55  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.46/1.55  tff(c_58, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.46/1.55  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.46/1.55  tff(c_100, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.46/1.55  tff(c_108, plain, (![B_11]: (k4_xboole_0(B_11, B_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_100])).
% 3.46/1.55  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.55  tff(c_30, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.46/1.55  tff(c_257, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | ~r2_hidden(C_81, B_80) | ~r2_hidden(C_81, A_79))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.46/1.55  tff(c_289, plain, (![C_87, B_88, A_89]: (~r2_hidden(C_87, B_88) | ~r2_hidden(C_87, A_89) | k4_xboole_0(A_89, B_88)!=A_89)), inference(resolution, [status(thm)], [c_30, c_257])).
% 3.46/1.55  tff(c_521, plain, (![A_117, A_118]: (~r2_hidden('#skF_1'(A_117), A_118) | k4_xboole_0(A_118, A_117)!=A_118 | v1_xboole_0(A_117))), inference(resolution, [status(thm)], [c_4, c_289])).
% 3.46/1.55  tff(c_534, plain, (![A_1]: (k4_xboole_0(A_1, A_1)!=A_1 | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_521])).
% 3.46/1.55  tff(c_538, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_534])).
% 3.46/1.55  tff(c_273, plain, (![A_82, B_83, C_84]: (k7_subset_1(A_82, B_83, C_84)=k4_xboole_0(B_83, C_84) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.46/1.55  tff(c_276, plain, (![C_84]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', C_84)=k4_xboole_0('#skF_4', C_84))), inference(resolution, [status(thm)], [c_50, c_273])).
% 3.46/1.55  tff(c_452, plain, (![A_109, B_110]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_109))), B_110, k1_tarski(k1_xboole_0))=k2_yellow19(A_109, k3_yellow19(A_109, k2_struct_0(A_109), B_110)) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_109))))) | ~v13_waybel_0(B_110, k3_yellow_1(k2_struct_0(A_109))) | ~v2_waybel_0(B_110, k3_yellow_1(k2_struct_0(A_109))) | v1_xboole_0(B_110) | ~l1_struct_0(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.46/1.55  tff(c_454, plain, (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3'))), '#skF_4', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4')) | ~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | v1_xboole_0('#skF_4') | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_452])).
% 3.46/1.55  tff(c_457, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_52, c_276, c_454])).
% 3.46/1.55  tff(c_458, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))=k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_62, c_58, c_457])).
% 3.46/1.55  tff(c_48, plain, (k2_yellow19('#skF_3', k3_yellow19('#skF_3', k2_struct_0('#skF_3'), '#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.46/1.55  tff(c_559, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_458, c_48])).
% 3.46/1.55  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.46/1.55  tff(c_26, plain, (![A_16]: (k4_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.46/1.55  tff(c_87, plain, (![C_44, B_45]: (~r2_hidden(C_44, k4_xboole_0(B_45, k1_tarski(C_44))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.46/1.55  tff(c_90, plain, (![C_44]: (~r2_hidden(C_44, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_87])).
% 3.46/1.55  tff(c_308, plain, (![A_91, B_92, C_93]: (r2_hidden(A_91, k4_xboole_0(B_92, k1_tarski(C_93))) | C_93=A_91 | ~r2_hidden(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.46/1.55  tff(c_324, plain, (![A_91, C_93]: (r2_hidden(A_91, k1_xboole_0) | C_93=A_91 | ~r2_hidden(A_91, k1_tarski(C_93)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_308])).
% 3.46/1.55  tff(c_336, plain, (![C_94, A_95]: (C_94=A_95 | ~r2_hidden(A_95, k1_tarski(C_94)))), inference(negUnitSimplification, [status(thm)], [c_90, c_324])).
% 3.46/1.55  tff(c_359, plain, (![A_97, C_98]: ('#skF_2'(A_97, k1_tarski(C_98))=C_98 | r1_xboole_0(A_97, k1_tarski(C_98)))), inference(resolution, [status(thm)], [c_10, c_336])).
% 3.46/1.55  tff(c_28, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.46/1.55  tff(c_1342, plain, (![A_169, C_170]: (k4_xboole_0(A_169, k1_tarski(C_170))=A_169 | '#skF_2'(A_169, k1_tarski(C_170))=C_170)), inference(resolution, [status(thm)], [c_359, c_28])).
% 3.46/1.55  tff(c_1427, plain, ('#skF_2'('#skF_4', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1342, c_559])).
% 3.46/1.55  tff(c_12, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.46/1.55  tff(c_1438, plain, (r2_hidden(k1_xboole_0, '#skF_4') | r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1427, c_12])).
% 3.46/1.55  tff(c_1459, plain, (r1_xboole_0('#skF_4', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1438])).
% 3.46/1.55  tff(c_1464, plain, (k4_xboole_0('#skF_4', k1_tarski(k1_xboole_0))='#skF_4'), inference(resolution, [status(thm)], [c_1459, c_28])).
% 3.46/1.55  tff(c_1469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_559, c_1464])).
% 3.46/1.55  tff(c_1470, plain, (r2_hidden(k1_xboole_0, '#skF_4')), inference(splitRight, [status(thm)], [c_1438])).
% 3.46/1.55  tff(c_46, plain, (![C_36, B_34, A_30]: (~v1_xboole_0(C_36) | ~r2_hidden(C_36, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30)))) | ~v13_waybel_0(B_34, k3_yellow_1(A_30)) | ~v2_waybel_0(B_34, k3_yellow_1(A_30)) | ~v1_subset_1(B_34, u1_struct_0(k3_yellow_1(A_30))) | v1_xboole_0(B_34) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.46/1.55  tff(c_1488, plain, (![A_30]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_30)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_30)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_30))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_30))), inference(resolution, [status(thm)], [c_1470, c_46])).
% 3.46/1.55  tff(c_1497, plain, (![A_30]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_30)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_30)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_30))) | v1_xboole_0('#skF_4') | v1_xboole_0(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_538, c_1488])).
% 3.46/1.55  tff(c_1548, plain, (![A_176]: (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_176)))) | ~v13_waybel_0('#skF_4', k3_yellow_1(A_176)) | ~v2_waybel_0('#skF_4', k3_yellow_1(A_176)) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(A_176))) | v1_xboole_0(A_176))), inference(negUnitSimplification, [status(thm)], [c_58, c_1497])).
% 3.46/1.55  tff(c_1551, plain, (~v13_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v2_waybel_0('#skF_4', k3_yellow_1(k2_struct_0('#skF_3'))) | ~v1_subset_1('#skF_4', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_3')))) | v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_1548])).
% 3.46/1.55  tff(c_1554, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1551])).
% 3.46/1.55  tff(c_40, plain, (![A_25]: (~v1_xboole_0(k2_struct_0(A_25)) | ~l1_struct_0(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.46/1.55  tff(c_1561, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1554, c_40])).
% 3.46/1.55  tff(c_1566, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1561])).
% 3.46/1.55  tff(c_1568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1566])).
% 3.46/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.55  
% 3.46/1.55  Inference rules
% 3.46/1.55  ----------------------
% 3.46/1.55  #Ref     : 0
% 3.46/1.55  #Sup     : 359
% 3.46/1.55  #Fact    : 0
% 3.46/1.55  #Define  : 0
% 3.46/1.55  #Split   : 4
% 3.46/1.55  #Chain   : 0
% 3.46/1.55  #Close   : 0
% 3.46/1.55  
% 3.46/1.55  Ordering : KBO
% 3.46/1.55  
% 3.46/1.55  Simplification rules
% 3.46/1.55  ----------------------
% 3.46/1.55  #Subsume      : 85
% 3.46/1.55  #Demod        : 75
% 3.46/1.55  #Tautology    : 140
% 3.46/1.55  #SimpNegUnit  : 17
% 3.46/1.55  #BackRed      : 2
% 3.46/1.55  
% 3.46/1.55  #Partial instantiations: 0
% 3.46/1.55  #Strategies tried      : 1
% 3.46/1.55  
% 3.46/1.55  Timing (in seconds)
% 3.46/1.55  ----------------------
% 3.46/1.56  Preprocessing        : 0.33
% 3.46/1.56  Parsing              : 0.17
% 3.46/1.56  CNF conversion       : 0.02
% 3.46/1.56  Main loop            : 0.47
% 3.46/1.56  Inferencing          : 0.17
% 3.46/1.56  Reduction            : 0.14
% 3.46/1.56  Demodulation         : 0.09
% 3.46/1.56  BG Simplification    : 0.03
% 3.46/1.56  Subsumption          : 0.09
% 3.46/1.56  Abstraction          : 0.03
% 3.46/1.56  MUC search           : 0.00
% 3.46/1.56  Cooper               : 0.00
% 3.46/1.56  Total                : 0.84
% 3.46/1.56  Index Insertion      : 0.00
% 3.46/1.56  Index Deletion       : 0.00
% 3.46/1.56  Index Matching       : 0.00
% 3.46/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
