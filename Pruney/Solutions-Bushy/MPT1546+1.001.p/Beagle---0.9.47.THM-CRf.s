%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1546+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:02 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 175 expanded)
%              Number of leaves         :   23 (  75 expanded)
%              Depth                    :   13
%              Number of atoms          :  185 ( 691 expanded)
%              Number of equality atoms :   24 (  84 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v1_lattice3 > l1_orders_2 > k13_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ( v3_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( B = k13_lattice3(A,B,C)
                <=> r1_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k13_lattice3(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k13_lattice3)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k13_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_0)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_32,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_30,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_77,plain,(
    ! [A_66,C_67,B_68] :
      ( k13_lattice3(A_66,C_67,B_68) = k13_lattice3(A_66,B_68,C_67)
      | ~ m1_subset_1(C_67,u1_struct_0(A_66))
      | ~ m1_subset_1(B_68,u1_struct_0(A_66))
      | ~ l1_orders_2(A_66)
      | ~ v1_lattice3(A_66)
      | ~ v5_orders_2(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_79,plain,(
    ! [B_68] :
      ( k13_lattice3('#skF_2',B_68,'#skF_3') = k13_lattice3('#skF_2','#skF_3',B_68)
      | ~ m1_subset_1(B_68,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_77])).

tff(c_89,plain,(
    ! [B_69] :
      ( k13_lattice3('#skF_2',B_69,'#skF_3') = k13_lattice3('#skF_2','#skF_3',B_69)
      | ~ m1_subset_1(B_69,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_79])).

tff(c_98,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = k13_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_89])).

tff(c_44,plain,
    ( k13_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3'
    | r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_46,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,
    ( ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | k13_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38])).

tff(c_99,plain,(
    k13_lattice3('#skF_2','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_48])).

tff(c_36,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_49,plain,(
    ! [A_62,B_63,C_64] :
      ( r3_orders_2(A_62,B_63,B_63)
      | ~ m1_subset_1(C_64,u1_struct_0(A_62))
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l1_orders_2(A_62)
      | ~ v3_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_51,plain,(
    ! [B_63] :
      ( r3_orders_2('#skF_2',B_63,B_63)
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_49])).

tff(c_56,plain,(
    ! [B_63] :
      ( r3_orders_2('#skF_2',B_63,B_63)
      | ~ m1_subset_1(B_63,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_51])).

tff(c_60,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v1_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_67,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_63])).

tff(c_69,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_70,plain,(
    ! [B_65] :
      ( r3_orders_2('#skF_2',B_65,B_65)
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_75,plain,(
    r3_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_70])).

tff(c_140,plain,(
    ! [A_75,B_76,C_77] :
      ( r1_orders_2(A_75,B_76,C_77)
      | ~ r3_orders_2(A_75,B_76,C_77)
      | ~ m1_subset_1(C_77,u1_struct_0(A_75))
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_144,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_75,c_140])).

tff(c_151,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_28,c_144])).

tff(c_152,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_151])).

tff(c_14,plain,(
    ! [A_11,C_47,B_35,D_53] :
      ( r1_orders_2(A_11,C_47,'#skF_1'(A_11,B_35,C_47,D_53))
      | k13_lattice3(A_11,B_35,C_47) = D_53
      | ~ r1_orders_2(A_11,C_47,D_53)
      | ~ r1_orders_2(A_11,B_35,D_53)
      | ~ m1_subset_1(D_53,u1_struct_0(A_11))
      | ~ m1_subset_1(C_47,u1_struct_0(A_11))
      | ~ m1_subset_1(B_35,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11)
      | ~ v1_lattice3(A_11)
      | ~ v5_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_184,plain,(
    ! [A_93,D_94,B_95,C_96] :
      ( ~ r1_orders_2(A_93,D_94,'#skF_1'(A_93,B_95,C_96,D_94))
      | k13_lattice3(A_93,B_95,C_96) = D_94
      | ~ r1_orders_2(A_93,C_96,D_94)
      | ~ r1_orders_2(A_93,B_95,D_94)
      | ~ m1_subset_1(D_94,u1_struct_0(A_93))
      | ~ m1_subset_1(C_96,u1_struct_0(A_93))
      | ~ m1_subset_1(B_95,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93)
      | ~ v1_lattice3(A_93)
      | ~ v5_orders_2(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_239,plain,(
    ! [A_101,B_102,D_103] :
      ( k13_lattice3(A_101,B_102,D_103) = D_103
      | ~ r1_orders_2(A_101,D_103,D_103)
      | ~ r1_orders_2(A_101,B_102,D_103)
      | ~ m1_subset_1(D_103,u1_struct_0(A_101))
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101)
      | ~ v1_lattice3(A_101)
      | ~ v5_orders_2(A_101) ) ),
    inference(resolution,[status(thm)],[c_14,c_184])).

tff(c_241,plain,(
    ! [B_102] :
      ( k13_lattice3('#skF_2',B_102,'#skF_3') = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_102,'#skF_3')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_102,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_152,c_239])).

tff(c_250,plain,(
    ! [B_104] :
      ( k13_lattice3('#skF_2',B_104,'#skF_3') = '#skF_3'
      | ~ r1_orders_2('#skF_2',B_104,'#skF_3')
      | ~ m1_subset_1(B_104,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_241])).

tff(c_260,plain,
    ( k13_lattice3('#skF_2','#skF_4','#skF_3') = '#skF_3'
    | ~ r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_250])).

tff(c_269,plain,(
    k13_lattice3('#skF_2','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_260])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_269])).

tff(c_273,plain,(
    ~ r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_272,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_357,plain,(
    ! [A_117,C_118,B_119] :
      ( k13_lattice3(A_117,C_118,B_119) = k13_lattice3(A_117,B_119,C_118)
      | ~ m1_subset_1(C_118,u1_struct_0(A_117))
      | ~ m1_subset_1(B_119,u1_struct_0(A_117))
      | ~ l1_orders_2(A_117)
      | ~ v1_lattice3(A_117)
      | ~ v5_orders_2(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_359,plain,(
    ! [B_119] :
      ( k13_lattice3('#skF_2',B_119,'#skF_3') = k13_lattice3('#skF_2','#skF_3',B_119)
      | ~ m1_subset_1(B_119,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_357])).

tff(c_368,plain,(
    ! [B_120] :
      ( k13_lattice3('#skF_2',B_120,'#skF_3') = k13_lattice3('#skF_2','#skF_3',B_120)
      | ~ m1_subset_1(B_120,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_359])).

tff(c_374,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = k13_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_368])).

tff(c_378,plain,(
    k13_lattice3('#skF_2','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_374])).

tff(c_394,plain,(
    ! [A_122,B_123,C_124] :
      ( r1_orders_2(A_122,B_123,k13_lattice3(A_122,B_123,C_124))
      | ~ m1_subset_1(k13_lattice3(A_122,B_123,C_124),u1_struct_0(A_122))
      | ~ m1_subset_1(C_124,u1_struct_0(A_122))
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | ~ v1_lattice3(A_122)
      | ~ v5_orders_2(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_396,plain,
    ( r1_orders_2('#skF_2','#skF_4',k13_lattice3('#skF_2','#skF_4','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_394])).

tff(c_400,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_26,c_28,c_28,c_378,c_396])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_400])).

%------------------------------------------------------------------------------
