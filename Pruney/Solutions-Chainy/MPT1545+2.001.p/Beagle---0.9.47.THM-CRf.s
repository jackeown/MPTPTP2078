%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:00 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 551 expanded)
%              Number of leaves         :   22 ( 208 expanded)
%              Depth                    :   17
%              Number of atoms          :  406 (3313 expanded)
%              Number of equality atoms :   56 ( 350 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v2_struct_0 > v2_lattice3 > l1_orders_2 > k12_lattice3 > k11_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( v5_orders_2(A)
          & v2_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( D = k12_lattice3(A,B,C)
                    <=> ( r1_orders_2(A,D,B)
                        & r1_orders_2(A,D,C)
                        & ! [E] :
                            ( m1_subset_1(E,u1_struct_0(A))
                           => ( ( r1_orders_2(A,E,B)
                                & r1_orders_2(A,E,C) )
                             => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_0)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k11_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(c_26,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    v2_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_216,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( m1_subset_1('#skF_1'(A_119,B_120,C_121,D_122),u1_struct_0(A_119))
      | k11_lattice3(A_119,B_120,C_121) = D_122
      | ~ r1_orders_2(A_119,D_122,C_121)
      | ~ r1_orders_2(A_119,D_122,B_120)
      | ~ m1_subset_1(D_122,u1_struct_0(A_119))
      | ~ m1_subset_1(C_121,u1_struct_0(A_119))
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l1_orders_2(A_119)
      | ~ v2_lattice3(A_119)
      | ~ v5_orders_2(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_62,plain,
    ( k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5'
    | r1_orders_2('#skF_2','#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_72,plain,(
    r1_orders_2('#skF_2','#skF_5','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_52,plain,
    ( k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5'
    | r1_orders_2('#skF_2','#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_73,plain,(
    r1_orders_2('#skF_2','#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_36,plain,
    ( r1_orders_2('#skF_2','#skF_6','#skF_4')
    | ~ r1_orders_2('#skF_2','#skF_5','#skF_4')
    | ~ r1_orders_2('#skF_2','#skF_5','#skF_3')
    | k12_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_75,plain,
    ( r1_orders_2('#skF_2','#skF_6','#skF_4')
    | k12_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_73,c_36])).

tff(c_76,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_42,plain,(
    ! [E_92] :
      ( k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5'
      | r1_orders_2('#skF_2',E_92,'#skF_5')
      | ~ r1_orders_2('#skF_2',E_92,'#skF_4')
      | ~ r1_orders_2('#skF_2',E_92,'#skF_3')
      | ~ m1_subset_1(E_92,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_83,plain,(
    ! [E_92] :
      ( r1_orders_2('#skF_2',E_92,'#skF_5')
      | ~ r1_orders_2('#skF_2',E_92,'#skF_4')
      | ~ r1_orders_2('#skF_2',E_92,'#skF_3')
      | ~ m1_subset_1(E_92,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_42])).

tff(c_234,plain,(
    ! [B_120,C_121,D_122] :
      ( r1_orders_2('#skF_2','#skF_1'('#skF_2',B_120,C_121,D_122),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_120,C_121,D_122),'#skF_4')
      | ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_120,C_121,D_122),'#skF_3')
      | k11_lattice3('#skF_2',B_120,C_121) = D_122
      | ~ r1_orders_2('#skF_2',D_122,C_121)
      | ~ r1_orders_2('#skF_2',D_122,B_120)
      | ~ m1_subset_1(D_122,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_121,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_120,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_216,c_83])).

tff(c_247,plain,(
    ! [B_120,C_121,D_122] :
      ( r1_orders_2('#skF_2','#skF_1'('#skF_2',B_120,C_121,D_122),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_120,C_121,D_122),'#skF_4')
      | ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_120,C_121,D_122),'#skF_3')
      | k11_lattice3('#skF_2',B_120,C_121) = D_122
      | ~ r1_orders_2('#skF_2',D_122,C_121)
      | ~ r1_orders_2('#skF_2',D_122,B_120)
      | ~ m1_subset_1(D_122,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_121,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_120,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_234])).

tff(c_264,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v2_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_267,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_264,c_2])).

tff(c_271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_267])).

tff(c_273,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_103,plain,(
    ! [A_95,B_96,C_97] :
      ( k12_lattice3(A_95,B_96,C_97) = k11_lattice3(A_95,B_96,C_97)
      | ~ m1_subset_1(C_97,u1_struct_0(A_95))
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95)
      | ~ v2_lattice3(A_95)
      | ~ v5_orders_2(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_109,plain,(
    ! [B_96] :
      ( k12_lattice3('#skF_2',B_96,'#skF_4') = k11_lattice3('#skF_2',B_96,'#skF_4')
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_103])).

tff(c_173,plain,(
    ! [B_100] :
      ( k12_lattice3('#skF_2',B_100,'#skF_4') = k11_lattice3('#skF_2',B_100,'#skF_4')
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_109])).

tff(c_183,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = k11_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_173])).

tff(c_188,plain,(
    k11_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_76])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6,plain,(
    ! [A_2,B_26,C_38,D_44] :
      ( r1_orders_2(A_2,'#skF_1'(A_2,B_26,C_38,D_44),C_38)
      | k11_lattice3(A_2,B_26,C_38) = D_44
      | ~ r1_orders_2(A_2,D_44,C_38)
      | ~ r1_orders_2(A_2,D_44,B_26)
      | ~ m1_subset_1(D_44,u1_struct_0(A_2))
      | ~ m1_subset_1(C_38,u1_struct_0(A_2))
      | ~ m1_subset_1(B_26,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2)
      | ~ v2_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_2,B_26,C_38,D_44] :
      ( r1_orders_2(A_2,'#skF_1'(A_2,B_26,C_38,D_44),B_26)
      | k11_lattice3(A_2,B_26,C_38) = D_44
      | ~ r1_orders_2(A_2,D_44,C_38)
      | ~ r1_orders_2(A_2,D_44,B_26)
      | ~ m1_subset_1(D_44,u1_struct_0(A_2))
      | ~ m1_subset_1(C_38,u1_struct_0(A_2))
      | ~ m1_subset_1(B_26,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2)
      | ~ v2_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_443,plain,(
    ! [B_134,C_135,D_136] :
      ( r1_orders_2('#skF_2','#skF_1'('#skF_2',B_134,C_135,D_136),'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_134,C_135,D_136),'#skF_4')
      | ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_134,C_135,D_136),'#skF_3')
      | k11_lattice3('#skF_2',B_134,C_135) = D_136
      | ~ r1_orders_2('#skF_2',D_136,C_135)
      | ~ r1_orders_2('#skF_2',D_136,B_134)
      | ~ m1_subset_1(D_136,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_135,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_4,plain,(
    ! [A_2,B_26,C_38,D_44] :
      ( ~ r1_orders_2(A_2,'#skF_1'(A_2,B_26,C_38,D_44),D_44)
      | k11_lattice3(A_2,B_26,C_38) = D_44
      | ~ r1_orders_2(A_2,D_44,C_38)
      | ~ r1_orders_2(A_2,D_44,B_26)
      | ~ m1_subset_1(D_44,u1_struct_0(A_2))
      | ~ m1_subset_1(C_38,u1_struct_0(A_2))
      | ~ m1_subset_1(B_26,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2)
      | ~ v2_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_449,plain,(
    ! [B_134,C_135] :
      ( ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_134,C_135,'#skF_5'),'#skF_4')
      | ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_134,C_135,'#skF_5'),'#skF_3')
      | k11_lattice3('#skF_2',B_134,C_135) = '#skF_5'
      | ~ r1_orders_2('#skF_2','#skF_5',C_135)
      | ~ r1_orders_2('#skF_2','#skF_5',B_134)
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_135,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_443,c_4])).

tff(c_456,plain,(
    ! [B_134,C_135] :
      ( v2_struct_0('#skF_2')
      | ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_134,C_135,'#skF_5'),'#skF_4')
      | ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_134,C_135,'#skF_5'),'#skF_3')
      | k11_lattice3('#skF_2',B_134,C_135) = '#skF_5'
      | ~ r1_orders_2('#skF_2','#skF_5',C_135)
      | ~ r1_orders_2('#skF_2','#skF_5',B_134)
      | ~ m1_subset_1(C_135,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30,c_28,c_26,c_449])).

tff(c_462,plain,(
    ! [B_137,C_138] :
      ( ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_137,C_138,'#skF_5'),'#skF_4')
      | ~ r1_orders_2('#skF_2','#skF_1'('#skF_2',B_137,C_138,'#skF_5'),'#skF_3')
      | k11_lattice3('#skF_2',B_137,C_138) = '#skF_5'
      | ~ r1_orders_2('#skF_2','#skF_5',C_138)
      | ~ r1_orders_2('#skF_2','#skF_5',B_137)
      | ~ m1_subset_1(C_138,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_137,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_456])).

tff(c_470,plain,(
    ! [C_38] :
      ( ~ r1_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3',C_38,'#skF_5'),'#skF_4')
      | k11_lattice3('#skF_2','#skF_3',C_38) = '#skF_5'
      | ~ r1_orders_2('#skF_2','#skF_5',C_38)
      | ~ r1_orders_2('#skF_2','#skF_5','#skF_3')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_462])).

tff(c_477,plain,(
    ! [C_38] :
      ( ~ r1_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3',C_38,'#skF_5'),'#skF_4')
      | k11_lattice3('#skF_2','#skF_3',C_38) = '#skF_5'
      | ~ r1_orders_2('#skF_2','#skF_5',C_38)
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_20,c_72,c_470])).

tff(c_530,plain,(
    ! [C_143] :
      ( ~ r1_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3',C_143,'#skF_5'),'#skF_4')
      | k11_lattice3('#skF_2','#skF_3',C_143) = '#skF_5'
      | ~ r1_orders_2('#skF_2','#skF_5',C_143)
      | ~ m1_subset_1(C_143,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_477])).

tff(c_534,plain,
    ( k11_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5'
    | ~ r1_orders_2('#skF_2','#skF_5','#skF_4')
    | ~ r1_orders_2('#skF_2','#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v2_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_530])).

tff(c_537,plain,
    ( k11_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_72,c_73,c_534])).

tff(c_539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_188,c_537])).

tff(c_541,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_34,plain,
    ( ~ r1_orders_2('#skF_2','#skF_6','#skF_5')
    | ~ r1_orders_2('#skF_2','#skF_5','#skF_4')
    | ~ r1_orders_2('#skF_2','#skF_5','#skF_3')
    | k12_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_549,plain,(
    ~ r1_orders_2('#skF_2','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_72,c_73,c_34])).

tff(c_38,plain,
    ( r1_orders_2('#skF_2','#skF_6','#skF_3')
    | ~ r1_orders_2('#skF_2','#skF_5','#skF_4')
    | ~ r1_orders_2('#skF_2','#skF_5','#skF_3')
    | k12_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_551,plain,(
    r1_orders_2('#skF_2','#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_72,c_73,c_38])).

tff(c_540,plain,(
    r1_orders_2('#skF_2','#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_40,plain,
    ( m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ r1_orders_2('#skF_2','#skF_5','#skF_4')
    | ~ r1_orders_2('#skF_2','#skF_5','#skF_3')
    | k12_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_547,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_72,c_73,c_40])).

tff(c_725,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( m1_subset_1('#skF_1'(A_157,B_158,C_159,D_160),u1_struct_0(A_157))
      | k11_lattice3(A_157,B_158,C_159) = D_160
      | ~ r1_orders_2(A_157,D_160,C_159)
      | ~ r1_orders_2(A_157,D_160,B_158)
      | ~ m1_subset_1(D_160,u1_struct_0(A_157))
      | ~ m1_subset_1(C_159,u1_struct_0(A_157))
      | ~ m1_subset_1(B_158,u1_struct_0(A_157))
      | ~ l1_orders_2(A_157)
      | ~ v2_lattice3(A_157)
      | ~ v5_orders_2(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_555,plain,(
    ! [A_144,B_145,C_146] :
      ( k12_lattice3(A_144,B_145,C_146) = k11_lattice3(A_144,B_145,C_146)
      | ~ m1_subset_1(C_146,u1_struct_0(A_144))
      | ~ m1_subset_1(B_145,u1_struct_0(A_144))
      | ~ l1_orders_2(A_144)
      | ~ v2_lattice3(A_144)
      | ~ v5_orders_2(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_563,plain,(
    ! [B_145] :
      ( k12_lattice3('#skF_2',B_145,'#skF_4') = k11_lattice3('#skF_2',B_145,'#skF_4')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_555])).

tff(c_575,plain,(
    ! [B_145] :
      ( k12_lattice3('#skF_2',B_145,'#skF_4') = k11_lattice3('#skF_2',B_145,'#skF_4')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_563])).

tff(c_737,plain,(
    ! [B_158,C_159,D_160] :
      ( k12_lattice3('#skF_2','#skF_1'('#skF_2',B_158,C_159,D_160),'#skF_4') = k11_lattice3('#skF_2','#skF_1'('#skF_2',B_158,C_159,D_160),'#skF_4')
      | k11_lattice3('#skF_2',B_158,C_159) = D_160
      | ~ r1_orders_2('#skF_2',D_160,C_159)
      | ~ r1_orders_2('#skF_2',D_160,B_158)
      | ~ m1_subset_1(D_160,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_159,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_725,c_575])).

tff(c_752,plain,(
    ! [B_158,C_159,D_160] :
      ( k12_lattice3('#skF_2','#skF_1'('#skF_2',B_158,C_159,D_160),'#skF_4') = k11_lattice3('#skF_2','#skF_1'('#skF_2',B_158,C_159,D_160),'#skF_4')
      | k11_lattice3('#skF_2',B_158,C_159) = D_160
      | ~ r1_orders_2('#skF_2',D_160,C_159)
      | ~ r1_orders_2('#skF_2',D_160,B_158)
      | ~ m1_subset_1(D_160,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_159,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_737])).

tff(c_759,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_752])).

tff(c_762,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_759,c_2])).

tff(c_766,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_762])).

tff(c_768,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_752])).

tff(c_611,plain,(
    ! [B_148] :
      ( k12_lattice3('#skF_2',B_148,'#skF_4') = k11_lattice3('#skF_2',B_148,'#skF_4')
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_563])).

tff(c_617,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = k11_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_611])).

tff(c_626,plain,(
    k11_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_617])).

tff(c_812,plain,(
    ! [A_179,E_180,B_181,C_182] :
      ( r1_orders_2(A_179,E_180,k11_lattice3(A_179,B_181,C_182))
      | ~ r1_orders_2(A_179,E_180,C_182)
      | ~ r1_orders_2(A_179,E_180,B_181)
      | ~ m1_subset_1(E_180,u1_struct_0(A_179))
      | ~ m1_subset_1(k11_lattice3(A_179,B_181,C_182),u1_struct_0(A_179))
      | ~ m1_subset_1(C_182,u1_struct_0(A_179))
      | ~ m1_subset_1(B_181,u1_struct_0(A_179))
      | ~ l1_orders_2(A_179)
      | ~ v2_lattice3(A_179)
      | ~ v5_orders_2(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_814,plain,(
    ! [E_180] :
      ( r1_orders_2('#skF_2',E_180,k11_lattice3('#skF_2','#skF_3','#skF_4'))
      | ~ r1_orders_2('#skF_2',E_180,'#skF_4')
      | ~ r1_orders_2('#skF_2',E_180,'#skF_3')
      | ~ m1_subset_1(E_180,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_812])).

tff(c_816,plain,(
    ! [E_180] :
      ( r1_orders_2('#skF_2',E_180,'#skF_5')
      | ~ r1_orders_2('#skF_2',E_180,'#skF_4')
      | ~ r1_orders_2('#skF_2',E_180,'#skF_3')
      | ~ m1_subset_1(E_180,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_626,c_814])).

tff(c_820,plain,(
    ! [E_183] :
      ( r1_orders_2('#skF_2',E_183,'#skF_5')
      | ~ r1_orders_2('#skF_2',E_183,'#skF_4')
      | ~ r1_orders_2('#skF_2',E_183,'#skF_3')
      | ~ m1_subset_1(E_183,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_768,c_816])).

tff(c_827,plain,
    ( r1_orders_2('#skF_2','#skF_6','#skF_5')
    | ~ r1_orders_2('#skF_2','#skF_6','#skF_4')
    | ~ r1_orders_2('#skF_2','#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_547,c_820])).

tff(c_843,plain,(
    r1_orders_2('#skF_2','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_540,c_827])).

tff(c_845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_549,c_843])).

tff(c_847,plain,(
    ~ r1_orders_2('#skF_2','#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_846,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_861,plain,(
    ! [A_184,B_185,C_186] :
      ( k12_lattice3(A_184,B_185,C_186) = k11_lattice3(A_184,B_185,C_186)
      | ~ m1_subset_1(C_186,u1_struct_0(A_184))
      | ~ m1_subset_1(B_185,u1_struct_0(A_184))
      | ~ l1_orders_2(A_184)
      | ~ v2_lattice3(A_184)
      | ~ v5_orders_2(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_867,plain,(
    ! [B_185] :
      ( k12_lattice3('#skF_2',B_185,'#skF_4') = k11_lattice3('#skF_2',B_185,'#skF_4')
      | ~ m1_subset_1(B_185,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_861])).

tff(c_904,plain,(
    ! [B_188] :
      ( k12_lattice3('#skF_2',B_188,'#skF_4') = k11_lattice3('#skF_2',B_188,'#skF_4')
      | ~ m1_subset_1(B_188,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_867])).

tff(c_907,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = k11_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_904])).

tff(c_915,plain,(
    k11_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_907])).

tff(c_966,plain,(
    ! [A_193,B_194,C_195] :
      ( r1_orders_2(A_193,k11_lattice3(A_193,B_194,C_195),C_195)
      | ~ m1_subset_1(k11_lattice3(A_193,B_194,C_195),u1_struct_0(A_193))
      | ~ m1_subset_1(C_195,u1_struct_0(A_193))
      | ~ m1_subset_1(B_194,u1_struct_0(A_193))
      | ~ l1_orders_2(A_193)
      | ~ v2_lattice3(A_193)
      | ~ v5_orders_2(A_193)
      | v2_struct_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_968,plain,
    ( r1_orders_2('#skF_2',k11_lattice3('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v2_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_966])).

tff(c_970,plain,
    ( r1_orders_2('#skF_2','#skF_5','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_915,c_968])).

tff(c_971,plain,(
    v2_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_847,c_970])).

tff(c_974,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_971,c_2])).

tff(c_978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_974])).

tff(c_980,plain,(
    ~ r1_orders_2('#skF_2','#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_979,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_995,plain,(
    ! [A_196,B_197,C_198] :
      ( k12_lattice3(A_196,B_197,C_198) = k11_lattice3(A_196,B_197,C_198)
      | ~ m1_subset_1(C_198,u1_struct_0(A_196))
      | ~ m1_subset_1(B_197,u1_struct_0(A_196))
      | ~ l1_orders_2(A_196)
      | ~ v2_lattice3(A_196)
      | ~ v5_orders_2(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1001,plain,(
    ! [B_197] :
      ( k12_lattice3('#skF_2',B_197,'#skF_4') = k11_lattice3('#skF_2',B_197,'#skF_4')
      | ~ m1_subset_1(B_197,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v2_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_995])).

tff(c_1061,plain,(
    ! [B_201] :
      ( k12_lattice3('#skF_2',B_201,'#skF_4') = k11_lattice3('#skF_2',B_201,'#skF_4')
      | ~ m1_subset_1(B_201,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_1001])).

tff(c_1064,plain,(
    k12_lattice3('#skF_2','#skF_3','#skF_4') = k11_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1061])).

tff(c_1072,plain,(
    k11_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_1064])).

tff(c_1087,plain,(
    ! [A_202,B_203,C_204] :
      ( r1_orders_2(A_202,k11_lattice3(A_202,B_203,C_204),B_203)
      | ~ m1_subset_1(k11_lattice3(A_202,B_203,C_204),u1_struct_0(A_202))
      | ~ m1_subset_1(C_204,u1_struct_0(A_202))
      | ~ m1_subset_1(B_203,u1_struct_0(A_202))
      | ~ l1_orders_2(A_202)
      | ~ v2_lattice3(A_202)
      | ~ v5_orders_2(A_202)
      | v2_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1089,plain,
    ( r1_orders_2('#skF_2',k11_lattice3('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v2_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1072,c_1087])).

tff(c_1091,plain,
    ( r1_orders_2('#skF_2','#skF_5','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_1072,c_1089])).

tff(c_1092,plain,(
    v2_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_980,c_1091])).

tff(c_1095,plain,
    ( ~ v2_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1092,c_2])).

tff(c_1099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_1095])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.59  
% 3.64/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.59  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v2_struct_0 > v2_lattice3 > l1_orders_2 > k12_lattice3 > k11_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.64/1.59  
% 3.64/1.59  %Foreground sorts:
% 3.64/1.59  
% 3.64/1.59  
% 3.64/1.59  %Background operators:
% 3.64/1.59  
% 3.64/1.59  
% 3.64/1.59  %Foreground operators:
% 3.64/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.64/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.59  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.64/1.59  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 3.64/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.64/1.59  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 3.64/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.64/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.59  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.64/1.59  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.64/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.64/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.59  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.64/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.64/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.64/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.64/1.59  
% 3.64/1.62  tff(f_108, negated_conjecture, ~(![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k12_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_yellow_0)).
% 3.64/1.62  tff(f_65, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 3.64/1.62  tff(f_32, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 3.64/1.62  tff(f_77, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 3.64/1.62  tff(c_26, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.64/1.62  tff(c_28, plain, (v2_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.64/1.62  tff(c_30, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.64/1.62  tff(c_216, plain, (![A_119, B_120, C_121, D_122]: (m1_subset_1('#skF_1'(A_119, B_120, C_121, D_122), u1_struct_0(A_119)) | k11_lattice3(A_119, B_120, C_121)=D_122 | ~r1_orders_2(A_119, D_122, C_121) | ~r1_orders_2(A_119, D_122, B_120) | ~m1_subset_1(D_122, u1_struct_0(A_119)) | ~m1_subset_1(C_121, u1_struct_0(A_119)) | ~m1_subset_1(B_120, u1_struct_0(A_119)) | ~l1_orders_2(A_119) | ~v2_lattice3(A_119) | ~v5_orders_2(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.64/1.62  tff(c_62, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5' | r1_orders_2('#skF_2', '#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.64/1.62  tff(c_72, plain, (r1_orders_2('#skF_2', '#skF_5', '#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 3.64/1.62  tff(c_52, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5' | r1_orders_2('#skF_2', '#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.64/1.62  tff(c_73, plain, (r1_orders_2('#skF_2', '#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_52])).
% 3.64/1.62  tff(c_36, plain, (r1_orders_2('#skF_2', '#skF_6', '#skF_4') | ~r1_orders_2('#skF_2', '#skF_5', '#skF_4') | ~r1_orders_2('#skF_2', '#skF_5', '#skF_3') | k12_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.64/1.62  tff(c_75, plain, (r1_orders_2('#skF_2', '#skF_6', '#skF_4') | k12_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_73, c_36])).
% 3.64/1.62  tff(c_76, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_75])).
% 3.64/1.62  tff(c_42, plain, (![E_92]: (k12_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5' | r1_orders_2('#skF_2', E_92, '#skF_5') | ~r1_orders_2('#skF_2', E_92, '#skF_4') | ~r1_orders_2('#skF_2', E_92, '#skF_3') | ~m1_subset_1(E_92, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.64/1.62  tff(c_83, plain, (![E_92]: (r1_orders_2('#skF_2', E_92, '#skF_5') | ~r1_orders_2('#skF_2', E_92, '#skF_4') | ~r1_orders_2('#skF_2', E_92, '#skF_3') | ~m1_subset_1(E_92, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_76, c_42])).
% 3.64/1.62  tff(c_234, plain, (![B_120, C_121, D_122]: (r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_120, C_121, D_122), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_120, C_121, D_122), '#skF_4') | ~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_120, C_121, D_122), '#skF_3') | k11_lattice3('#skF_2', B_120, C_121)=D_122 | ~r1_orders_2('#skF_2', D_122, C_121) | ~r1_orders_2('#skF_2', D_122, B_120) | ~m1_subset_1(D_122, u1_struct_0('#skF_2')) | ~m1_subset_1(C_121, u1_struct_0('#skF_2')) | ~m1_subset_1(B_120, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_216, c_83])).
% 3.64/1.62  tff(c_247, plain, (![B_120, C_121, D_122]: (r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_120, C_121, D_122), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_120, C_121, D_122), '#skF_4') | ~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_120, C_121, D_122), '#skF_3') | k11_lattice3('#skF_2', B_120, C_121)=D_122 | ~r1_orders_2('#skF_2', D_122, C_121) | ~r1_orders_2('#skF_2', D_122, B_120) | ~m1_subset_1(D_122, u1_struct_0('#skF_2')) | ~m1_subset_1(C_121, u1_struct_0('#skF_2')) | ~m1_subset_1(B_120, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_234])).
% 3.64/1.62  tff(c_264, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_247])).
% 3.64/1.62  tff(c_2, plain, (![A_1]: (~v2_struct_0(A_1) | ~v2_lattice3(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.64/1.62  tff(c_267, plain, (~v2_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_264, c_2])).
% 3.64/1.62  tff(c_271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_267])).
% 3.64/1.62  tff(c_273, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_247])).
% 3.64/1.62  tff(c_24, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.64/1.62  tff(c_22, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.64/1.62  tff(c_103, plain, (![A_95, B_96, C_97]: (k12_lattice3(A_95, B_96, C_97)=k11_lattice3(A_95, B_96, C_97) | ~m1_subset_1(C_97, u1_struct_0(A_95)) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l1_orders_2(A_95) | ~v2_lattice3(A_95) | ~v5_orders_2(A_95))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.64/1.62  tff(c_109, plain, (![B_96]: (k12_lattice3('#skF_2', B_96, '#skF_4')=k11_lattice3('#skF_2', B_96, '#skF_4') | ~m1_subset_1(B_96, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_103])).
% 3.64/1.62  tff(c_173, plain, (![B_100]: (k12_lattice3('#skF_2', B_100, '#skF_4')=k11_lattice3('#skF_2', B_100, '#skF_4') | ~m1_subset_1(B_100, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_109])).
% 3.64/1.62  tff(c_183, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')=k11_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_173])).
% 3.64/1.62  tff(c_188, plain, (k11_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_183, c_76])).
% 3.64/1.62  tff(c_20, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.64/1.62  tff(c_6, plain, (![A_2, B_26, C_38, D_44]: (r1_orders_2(A_2, '#skF_1'(A_2, B_26, C_38, D_44), C_38) | k11_lattice3(A_2, B_26, C_38)=D_44 | ~r1_orders_2(A_2, D_44, C_38) | ~r1_orders_2(A_2, D_44, B_26) | ~m1_subset_1(D_44, u1_struct_0(A_2)) | ~m1_subset_1(C_38, u1_struct_0(A_2)) | ~m1_subset_1(B_26, u1_struct_0(A_2)) | ~l1_orders_2(A_2) | ~v2_lattice3(A_2) | ~v5_orders_2(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.64/1.62  tff(c_8, plain, (![A_2, B_26, C_38, D_44]: (r1_orders_2(A_2, '#skF_1'(A_2, B_26, C_38, D_44), B_26) | k11_lattice3(A_2, B_26, C_38)=D_44 | ~r1_orders_2(A_2, D_44, C_38) | ~r1_orders_2(A_2, D_44, B_26) | ~m1_subset_1(D_44, u1_struct_0(A_2)) | ~m1_subset_1(C_38, u1_struct_0(A_2)) | ~m1_subset_1(B_26, u1_struct_0(A_2)) | ~l1_orders_2(A_2) | ~v2_lattice3(A_2) | ~v5_orders_2(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.64/1.62  tff(c_443, plain, (![B_134, C_135, D_136]: (r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_134, C_135, D_136), '#skF_5') | ~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_134, C_135, D_136), '#skF_4') | ~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_134, C_135, D_136), '#skF_3') | k11_lattice3('#skF_2', B_134, C_135)=D_136 | ~r1_orders_2('#skF_2', D_136, C_135) | ~r1_orders_2('#skF_2', D_136, B_134) | ~m1_subset_1(D_136, u1_struct_0('#skF_2')) | ~m1_subset_1(C_135, u1_struct_0('#skF_2')) | ~m1_subset_1(B_134, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_247])).
% 3.64/1.62  tff(c_4, plain, (![A_2, B_26, C_38, D_44]: (~r1_orders_2(A_2, '#skF_1'(A_2, B_26, C_38, D_44), D_44) | k11_lattice3(A_2, B_26, C_38)=D_44 | ~r1_orders_2(A_2, D_44, C_38) | ~r1_orders_2(A_2, D_44, B_26) | ~m1_subset_1(D_44, u1_struct_0(A_2)) | ~m1_subset_1(C_38, u1_struct_0(A_2)) | ~m1_subset_1(B_26, u1_struct_0(A_2)) | ~l1_orders_2(A_2) | ~v2_lattice3(A_2) | ~v5_orders_2(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.64/1.62  tff(c_449, plain, (![B_134, C_135]: (~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_134, C_135, '#skF_5'), '#skF_4') | ~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_134, C_135, '#skF_5'), '#skF_3') | k11_lattice3('#skF_2', B_134, C_135)='#skF_5' | ~r1_orders_2('#skF_2', '#skF_5', C_135) | ~r1_orders_2('#skF_2', '#skF_5', B_134) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1(C_135, u1_struct_0('#skF_2')) | ~m1_subset_1(B_134, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_443, c_4])).
% 3.64/1.62  tff(c_456, plain, (![B_134, C_135]: (v2_struct_0('#skF_2') | ~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_134, C_135, '#skF_5'), '#skF_4') | ~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_134, C_135, '#skF_5'), '#skF_3') | k11_lattice3('#skF_2', B_134, C_135)='#skF_5' | ~r1_orders_2('#skF_2', '#skF_5', C_135) | ~r1_orders_2('#skF_2', '#skF_5', B_134) | ~m1_subset_1(C_135, u1_struct_0('#skF_2')) | ~m1_subset_1(B_134, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_30, c_28, c_26, c_449])).
% 3.64/1.62  tff(c_462, plain, (![B_137, C_138]: (~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_137, C_138, '#skF_5'), '#skF_4') | ~r1_orders_2('#skF_2', '#skF_1'('#skF_2', B_137, C_138, '#skF_5'), '#skF_3') | k11_lattice3('#skF_2', B_137, C_138)='#skF_5' | ~r1_orders_2('#skF_2', '#skF_5', C_138) | ~r1_orders_2('#skF_2', '#skF_5', B_137) | ~m1_subset_1(C_138, u1_struct_0('#skF_2')) | ~m1_subset_1(B_137, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_273, c_456])).
% 3.64/1.62  tff(c_470, plain, (![C_38]: (~r1_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', C_38, '#skF_5'), '#skF_4') | k11_lattice3('#skF_2', '#skF_3', C_38)='#skF_5' | ~r1_orders_2('#skF_2', '#skF_5', C_38) | ~r1_orders_2('#skF_2', '#skF_5', '#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1(C_38, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_462])).
% 3.64/1.62  tff(c_477, plain, (![C_38]: (~r1_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', C_38, '#skF_5'), '#skF_4') | k11_lattice3('#skF_2', '#skF_3', C_38)='#skF_5' | ~r1_orders_2('#skF_2', '#skF_5', C_38) | ~m1_subset_1(C_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_20, c_72, c_470])).
% 3.64/1.62  tff(c_530, plain, (![C_143]: (~r1_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', C_143, '#skF_5'), '#skF_4') | k11_lattice3('#skF_2', '#skF_3', C_143)='#skF_5' | ~r1_orders_2('#skF_2', '#skF_5', C_143) | ~m1_subset_1(C_143, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_273, c_477])).
% 3.64/1.62  tff(c_534, plain, (k11_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5' | ~r1_orders_2('#skF_2', '#skF_5', '#skF_4') | ~r1_orders_2('#skF_2', '#skF_5', '#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_6, c_530])).
% 3.64/1.62  tff(c_537, plain, (k11_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_72, c_73, c_534])).
% 3.64/1.62  tff(c_539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_273, c_188, c_537])).
% 3.64/1.62  tff(c_541, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_75])).
% 3.64/1.62  tff(c_34, plain, (~r1_orders_2('#skF_2', '#skF_6', '#skF_5') | ~r1_orders_2('#skF_2', '#skF_5', '#skF_4') | ~r1_orders_2('#skF_2', '#skF_5', '#skF_3') | k12_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.64/1.62  tff(c_549, plain, (~r1_orders_2('#skF_2', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_541, c_72, c_73, c_34])).
% 3.64/1.62  tff(c_38, plain, (r1_orders_2('#skF_2', '#skF_6', '#skF_3') | ~r1_orders_2('#skF_2', '#skF_5', '#skF_4') | ~r1_orders_2('#skF_2', '#skF_5', '#skF_3') | k12_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.64/1.62  tff(c_551, plain, (r1_orders_2('#skF_2', '#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_541, c_72, c_73, c_38])).
% 3.64/1.62  tff(c_540, plain, (r1_orders_2('#skF_2', '#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_75])).
% 3.64/1.62  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~r1_orders_2('#skF_2', '#skF_5', '#skF_4') | ~r1_orders_2('#skF_2', '#skF_5', '#skF_3') | k12_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.64/1.62  tff(c_547, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_541, c_72, c_73, c_40])).
% 3.64/1.62  tff(c_725, plain, (![A_157, B_158, C_159, D_160]: (m1_subset_1('#skF_1'(A_157, B_158, C_159, D_160), u1_struct_0(A_157)) | k11_lattice3(A_157, B_158, C_159)=D_160 | ~r1_orders_2(A_157, D_160, C_159) | ~r1_orders_2(A_157, D_160, B_158) | ~m1_subset_1(D_160, u1_struct_0(A_157)) | ~m1_subset_1(C_159, u1_struct_0(A_157)) | ~m1_subset_1(B_158, u1_struct_0(A_157)) | ~l1_orders_2(A_157) | ~v2_lattice3(A_157) | ~v5_orders_2(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.64/1.62  tff(c_555, plain, (![A_144, B_145, C_146]: (k12_lattice3(A_144, B_145, C_146)=k11_lattice3(A_144, B_145, C_146) | ~m1_subset_1(C_146, u1_struct_0(A_144)) | ~m1_subset_1(B_145, u1_struct_0(A_144)) | ~l1_orders_2(A_144) | ~v2_lattice3(A_144) | ~v5_orders_2(A_144))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.64/1.62  tff(c_563, plain, (![B_145]: (k12_lattice3('#skF_2', B_145, '#skF_4')=k11_lattice3('#skF_2', B_145, '#skF_4') | ~m1_subset_1(B_145, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_555])).
% 3.64/1.62  tff(c_575, plain, (![B_145]: (k12_lattice3('#skF_2', B_145, '#skF_4')=k11_lattice3('#skF_2', B_145, '#skF_4') | ~m1_subset_1(B_145, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_563])).
% 3.64/1.62  tff(c_737, plain, (![B_158, C_159, D_160]: (k12_lattice3('#skF_2', '#skF_1'('#skF_2', B_158, C_159, D_160), '#skF_4')=k11_lattice3('#skF_2', '#skF_1'('#skF_2', B_158, C_159, D_160), '#skF_4') | k11_lattice3('#skF_2', B_158, C_159)=D_160 | ~r1_orders_2('#skF_2', D_160, C_159) | ~r1_orders_2('#skF_2', D_160, B_158) | ~m1_subset_1(D_160, u1_struct_0('#skF_2')) | ~m1_subset_1(C_159, u1_struct_0('#skF_2')) | ~m1_subset_1(B_158, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_725, c_575])).
% 3.64/1.62  tff(c_752, plain, (![B_158, C_159, D_160]: (k12_lattice3('#skF_2', '#skF_1'('#skF_2', B_158, C_159, D_160), '#skF_4')=k11_lattice3('#skF_2', '#skF_1'('#skF_2', B_158, C_159, D_160), '#skF_4') | k11_lattice3('#skF_2', B_158, C_159)=D_160 | ~r1_orders_2('#skF_2', D_160, C_159) | ~r1_orders_2('#skF_2', D_160, B_158) | ~m1_subset_1(D_160, u1_struct_0('#skF_2')) | ~m1_subset_1(C_159, u1_struct_0('#skF_2')) | ~m1_subset_1(B_158, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_737])).
% 3.64/1.62  tff(c_759, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_752])).
% 3.64/1.62  tff(c_762, plain, (~v2_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_759, c_2])).
% 3.64/1.62  tff(c_766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_762])).
% 3.64/1.62  tff(c_768, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_752])).
% 3.64/1.62  tff(c_611, plain, (![B_148]: (k12_lattice3('#skF_2', B_148, '#skF_4')=k11_lattice3('#skF_2', B_148, '#skF_4') | ~m1_subset_1(B_148, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_563])).
% 3.64/1.62  tff(c_617, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')=k11_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_611])).
% 3.64/1.62  tff(c_626, plain, (k11_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_541, c_617])).
% 3.64/1.62  tff(c_812, plain, (![A_179, E_180, B_181, C_182]: (r1_orders_2(A_179, E_180, k11_lattice3(A_179, B_181, C_182)) | ~r1_orders_2(A_179, E_180, C_182) | ~r1_orders_2(A_179, E_180, B_181) | ~m1_subset_1(E_180, u1_struct_0(A_179)) | ~m1_subset_1(k11_lattice3(A_179, B_181, C_182), u1_struct_0(A_179)) | ~m1_subset_1(C_182, u1_struct_0(A_179)) | ~m1_subset_1(B_181, u1_struct_0(A_179)) | ~l1_orders_2(A_179) | ~v2_lattice3(A_179) | ~v5_orders_2(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.64/1.62  tff(c_814, plain, (![E_180]: (r1_orders_2('#skF_2', E_180, k11_lattice3('#skF_2', '#skF_3', '#skF_4')) | ~r1_orders_2('#skF_2', E_180, '#skF_4') | ~r1_orders_2('#skF_2', E_180, '#skF_3') | ~m1_subset_1(E_180, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_626, c_812])).
% 3.64/1.62  tff(c_816, plain, (![E_180]: (r1_orders_2('#skF_2', E_180, '#skF_5') | ~r1_orders_2('#skF_2', E_180, '#skF_4') | ~r1_orders_2('#skF_2', E_180, '#skF_3') | ~m1_subset_1(E_180, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_626, c_814])).
% 3.64/1.62  tff(c_820, plain, (![E_183]: (r1_orders_2('#skF_2', E_183, '#skF_5') | ~r1_orders_2('#skF_2', E_183, '#skF_4') | ~r1_orders_2('#skF_2', E_183, '#skF_3') | ~m1_subset_1(E_183, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_768, c_816])).
% 3.64/1.62  tff(c_827, plain, (r1_orders_2('#skF_2', '#skF_6', '#skF_5') | ~r1_orders_2('#skF_2', '#skF_6', '#skF_4') | ~r1_orders_2('#skF_2', '#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_547, c_820])).
% 3.64/1.62  tff(c_843, plain, (r1_orders_2('#skF_2', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_551, c_540, c_827])).
% 3.64/1.62  tff(c_845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_549, c_843])).
% 3.64/1.62  tff(c_847, plain, (~r1_orders_2('#skF_2', '#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 3.64/1.62  tff(c_846, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_52])).
% 3.64/1.62  tff(c_861, plain, (![A_184, B_185, C_186]: (k12_lattice3(A_184, B_185, C_186)=k11_lattice3(A_184, B_185, C_186) | ~m1_subset_1(C_186, u1_struct_0(A_184)) | ~m1_subset_1(B_185, u1_struct_0(A_184)) | ~l1_orders_2(A_184) | ~v2_lattice3(A_184) | ~v5_orders_2(A_184))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.64/1.62  tff(c_867, plain, (![B_185]: (k12_lattice3('#skF_2', B_185, '#skF_4')=k11_lattice3('#skF_2', B_185, '#skF_4') | ~m1_subset_1(B_185, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_861])).
% 3.64/1.62  tff(c_904, plain, (![B_188]: (k12_lattice3('#skF_2', B_188, '#skF_4')=k11_lattice3('#skF_2', B_188, '#skF_4') | ~m1_subset_1(B_188, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_867])).
% 3.64/1.62  tff(c_907, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')=k11_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_904])).
% 3.64/1.62  tff(c_915, plain, (k11_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_846, c_907])).
% 3.64/1.62  tff(c_966, plain, (![A_193, B_194, C_195]: (r1_orders_2(A_193, k11_lattice3(A_193, B_194, C_195), C_195) | ~m1_subset_1(k11_lattice3(A_193, B_194, C_195), u1_struct_0(A_193)) | ~m1_subset_1(C_195, u1_struct_0(A_193)) | ~m1_subset_1(B_194, u1_struct_0(A_193)) | ~l1_orders_2(A_193) | ~v2_lattice3(A_193) | ~v5_orders_2(A_193) | v2_struct_0(A_193))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.64/1.62  tff(c_968, plain, (r1_orders_2('#skF_2', k11_lattice3('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_915, c_966])).
% 3.64/1.62  tff(c_970, plain, (r1_orders_2('#skF_2', '#skF_5', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_915, c_968])).
% 3.64/1.62  tff(c_971, plain, (v2_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_847, c_970])).
% 3.64/1.62  tff(c_974, plain, (~v2_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_971, c_2])).
% 3.64/1.62  tff(c_978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_974])).
% 3.64/1.62  tff(c_980, plain, (~r1_orders_2('#skF_2', '#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_62])).
% 3.64/1.62  tff(c_979, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_62])).
% 3.64/1.62  tff(c_995, plain, (![A_196, B_197, C_198]: (k12_lattice3(A_196, B_197, C_198)=k11_lattice3(A_196, B_197, C_198) | ~m1_subset_1(C_198, u1_struct_0(A_196)) | ~m1_subset_1(B_197, u1_struct_0(A_196)) | ~l1_orders_2(A_196) | ~v2_lattice3(A_196) | ~v5_orders_2(A_196))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.64/1.62  tff(c_1001, plain, (![B_197]: (k12_lattice3('#skF_2', B_197, '#skF_4')=k11_lattice3('#skF_2', B_197, '#skF_4') | ~m1_subset_1(B_197, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_995])).
% 3.64/1.62  tff(c_1061, plain, (![B_201]: (k12_lattice3('#skF_2', B_201, '#skF_4')=k11_lattice3('#skF_2', B_201, '#skF_4') | ~m1_subset_1(B_201, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_1001])).
% 3.64/1.62  tff(c_1064, plain, (k12_lattice3('#skF_2', '#skF_3', '#skF_4')=k11_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_1061])).
% 3.64/1.62  tff(c_1072, plain, (k11_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_979, c_1064])).
% 3.64/1.62  tff(c_1087, plain, (![A_202, B_203, C_204]: (r1_orders_2(A_202, k11_lattice3(A_202, B_203, C_204), B_203) | ~m1_subset_1(k11_lattice3(A_202, B_203, C_204), u1_struct_0(A_202)) | ~m1_subset_1(C_204, u1_struct_0(A_202)) | ~m1_subset_1(B_203, u1_struct_0(A_202)) | ~l1_orders_2(A_202) | ~v2_lattice3(A_202) | ~v5_orders_2(A_202) | v2_struct_0(A_202))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.64/1.62  tff(c_1089, plain, (r1_orders_2('#skF_2', k11_lattice3('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v2_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1072, c_1087])).
% 3.64/1.62  tff(c_1091, plain, (r1_orders_2('#skF_2', '#skF_5', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_1072, c_1089])).
% 3.64/1.62  tff(c_1092, plain, (v2_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_980, c_1091])).
% 3.64/1.62  tff(c_1095, plain, (~v2_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_1092, c_2])).
% 3.64/1.62  tff(c_1099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_1095])).
% 3.64/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.62  
% 3.64/1.62  Inference rules
% 3.64/1.62  ----------------------
% 3.64/1.62  #Ref     : 0
% 3.64/1.62  #Sup     : 249
% 3.64/1.62  #Fact    : 0
% 3.64/1.62  #Define  : 0
% 3.64/1.62  #Split   : 10
% 3.64/1.62  #Chain   : 0
% 3.64/1.62  #Close   : 0
% 3.64/1.62  
% 3.64/1.62  Ordering : KBO
% 3.64/1.62  
% 3.64/1.62  Simplification rules
% 3.64/1.62  ----------------------
% 3.64/1.62  #Subsume      : 28
% 3.64/1.62  #Demod        : 416
% 3.64/1.62  #Tautology    : 153
% 3.64/1.62  #SimpNegUnit  : 40
% 3.64/1.62  #BackRed      : 7
% 3.64/1.62  
% 3.64/1.62  #Partial instantiations: 0
% 3.64/1.62  #Strategies tried      : 1
% 3.64/1.62  
% 3.64/1.62  Timing (in seconds)
% 3.64/1.62  ----------------------
% 3.64/1.62  Preprocessing        : 0.35
% 3.64/1.62  Parsing              : 0.17
% 3.64/1.62  CNF conversion       : 0.03
% 3.64/1.62  Main loop            : 0.50
% 3.64/1.62  Inferencing          : 0.17
% 3.64/1.62  Reduction            : 0.16
% 3.64/1.62  Demodulation         : 0.11
% 3.64/1.62  BG Simplification    : 0.03
% 3.64/1.62  Subsumption          : 0.10
% 3.64/1.62  Abstraction          : 0.03
% 3.64/1.62  MUC search           : 0.00
% 3.64/1.62  Cooper               : 0.00
% 3.64/1.62  Total                : 0.89
% 3.64/1.62  Index Insertion      : 0.00
% 3.64/1.62  Index Deletion       : 0.00
% 3.64/1.62  Index Matching       : 0.00
% 3.64/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
