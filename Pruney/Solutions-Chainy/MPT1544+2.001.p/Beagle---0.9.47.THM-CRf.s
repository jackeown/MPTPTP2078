%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:00 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
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
%$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v2_struct_0 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
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

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k10_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(c_26,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_216,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( m1_subset_1('#skF_1'(A_119,B_120,C_121,D_122),u1_struct_0(A_119))
      | k10_lattice3(A_119,B_120,C_121) = D_122
      | ~ r1_orders_2(A_119,C_121,D_122)
      | ~ r1_orders_2(A_119,B_120,D_122)
      | ~ m1_subset_1(D_122,u1_struct_0(A_119))
      | ~ m1_subset_1(C_121,u1_struct_0(A_119))
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l1_orders_2(A_119)
      | ~ v1_lattice3(A_119)
      | ~ v5_orders_2(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_62,plain,
    ( k13_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5'
    | r1_orders_2('#skF_2','#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_72,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_52,plain,
    ( k13_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5'
    | r1_orders_2('#skF_2','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_73,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_36,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_6')
    | ~ r1_orders_2('#skF_2','#skF_4','#skF_5')
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_5')
    | k13_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_75,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_6')
    | k13_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_73,c_36])).

tff(c_76,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_42,plain,(
    ! [E_92] :
      ( k13_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5'
      | r1_orders_2('#skF_2','#skF_5',E_92)
      | ~ r1_orders_2('#skF_2','#skF_4',E_92)
      | ~ r1_orders_2('#skF_2','#skF_3',E_92)
      | ~ m1_subset_1(E_92,u1_struct_0('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_83,plain,(
    ! [E_92] :
      ( r1_orders_2('#skF_2','#skF_5',E_92)
      | ~ r1_orders_2('#skF_2','#skF_4',E_92)
      | ~ r1_orders_2('#skF_2','#skF_3',E_92)
      | ~ m1_subset_1(E_92,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_42])).

tff(c_234,plain,(
    ! [B_120,C_121,D_122] :
      ( r1_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2',B_120,C_121,D_122))
      | ~ r1_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2',B_120,C_121,D_122))
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_120,C_121,D_122))
      | k10_lattice3('#skF_2',B_120,C_121) = D_122
      | ~ r1_orders_2('#skF_2',C_121,D_122)
      | ~ r1_orders_2('#skF_2',B_120,D_122)
      | ~ m1_subset_1(D_122,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_121,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_120,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_216,c_83])).

tff(c_247,plain,(
    ! [B_120,C_121,D_122] :
      ( r1_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2',B_120,C_121,D_122))
      | ~ r1_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2',B_120,C_121,D_122))
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_120,C_121,D_122))
      | k10_lattice3('#skF_2',B_120,C_121) = D_122
      | ~ r1_orders_2('#skF_2',C_121,D_122)
      | ~ r1_orders_2('#skF_2',B_120,D_122)
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
      | ~ v1_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_267,plain,
    ( ~ v1_lattice3('#skF_2')
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
      ( k13_lattice3(A_95,B_96,C_97) = k10_lattice3(A_95,B_96,C_97)
      | ~ m1_subset_1(C_97,u1_struct_0(A_95))
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95)
      | ~ v1_lattice3(A_95)
      | ~ v5_orders_2(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_109,plain,(
    ! [B_96] :
      ( k13_lattice3('#skF_2',B_96,'#skF_4') = k10_lattice3('#skF_2',B_96,'#skF_4')
      | ~ m1_subset_1(B_96,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_103])).

tff(c_173,plain,(
    ! [B_100] :
      ( k13_lattice3('#skF_2',B_100,'#skF_4') = k10_lattice3('#skF_2',B_100,'#skF_4')
      | ~ m1_subset_1(B_100,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_109])).

tff(c_183,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = k10_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_173])).

tff(c_188,plain,(
    k10_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_76])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6,plain,(
    ! [A_2,C_38,B_26,D_44] :
      ( r1_orders_2(A_2,C_38,'#skF_1'(A_2,B_26,C_38,D_44))
      | k10_lattice3(A_2,B_26,C_38) = D_44
      | ~ r1_orders_2(A_2,C_38,D_44)
      | ~ r1_orders_2(A_2,B_26,D_44)
      | ~ m1_subset_1(D_44,u1_struct_0(A_2))
      | ~ m1_subset_1(C_38,u1_struct_0(A_2))
      | ~ m1_subset_1(B_26,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2)
      | ~ v1_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_2,B_26,C_38,D_44] :
      ( r1_orders_2(A_2,B_26,'#skF_1'(A_2,B_26,C_38,D_44))
      | k10_lattice3(A_2,B_26,C_38) = D_44
      | ~ r1_orders_2(A_2,C_38,D_44)
      | ~ r1_orders_2(A_2,B_26,D_44)
      | ~ m1_subset_1(D_44,u1_struct_0(A_2))
      | ~ m1_subset_1(C_38,u1_struct_0(A_2))
      | ~ m1_subset_1(B_26,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2)
      | ~ v1_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_443,plain,(
    ! [B_134,C_135,D_136] :
      ( r1_orders_2('#skF_2','#skF_5','#skF_1'('#skF_2',B_134,C_135,D_136))
      | ~ r1_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2',B_134,C_135,D_136))
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_134,C_135,D_136))
      | k10_lattice3('#skF_2',B_134,C_135) = D_136
      | ~ r1_orders_2('#skF_2',C_135,D_136)
      | ~ r1_orders_2('#skF_2',B_134,D_136)
      | ~ m1_subset_1(D_136,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_135,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_4,plain,(
    ! [A_2,D_44,B_26,C_38] :
      ( ~ r1_orders_2(A_2,D_44,'#skF_1'(A_2,B_26,C_38,D_44))
      | k10_lattice3(A_2,B_26,C_38) = D_44
      | ~ r1_orders_2(A_2,C_38,D_44)
      | ~ r1_orders_2(A_2,B_26,D_44)
      | ~ m1_subset_1(D_44,u1_struct_0(A_2))
      | ~ m1_subset_1(C_38,u1_struct_0(A_2))
      | ~ m1_subset_1(B_26,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2)
      | ~ v1_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_449,plain,(
    ! [B_134,C_135] :
      ( ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2',B_134,C_135,'#skF_5'))
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_134,C_135,'#skF_5'))
      | k10_lattice3('#skF_2',B_134,C_135) = '#skF_5'
      | ~ r1_orders_2('#skF_2',C_135,'#skF_5')
      | ~ r1_orders_2('#skF_2',B_134,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_135,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_443,c_4])).

tff(c_456,plain,(
    ! [B_134,C_135] :
      ( v2_struct_0('#skF_2')
      | ~ r1_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2',B_134,C_135,'#skF_5'))
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_134,C_135,'#skF_5'))
      | k10_lattice3('#skF_2',B_134,C_135) = '#skF_5'
      | ~ r1_orders_2('#skF_2',C_135,'#skF_5')
      | ~ r1_orders_2('#skF_2',B_134,'#skF_5')
      | ~ m1_subset_1(C_135,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_134,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30,c_28,c_26,c_449])).

tff(c_462,plain,(
    ! [B_137,C_138] :
      ( ~ r1_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2',B_137,C_138,'#skF_5'))
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2',B_137,C_138,'#skF_5'))
      | k10_lattice3('#skF_2',B_137,C_138) = '#skF_5'
      | ~ r1_orders_2('#skF_2',C_138,'#skF_5')
      | ~ r1_orders_2('#skF_2',B_137,'#skF_5')
      | ~ m1_subset_1(C_138,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_137,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_456])).

tff(c_470,plain,(
    ! [C_38] :
      ( ~ r1_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_3',C_38,'#skF_5'))
      | k10_lattice3('#skF_2','#skF_3',C_38) = '#skF_5'
      | ~ r1_orders_2('#skF_2',C_38,'#skF_5')
      | ~ r1_orders_2('#skF_2','#skF_3','#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_462])).

tff(c_477,plain,(
    ! [C_38] :
      ( ~ r1_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_3',C_38,'#skF_5'))
      | k10_lattice3('#skF_2','#skF_3',C_38) = '#skF_5'
      | ~ r1_orders_2('#skF_2',C_38,'#skF_5')
      | ~ m1_subset_1(C_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_20,c_72,c_470])).

tff(c_530,plain,(
    ! [C_143] :
      ( ~ r1_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_3',C_143,'#skF_5'))
      | k10_lattice3('#skF_2','#skF_3',C_143) = '#skF_5'
      | ~ r1_orders_2('#skF_2',C_143,'#skF_5')
      | ~ m1_subset_1(C_143,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_477])).

tff(c_534,plain,
    ( k10_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5'
    | ~ r1_orders_2('#skF_2','#skF_4','#skF_5')
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_530])).

tff(c_537,plain,
    ( k10_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_72,c_73,c_534])).

tff(c_539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_273,c_188,c_537])).

tff(c_541,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_34,plain,
    ( ~ r1_orders_2('#skF_2','#skF_5','#skF_6')
    | ~ r1_orders_2('#skF_2','#skF_4','#skF_5')
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_5')
    | k13_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_549,plain,(
    ~ r1_orders_2('#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_72,c_73,c_34])).

tff(c_38,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_6')
    | ~ r1_orders_2('#skF_2','#skF_4','#skF_5')
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_5')
    | k13_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_551,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_72,c_73,c_38])).

tff(c_540,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_40,plain,
    ( m1_subset_1('#skF_6',u1_struct_0('#skF_2'))
    | ~ r1_orders_2('#skF_2','#skF_4','#skF_5')
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_5')
    | k13_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_547,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_72,c_73,c_40])).

tff(c_725,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( m1_subset_1('#skF_1'(A_157,B_158,C_159,D_160),u1_struct_0(A_157))
      | k10_lattice3(A_157,B_158,C_159) = D_160
      | ~ r1_orders_2(A_157,C_159,D_160)
      | ~ r1_orders_2(A_157,B_158,D_160)
      | ~ m1_subset_1(D_160,u1_struct_0(A_157))
      | ~ m1_subset_1(C_159,u1_struct_0(A_157))
      | ~ m1_subset_1(B_158,u1_struct_0(A_157))
      | ~ l1_orders_2(A_157)
      | ~ v1_lattice3(A_157)
      | ~ v5_orders_2(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_555,plain,(
    ! [A_144,B_145,C_146] :
      ( k13_lattice3(A_144,B_145,C_146) = k10_lattice3(A_144,B_145,C_146)
      | ~ m1_subset_1(C_146,u1_struct_0(A_144))
      | ~ m1_subset_1(B_145,u1_struct_0(A_144))
      | ~ l1_orders_2(A_144)
      | ~ v1_lattice3(A_144)
      | ~ v5_orders_2(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_563,plain,(
    ! [B_145] :
      ( k13_lattice3('#skF_2',B_145,'#skF_4') = k10_lattice3('#skF_2',B_145,'#skF_4')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_555])).

tff(c_575,plain,(
    ! [B_145] :
      ( k13_lattice3('#skF_2',B_145,'#skF_4') = k10_lattice3('#skF_2',B_145,'#skF_4')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_563])).

tff(c_737,plain,(
    ! [B_158,C_159,D_160] :
      ( k13_lattice3('#skF_2','#skF_1'('#skF_2',B_158,C_159,D_160),'#skF_4') = k10_lattice3('#skF_2','#skF_1'('#skF_2',B_158,C_159,D_160),'#skF_4')
      | k10_lattice3('#skF_2',B_158,C_159) = D_160
      | ~ r1_orders_2('#skF_2',C_159,D_160)
      | ~ r1_orders_2('#skF_2',B_158,D_160)
      | ~ m1_subset_1(D_160,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_159,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_725,c_575])).

tff(c_752,plain,(
    ! [B_158,C_159,D_160] :
      ( k13_lattice3('#skF_2','#skF_1'('#skF_2',B_158,C_159,D_160),'#skF_4') = k10_lattice3('#skF_2','#skF_1'('#skF_2',B_158,C_159,D_160),'#skF_4')
      | k10_lattice3('#skF_2',B_158,C_159) = D_160
      | ~ r1_orders_2('#skF_2',C_159,D_160)
      | ~ r1_orders_2('#skF_2',B_158,D_160)
      | ~ m1_subset_1(D_160,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(C_159,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_158,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_737])).

tff(c_759,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_752])).

tff(c_762,plain,
    ( ~ v1_lattice3('#skF_2')
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
      ( k13_lattice3('#skF_2',B_148,'#skF_4') = k10_lattice3('#skF_2',B_148,'#skF_4')
      | ~ m1_subset_1(B_148,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_563])).

tff(c_617,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = k10_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_611])).

tff(c_626,plain,(
    k10_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_617])).

tff(c_812,plain,(
    ! [A_179,B_180,C_181,E_182] :
      ( r1_orders_2(A_179,k10_lattice3(A_179,B_180,C_181),E_182)
      | ~ r1_orders_2(A_179,C_181,E_182)
      | ~ r1_orders_2(A_179,B_180,E_182)
      | ~ m1_subset_1(E_182,u1_struct_0(A_179))
      | ~ m1_subset_1(k10_lattice3(A_179,B_180,C_181),u1_struct_0(A_179))
      | ~ m1_subset_1(C_181,u1_struct_0(A_179))
      | ~ m1_subset_1(B_180,u1_struct_0(A_179))
      | ~ l1_orders_2(A_179)
      | ~ v1_lattice3(A_179)
      | ~ v5_orders_2(A_179)
      | v2_struct_0(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_814,plain,(
    ! [E_182] :
      ( r1_orders_2('#skF_2',k10_lattice3('#skF_2','#skF_3','#skF_4'),E_182)
      | ~ r1_orders_2('#skF_2','#skF_4',E_182)
      | ~ r1_orders_2('#skF_2','#skF_3',E_182)
      | ~ m1_subset_1(E_182,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_812])).

tff(c_816,plain,(
    ! [E_182] :
      ( r1_orders_2('#skF_2','#skF_5',E_182)
      | ~ r1_orders_2('#skF_2','#skF_4',E_182)
      | ~ r1_orders_2('#skF_2','#skF_3',E_182)
      | ~ m1_subset_1(E_182,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_626,c_814])).

tff(c_820,plain,(
    ! [E_183] :
      ( r1_orders_2('#skF_2','#skF_5',E_183)
      | ~ r1_orders_2('#skF_2','#skF_4',E_183)
      | ~ r1_orders_2('#skF_2','#skF_3',E_183)
      | ~ m1_subset_1(E_183,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_768,c_816])).

tff(c_827,plain,
    ( r1_orders_2('#skF_2','#skF_5','#skF_6')
    | ~ r1_orders_2('#skF_2','#skF_4','#skF_6')
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_547,c_820])).

tff(c_843,plain,(
    r1_orders_2('#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_540,c_827])).

tff(c_845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_549,c_843])).

tff(c_847,plain,(
    ~ r1_orders_2('#skF_2','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_846,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_861,plain,(
    ! [A_184,B_185,C_186] :
      ( k13_lattice3(A_184,B_185,C_186) = k10_lattice3(A_184,B_185,C_186)
      | ~ m1_subset_1(C_186,u1_struct_0(A_184))
      | ~ m1_subset_1(B_185,u1_struct_0(A_184))
      | ~ l1_orders_2(A_184)
      | ~ v1_lattice3(A_184)
      | ~ v5_orders_2(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_867,plain,(
    ! [B_185] :
      ( k13_lattice3('#skF_2',B_185,'#skF_4') = k10_lattice3('#skF_2',B_185,'#skF_4')
      | ~ m1_subset_1(B_185,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_861])).

tff(c_904,plain,(
    ! [B_188] :
      ( k13_lattice3('#skF_2',B_188,'#skF_4') = k10_lattice3('#skF_2',B_188,'#skF_4')
      | ~ m1_subset_1(B_188,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_867])).

tff(c_907,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = k10_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_904])).

tff(c_915,plain,(
    k10_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_907])).

tff(c_966,plain,(
    ! [A_193,C_194,B_195] :
      ( r1_orders_2(A_193,C_194,k10_lattice3(A_193,B_195,C_194))
      | ~ m1_subset_1(k10_lattice3(A_193,B_195,C_194),u1_struct_0(A_193))
      | ~ m1_subset_1(C_194,u1_struct_0(A_193))
      | ~ m1_subset_1(B_195,u1_struct_0(A_193))
      | ~ l1_orders_2(A_193)
      | ~ v1_lattice3(A_193)
      | ~ v5_orders_2(A_193)
      | v2_struct_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_968,plain,
    ( r1_orders_2('#skF_2','#skF_4',k10_lattice3('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_966])).

tff(c_970,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_915,c_968])).

tff(c_971,plain,(
    v2_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_847,c_970])).

tff(c_974,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_971,c_2])).

tff(c_978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_974])).

tff(c_980,plain,(
    ~ r1_orders_2('#skF_2','#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_979,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_995,plain,(
    ! [A_196,B_197,C_198] :
      ( k13_lattice3(A_196,B_197,C_198) = k10_lattice3(A_196,B_197,C_198)
      | ~ m1_subset_1(C_198,u1_struct_0(A_196))
      | ~ m1_subset_1(B_197,u1_struct_0(A_196))
      | ~ l1_orders_2(A_196)
      | ~ v1_lattice3(A_196)
      | ~ v5_orders_2(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1001,plain,(
    ! [B_197] :
      ( k13_lattice3('#skF_2',B_197,'#skF_4') = k10_lattice3('#skF_2',B_197,'#skF_4')
      | ~ m1_subset_1(B_197,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_995])).

tff(c_1061,plain,(
    ! [B_201] :
      ( k13_lattice3('#skF_2',B_201,'#skF_4') = k10_lattice3('#skF_2',B_201,'#skF_4')
      | ~ m1_subset_1(B_201,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_1001])).

tff(c_1064,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = k10_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1061])).

tff(c_1072,plain,(
    k10_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_1064])).

tff(c_1087,plain,(
    ! [A_202,B_203,C_204] :
      ( r1_orders_2(A_202,B_203,k10_lattice3(A_202,B_203,C_204))
      | ~ m1_subset_1(k10_lattice3(A_202,B_203,C_204),u1_struct_0(A_202))
      | ~ m1_subset_1(C_204,u1_struct_0(A_202))
      | ~ m1_subset_1(B_203,u1_struct_0(A_202))
      | ~ l1_orders_2(A_202)
      | ~ v1_lattice3(A_202)
      | ~ v5_orders_2(A_202)
      | v2_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1089,plain,
    ( r1_orders_2('#skF_2','#skF_3',k10_lattice3('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1072,c_1087])).

tff(c_1091,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_20,c_1072,c_1089])).

tff(c_1092,plain,(
    v2_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_980,c_1091])).

tff(c_1095,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_1092,c_2])).

tff(c_1099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_1095])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:06:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.48  
% 3.31/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.48  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v2_struct_0 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.31/1.48  
% 3.31/1.48  %Foreground sorts:
% 3.31/1.48  
% 3.31/1.48  
% 3.31/1.48  %Background operators:
% 3.31/1.48  
% 3.31/1.48  
% 3.31/1.48  %Foreground operators:
% 3.31/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.31/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.48  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 3.31/1.48  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.31/1.48  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 3.31/1.48  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 3.31/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.31/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.31/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.31/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.48  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.31/1.48  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.31/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.31/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.31/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.31/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.48  
% 3.31/1.51  tff(f_108, negated_conjecture, ~(![A]: (((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k13_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_yellow_0)).
% 3.31/1.51  tff(f_65, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l26_lattice3)).
% 3.31/1.51  tff(f_32, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 3.31/1.51  tff(f_77, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 3.31/1.51  tff(c_26, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.51  tff(c_28, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.51  tff(c_30, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.51  tff(c_216, plain, (![A_119, B_120, C_121, D_122]: (m1_subset_1('#skF_1'(A_119, B_120, C_121, D_122), u1_struct_0(A_119)) | k10_lattice3(A_119, B_120, C_121)=D_122 | ~r1_orders_2(A_119, C_121, D_122) | ~r1_orders_2(A_119, B_120, D_122) | ~m1_subset_1(D_122, u1_struct_0(A_119)) | ~m1_subset_1(C_121, u1_struct_0(A_119)) | ~m1_subset_1(B_120, u1_struct_0(A_119)) | ~l1_orders_2(A_119) | ~v1_lattice3(A_119) | ~v5_orders_2(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.51  tff(c_62, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5' | r1_orders_2('#skF_2', '#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.51  tff(c_72, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_62])).
% 3.31/1.51  tff(c_52, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5' | r1_orders_2('#skF_2', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.51  tff(c_73, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_52])).
% 3.31/1.51  tff(c_36, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_6') | ~r1_orders_2('#skF_2', '#skF_4', '#skF_5') | ~r1_orders_2('#skF_2', '#skF_3', '#skF_5') | k13_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.51  tff(c_75, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_6') | k13_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_73, c_36])).
% 3.31/1.51  tff(c_76, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(splitLeft, [status(thm)], [c_75])).
% 3.31/1.51  tff(c_42, plain, (![E_92]: (k13_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5' | r1_orders_2('#skF_2', '#skF_5', E_92) | ~r1_orders_2('#skF_2', '#skF_4', E_92) | ~r1_orders_2('#skF_2', '#skF_3', E_92) | ~m1_subset_1(E_92, u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.51  tff(c_83, plain, (![E_92]: (r1_orders_2('#skF_2', '#skF_5', E_92) | ~r1_orders_2('#skF_2', '#skF_4', E_92) | ~r1_orders_2('#skF_2', '#skF_3', E_92) | ~m1_subset_1(E_92, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_76, c_42])).
% 3.31/1.51  tff(c_234, plain, (![B_120, C_121, D_122]: (r1_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', B_120, C_121, D_122)) | ~r1_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', B_120, C_121, D_122)) | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', B_120, C_121, D_122)) | k10_lattice3('#skF_2', B_120, C_121)=D_122 | ~r1_orders_2('#skF_2', C_121, D_122) | ~r1_orders_2('#skF_2', B_120, D_122) | ~m1_subset_1(D_122, u1_struct_0('#skF_2')) | ~m1_subset_1(C_121, u1_struct_0('#skF_2')) | ~m1_subset_1(B_120, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_216, c_83])).
% 3.31/1.51  tff(c_247, plain, (![B_120, C_121, D_122]: (r1_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', B_120, C_121, D_122)) | ~r1_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', B_120, C_121, D_122)) | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', B_120, C_121, D_122)) | k10_lattice3('#skF_2', B_120, C_121)=D_122 | ~r1_orders_2('#skF_2', C_121, D_122) | ~r1_orders_2('#skF_2', B_120, D_122) | ~m1_subset_1(D_122, u1_struct_0('#skF_2')) | ~m1_subset_1(C_121, u1_struct_0('#skF_2')) | ~m1_subset_1(B_120, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_234])).
% 3.31/1.51  tff(c_264, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_247])).
% 3.31/1.51  tff(c_2, plain, (![A_1]: (~v2_struct_0(A_1) | ~v1_lattice3(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.51  tff(c_267, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_264, c_2])).
% 3.31/1.51  tff(c_271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_267])).
% 3.31/1.51  tff(c_273, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_247])).
% 3.31/1.51  tff(c_24, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.51  tff(c_22, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.51  tff(c_103, plain, (![A_95, B_96, C_97]: (k13_lattice3(A_95, B_96, C_97)=k10_lattice3(A_95, B_96, C_97) | ~m1_subset_1(C_97, u1_struct_0(A_95)) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l1_orders_2(A_95) | ~v1_lattice3(A_95) | ~v5_orders_2(A_95))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.31/1.51  tff(c_109, plain, (![B_96]: (k13_lattice3('#skF_2', B_96, '#skF_4')=k10_lattice3('#skF_2', B_96, '#skF_4') | ~m1_subset_1(B_96, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_103])).
% 3.31/1.51  tff(c_173, plain, (![B_100]: (k13_lattice3('#skF_2', B_100, '#skF_4')=k10_lattice3('#skF_2', B_100, '#skF_4') | ~m1_subset_1(B_100, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_109])).
% 3.31/1.51  tff(c_183, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')=k10_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_173])).
% 3.31/1.51  tff(c_188, plain, (k10_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_183, c_76])).
% 3.31/1.51  tff(c_20, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.51  tff(c_6, plain, (![A_2, C_38, B_26, D_44]: (r1_orders_2(A_2, C_38, '#skF_1'(A_2, B_26, C_38, D_44)) | k10_lattice3(A_2, B_26, C_38)=D_44 | ~r1_orders_2(A_2, C_38, D_44) | ~r1_orders_2(A_2, B_26, D_44) | ~m1_subset_1(D_44, u1_struct_0(A_2)) | ~m1_subset_1(C_38, u1_struct_0(A_2)) | ~m1_subset_1(B_26, u1_struct_0(A_2)) | ~l1_orders_2(A_2) | ~v1_lattice3(A_2) | ~v5_orders_2(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.51  tff(c_8, plain, (![A_2, B_26, C_38, D_44]: (r1_orders_2(A_2, B_26, '#skF_1'(A_2, B_26, C_38, D_44)) | k10_lattice3(A_2, B_26, C_38)=D_44 | ~r1_orders_2(A_2, C_38, D_44) | ~r1_orders_2(A_2, B_26, D_44) | ~m1_subset_1(D_44, u1_struct_0(A_2)) | ~m1_subset_1(C_38, u1_struct_0(A_2)) | ~m1_subset_1(B_26, u1_struct_0(A_2)) | ~l1_orders_2(A_2) | ~v1_lattice3(A_2) | ~v5_orders_2(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.51  tff(c_443, plain, (![B_134, C_135, D_136]: (r1_orders_2('#skF_2', '#skF_5', '#skF_1'('#skF_2', B_134, C_135, D_136)) | ~r1_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', B_134, C_135, D_136)) | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', B_134, C_135, D_136)) | k10_lattice3('#skF_2', B_134, C_135)=D_136 | ~r1_orders_2('#skF_2', C_135, D_136) | ~r1_orders_2('#skF_2', B_134, D_136) | ~m1_subset_1(D_136, u1_struct_0('#skF_2')) | ~m1_subset_1(C_135, u1_struct_0('#skF_2')) | ~m1_subset_1(B_134, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_247])).
% 3.31/1.51  tff(c_4, plain, (![A_2, D_44, B_26, C_38]: (~r1_orders_2(A_2, D_44, '#skF_1'(A_2, B_26, C_38, D_44)) | k10_lattice3(A_2, B_26, C_38)=D_44 | ~r1_orders_2(A_2, C_38, D_44) | ~r1_orders_2(A_2, B_26, D_44) | ~m1_subset_1(D_44, u1_struct_0(A_2)) | ~m1_subset_1(C_38, u1_struct_0(A_2)) | ~m1_subset_1(B_26, u1_struct_0(A_2)) | ~l1_orders_2(A_2) | ~v1_lattice3(A_2) | ~v5_orders_2(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.51  tff(c_449, plain, (![B_134, C_135]: (~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~r1_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', B_134, C_135, '#skF_5')) | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', B_134, C_135, '#skF_5')) | k10_lattice3('#skF_2', B_134, C_135)='#skF_5' | ~r1_orders_2('#skF_2', C_135, '#skF_5') | ~r1_orders_2('#skF_2', B_134, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1(C_135, u1_struct_0('#skF_2')) | ~m1_subset_1(B_134, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_443, c_4])).
% 3.31/1.51  tff(c_456, plain, (![B_134, C_135]: (v2_struct_0('#skF_2') | ~r1_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', B_134, C_135, '#skF_5')) | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', B_134, C_135, '#skF_5')) | k10_lattice3('#skF_2', B_134, C_135)='#skF_5' | ~r1_orders_2('#skF_2', C_135, '#skF_5') | ~r1_orders_2('#skF_2', B_134, '#skF_5') | ~m1_subset_1(C_135, u1_struct_0('#skF_2')) | ~m1_subset_1(B_134, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_30, c_28, c_26, c_449])).
% 3.31/1.51  tff(c_462, plain, (![B_137, C_138]: (~r1_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', B_137, C_138, '#skF_5')) | ~r1_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', B_137, C_138, '#skF_5')) | k10_lattice3('#skF_2', B_137, C_138)='#skF_5' | ~r1_orders_2('#skF_2', C_138, '#skF_5') | ~r1_orders_2('#skF_2', B_137, '#skF_5') | ~m1_subset_1(C_138, u1_struct_0('#skF_2')) | ~m1_subset_1(B_137, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_273, c_456])).
% 3.31/1.51  tff(c_470, plain, (![C_38]: (~r1_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_3', C_38, '#skF_5')) | k10_lattice3('#skF_2', '#skF_3', C_38)='#skF_5' | ~r1_orders_2('#skF_2', C_38, '#skF_5') | ~r1_orders_2('#skF_2', '#skF_3', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1(C_38, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_462])).
% 3.31/1.51  tff(c_477, plain, (![C_38]: (~r1_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_3', C_38, '#skF_5')) | k10_lattice3('#skF_2', '#skF_3', C_38)='#skF_5' | ~r1_orders_2('#skF_2', C_38, '#skF_5') | ~m1_subset_1(C_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_20, c_72, c_470])).
% 3.31/1.51  tff(c_530, plain, (![C_143]: (~r1_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_3', C_143, '#skF_5')) | k10_lattice3('#skF_2', '#skF_3', C_143)='#skF_5' | ~r1_orders_2('#skF_2', C_143, '#skF_5') | ~m1_subset_1(C_143, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_273, c_477])).
% 3.31/1.51  tff(c_534, plain, (k10_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5' | ~r1_orders_2('#skF_2', '#skF_4', '#skF_5') | ~r1_orders_2('#skF_2', '#skF_3', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_6, c_530])).
% 3.31/1.51  tff(c_537, plain, (k10_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_72, c_73, c_534])).
% 3.31/1.51  tff(c_539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_273, c_188, c_537])).
% 3.31/1.51  tff(c_541, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_75])).
% 3.31/1.51  tff(c_34, plain, (~r1_orders_2('#skF_2', '#skF_5', '#skF_6') | ~r1_orders_2('#skF_2', '#skF_4', '#skF_5') | ~r1_orders_2('#skF_2', '#skF_3', '#skF_5') | k13_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.51  tff(c_549, plain, (~r1_orders_2('#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_541, c_72, c_73, c_34])).
% 3.31/1.51  tff(c_38, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_6') | ~r1_orders_2('#skF_2', '#skF_4', '#skF_5') | ~r1_orders_2('#skF_2', '#skF_3', '#skF_5') | k13_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.51  tff(c_551, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_541, c_72, c_73, c_38])).
% 3.31/1.51  tff(c_540, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_75])).
% 3.31/1.51  tff(c_40, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2')) | ~r1_orders_2('#skF_2', '#skF_4', '#skF_5') | ~r1_orders_2('#skF_2', '#skF_3', '#skF_5') | k13_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.31/1.51  tff(c_547, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_541, c_72, c_73, c_40])).
% 3.31/1.51  tff(c_725, plain, (![A_157, B_158, C_159, D_160]: (m1_subset_1('#skF_1'(A_157, B_158, C_159, D_160), u1_struct_0(A_157)) | k10_lattice3(A_157, B_158, C_159)=D_160 | ~r1_orders_2(A_157, C_159, D_160) | ~r1_orders_2(A_157, B_158, D_160) | ~m1_subset_1(D_160, u1_struct_0(A_157)) | ~m1_subset_1(C_159, u1_struct_0(A_157)) | ~m1_subset_1(B_158, u1_struct_0(A_157)) | ~l1_orders_2(A_157) | ~v1_lattice3(A_157) | ~v5_orders_2(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.51  tff(c_555, plain, (![A_144, B_145, C_146]: (k13_lattice3(A_144, B_145, C_146)=k10_lattice3(A_144, B_145, C_146) | ~m1_subset_1(C_146, u1_struct_0(A_144)) | ~m1_subset_1(B_145, u1_struct_0(A_144)) | ~l1_orders_2(A_144) | ~v1_lattice3(A_144) | ~v5_orders_2(A_144))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.31/1.51  tff(c_563, plain, (![B_145]: (k13_lattice3('#skF_2', B_145, '#skF_4')=k10_lattice3('#skF_2', B_145, '#skF_4') | ~m1_subset_1(B_145, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_555])).
% 3.31/1.51  tff(c_575, plain, (![B_145]: (k13_lattice3('#skF_2', B_145, '#skF_4')=k10_lattice3('#skF_2', B_145, '#skF_4') | ~m1_subset_1(B_145, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_563])).
% 3.31/1.51  tff(c_737, plain, (![B_158, C_159, D_160]: (k13_lattice3('#skF_2', '#skF_1'('#skF_2', B_158, C_159, D_160), '#skF_4')=k10_lattice3('#skF_2', '#skF_1'('#skF_2', B_158, C_159, D_160), '#skF_4') | k10_lattice3('#skF_2', B_158, C_159)=D_160 | ~r1_orders_2('#skF_2', C_159, D_160) | ~r1_orders_2('#skF_2', B_158, D_160) | ~m1_subset_1(D_160, u1_struct_0('#skF_2')) | ~m1_subset_1(C_159, u1_struct_0('#skF_2')) | ~m1_subset_1(B_158, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_725, c_575])).
% 3.31/1.51  tff(c_752, plain, (![B_158, C_159, D_160]: (k13_lattice3('#skF_2', '#skF_1'('#skF_2', B_158, C_159, D_160), '#skF_4')=k10_lattice3('#skF_2', '#skF_1'('#skF_2', B_158, C_159, D_160), '#skF_4') | k10_lattice3('#skF_2', B_158, C_159)=D_160 | ~r1_orders_2('#skF_2', C_159, D_160) | ~r1_orders_2('#skF_2', B_158, D_160) | ~m1_subset_1(D_160, u1_struct_0('#skF_2')) | ~m1_subset_1(C_159, u1_struct_0('#skF_2')) | ~m1_subset_1(B_158, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_737])).
% 3.31/1.51  tff(c_759, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_752])).
% 3.31/1.51  tff(c_762, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_759, c_2])).
% 3.31/1.51  tff(c_766, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_762])).
% 3.31/1.51  tff(c_768, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_752])).
% 3.31/1.51  tff(c_611, plain, (![B_148]: (k13_lattice3('#skF_2', B_148, '#skF_4')=k10_lattice3('#skF_2', B_148, '#skF_4') | ~m1_subset_1(B_148, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_563])).
% 3.31/1.51  tff(c_617, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')=k10_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_611])).
% 3.31/1.51  tff(c_626, plain, (k10_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_541, c_617])).
% 3.31/1.51  tff(c_812, plain, (![A_179, B_180, C_181, E_182]: (r1_orders_2(A_179, k10_lattice3(A_179, B_180, C_181), E_182) | ~r1_orders_2(A_179, C_181, E_182) | ~r1_orders_2(A_179, B_180, E_182) | ~m1_subset_1(E_182, u1_struct_0(A_179)) | ~m1_subset_1(k10_lattice3(A_179, B_180, C_181), u1_struct_0(A_179)) | ~m1_subset_1(C_181, u1_struct_0(A_179)) | ~m1_subset_1(B_180, u1_struct_0(A_179)) | ~l1_orders_2(A_179) | ~v1_lattice3(A_179) | ~v5_orders_2(A_179) | v2_struct_0(A_179))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.51  tff(c_814, plain, (![E_182]: (r1_orders_2('#skF_2', k10_lattice3('#skF_2', '#skF_3', '#skF_4'), E_182) | ~r1_orders_2('#skF_2', '#skF_4', E_182) | ~r1_orders_2('#skF_2', '#skF_3', E_182) | ~m1_subset_1(E_182, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_626, c_812])).
% 3.31/1.51  tff(c_816, plain, (![E_182]: (r1_orders_2('#skF_2', '#skF_5', E_182) | ~r1_orders_2('#skF_2', '#skF_4', E_182) | ~r1_orders_2('#skF_2', '#skF_3', E_182) | ~m1_subset_1(E_182, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_626, c_814])).
% 3.31/1.51  tff(c_820, plain, (![E_183]: (r1_orders_2('#skF_2', '#skF_5', E_183) | ~r1_orders_2('#skF_2', '#skF_4', E_183) | ~r1_orders_2('#skF_2', '#skF_3', E_183) | ~m1_subset_1(E_183, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_768, c_816])).
% 3.31/1.51  tff(c_827, plain, (r1_orders_2('#skF_2', '#skF_5', '#skF_6') | ~r1_orders_2('#skF_2', '#skF_4', '#skF_6') | ~r1_orders_2('#skF_2', '#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_547, c_820])).
% 3.31/1.51  tff(c_843, plain, (r1_orders_2('#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_551, c_540, c_827])).
% 3.31/1.51  tff(c_845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_549, c_843])).
% 3.31/1.51  tff(c_847, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 3.31/1.51  tff(c_846, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_52])).
% 3.31/1.51  tff(c_861, plain, (![A_184, B_185, C_186]: (k13_lattice3(A_184, B_185, C_186)=k10_lattice3(A_184, B_185, C_186) | ~m1_subset_1(C_186, u1_struct_0(A_184)) | ~m1_subset_1(B_185, u1_struct_0(A_184)) | ~l1_orders_2(A_184) | ~v1_lattice3(A_184) | ~v5_orders_2(A_184))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.31/1.51  tff(c_867, plain, (![B_185]: (k13_lattice3('#skF_2', B_185, '#skF_4')=k10_lattice3('#skF_2', B_185, '#skF_4') | ~m1_subset_1(B_185, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_861])).
% 3.31/1.51  tff(c_904, plain, (![B_188]: (k13_lattice3('#skF_2', B_188, '#skF_4')=k10_lattice3('#skF_2', B_188, '#skF_4') | ~m1_subset_1(B_188, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_867])).
% 3.31/1.51  tff(c_907, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')=k10_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_904])).
% 3.31/1.51  tff(c_915, plain, (k10_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_846, c_907])).
% 3.31/1.51  tff(c_966, plain, (![A_193, C_194, B_195]: (r1_orders_2(A_193, C_194, k10_lattice3(A_193, B_195, C_194)) | ~m1_subset_1(k10_lattice3(A_193, B_195, C_194), u1_struct_0(A_193)) | ~m1_subset_1(C_194, u1_struct_0(A_193)) | ~m1_subset_1(B_195, u1_struct_0(A_193)) | ~l1_orders_2(A_193) | ~v1_lattice3(A_193) | ~v5_orders_2(A_193) | v2_struct_0(A_193))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.51  tff(c_968, plain, (r1_orders_2('#skF_2', '#skF_4', k10_lattice3('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_915, c_966])).
% 3.31/1.51  tff(c_970, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_915, c_968])).
% 3.31/1.51  tff(c_971, plain, (v2_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_847, c_970])).
% 3.31/1.51  tff(c_974, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_971, c_2])).
% 3.31/1.51  tff(c_978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_974])).
% 3.31/1.51  tff(c_980, plain, (~r1_orders_2('#skF_2', '#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_62])).
% 3.31/1.51  tff(c_979, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_62])).
% 3.31/1.51  tff(c_995, plain, (![A_196, B_197, C_198]: (k13_lattice3(A_196, B_197, C_198)=k10_lattice3(A_196, B_197, C_198) | ~m1_subset_1(C_198, u1_struct_0(A_196)) | ~m1_subset_1(B_197, u1_struct_0(A_196)) | ~l1_orders_2(A_196) | ~v1_lattice3(A_196) | ~v5_orders_2(A_196))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.31/1.51  tff(c_1001, plain, (![B_197]: (k13_lattice3('#skF_2', B_197, '#skF_4')=k10_lattice3('#skF_2', B_197, '#skF_4') | ~m1_subset_1(B_197, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_995])).
% 3.31/1.51  tff(c_1061, plain, (![B_201]: (k13_lattice3('#skF_2', B_201, '#skF_4')=k10_lattice3('#skF_2', B_201, '#skF_4') | ~m1_subset_1(B_201, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_1001])).
% 3.31/1.51  tff(c_1064, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')=k10_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_1061])).
% 3.31/1.51  tff(c_1072, plain, (k10_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_979, c_1064])).
% 3.31/1.51  tff(c_1087, plain, (![A_202, B_203, C_204]: (r1_orders_2(A_202, B_203, k10_lattice3(A_202, B_203, C_204)) | ~m1_subset_1(k10_lattice3(A_202, B_203, C_204), u1_struct_0(A_202)) | ~m1_subset_1(C_204, u1_struct_0(A_202)) | ~m1_subset_1(B_203, u1_struct_0(A_202)) | ~l1_orders_2(A_202) | ~v1_lattice3(A_202) | ~v5_orders_2(A_202) | v2_struct_0(A_202))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.51  tff(c_1089, plain, (r1_orders_2('#skF_2', '#skF_3', k10_lattice3('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1072, c_1087])).
% 3.31/1.51  tff(c_1091, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_20, c_1072, c_1089])).
% 3.31/1.51  tff(c_1092, plain, (v2_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_980, c_1091])).
% 3.31/1.51  tff(c_1095, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_1092, c_2])).
% 3.31/1.51  tff(c_1099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_1095])).
% 3.31/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.51  
% 3.31/1.51  Inference rules
% 3.31/1.51  ----------------------
% 3.31/1.51  #Ref     : 0
% 3.31/1.51  #Sup     : 249
% 3.31/1.51  #Fact    : 0
% 3.31/1.51  #Define  : 0
% 3.31/1.51  #Split   : 10
% 3.31/1.51  #Chain   : 0
% 3.31/1.51  #Close   : 0
% 3.31/1.51  
% 3.31/1.51  Ordering : KBO
% 3.31/1.51  
% 3.31/1.51  Simplification rules
% 3.31/1.51  ----------------------
% 3.31/1.51  #Subsume      : 28
% 3.31/1.51  #Demod        : 416
% 3.31/1.51  #Tautology    : 153
% 3.31/1.51  #SimpNegUnit  : 40
% 3.31/1.51  #BackRed      : 7
% 3.31/1.51  
% 3.31/1.51  #Partial instantiations: 0
% 3.31/1.51  #Strategies tried      : 1
% 3.31/1.51  
% 3.31/1.51  Timing (in seconds)
% 3.31/1.51  ----------------------
% 3.31/1.51  Preprocessing        : 0.33
% 3.31/1.51  Parsing              : 0.16
% 3.31/1.51  CNF conversion       : 0.03
% 3.31/1.51  Main loop            : 0.43
% 3.31/1.51  Inferencing          : 0.15
% 3.31/1.51  Reduction            : 0.14
% 3.31/1.51  Demodulation         : 0.10
% 3.31/1.51  BG Simplification    : 0.03
% 3.31/1.51  Subsumption          : 0.09
% 3.31/1.51  Abstraction          : 0.03
% 3.31/1.51  MUC search           : 0.00
% 3.31/1.51  Cooper               : 0.00
% 3.31/1.51  Total                : 0.80
% 3.31/1.51  Index Insertion      : 0.00
% 3.31/1.51  Index Deletion       : 0.00
% 3.31/1.51  Index Matching       : 0.00
% 3.31/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
