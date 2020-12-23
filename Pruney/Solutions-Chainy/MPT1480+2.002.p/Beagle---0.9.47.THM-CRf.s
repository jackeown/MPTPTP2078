%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:39 EST 2020

% Result     : Theorem 15.32s
% Output     : CNFRefutation 15.46s
% Verified   : 
% Statistics : Number of formulae       :   84 (1320 expanded)
%              Number of leaves         :   19 ( 473 expanded)
%              Depth                    :   26
%              Number of atoms          :  376 (8597 expanded)
%              Number of equality atoms :   33 ( 603 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v2_struct_0 > v1_lattice3 > l1_orders_2 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( ( v5_orders_2(A)
          & v1_lattice3(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k10_lattice3(A,B,C) = k10_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_lattice3)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k10_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

tff(f_73,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(c_26,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4,plain,(
    ! [A_2,B_3,C_4] :
      ( m1_subset_1(k10_lattice3(A_2,B_3,C_4),u1_struct_0(A_2))
      | ~ m1_subset_1(C_4,u1_struct_0(A_2))
      | ~ m1_subset_1(B_3,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_37,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_orders_2(A_62,C_63,k10_lattice3(A_62,B_64,C_63))
      | ~ m1_subset_1(k10_lattice3(A_62,B_64,C_63),u1_struct_0(A_62))
      | ~ m1_subset_1(C_63,u1_struct_0(A_62))
      | ~ m1_subset_1(B_64,u1_struct_0(A_62))
      | ~ l1_orders_2(A_62)
      | ~ v1_lattice3(A_62)
      | ~ v5_orders_2(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ! [A_2,C_4,B_3] :
      ( r1_orders_2(A_2,C_4,k10_lattice3(A_2,B_3,C_4))
      | ~ v1_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | v2_struct_0(A_2)
      | ~ m1_subset_1(C_4,u1_struct_0(A_2))
      | ~ m1_subset_1(B_3,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_37])).

tff(c_33,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_orders_2(A_59,B_60,k10_lattice3(A_59,B_60,C_61))
      | ~ m1_subset_1(k10_lattice3(A_59,B_60,C_61),u1_struct_0(A_59))
      | ~ m1_subset_1(C_61,u1_struct_0(A_59))
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | ~ v1_lattice3(A_59)
      | ~ v5_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_36,plain,(
    ! [A_2,B_3,C_4] :
      ( r1_orders_2(A_2,B_3,k10_lattice3(A_2,B_3,C_4))
      | ~ v1_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | v2_struct_0(A_2)
      | ~ m1_subset_1(C_4,u1_struct_0(A_2))
      | ~ m1_subset_1(B_3,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_33])).

tff(c_71,plain,(
    ! [A_93,B_94,C_95,E_96] :
      ( r1_orders_2(A_93,k10_lattice3(A_93,B_94,C_95),E_96)
      | ~ r1_orders_2(A_93,C_95,E_96)
      | ~ r1_orders_2(A_93,B_94,E_96)
      | ~ m1_subset_1(E_96,u1_struct_0(A_93))
      | ~ m1_subset_1(k10_lattice3(A_93,B_94,C_95),u1_struct_0(A_93))
      | ~ m1_subset_1(C_95,u1_struct_0(A_93))
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93)
      | ~ v1_lattice3(A_93)
      | ~ v5_orders_2(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_74,plain,(
    ! [A_2,B_3,C_4,E_96] :
      ( r1_orders_2(A_2,k10_lattice3(A_2,B_3,C_4),E_96)
      | ~ r1_orders_2(A_2,C_4,E_96)
      | ~ r1_orders_2(A_2,B_3,E_96)
      | ~ m1_subset_1(E_96,u1_struct_0(A_2))
      | ~ v1_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | v2_struct_0(A_2)
      | ~ m1_subset_1(C_4,u1_struct_0(A_2))
      | ~ m1_subset_1(B_3,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_51,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( r1_orders_2(A_82,B_83,'#skF_1'(A_82,B_83,C_84,D_85))
      | k10_lattice3(A_82,B_83,C_84) = D_85
      | ~ r1_orders_2(A_82,C_84,D_85)
      | ~ r1_orders_2(A_82,B_83,D_85)
      | ~ m1_subset_1(D_85,u1_struct_0(A_82))
      | ~ m1_subset_1(C_84,u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | ~ v1_lattice3(A_82)
      | ~ v5_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_5,D_47,B_29,C_41] :
      ( ~ r1_orders_2(A_5,D_47,'#skF_1'(A_5,B_29,C_41,D_47))
      | k10_lattice3(A_5,B_29,C_41) = D_47
      | ~ r1_orders_2(A_5,C_41,D_47)
      | ~ r1_orders_2(A_5,B_29,D_47)
      | ~ m1_subset_1(D_47,u1_struct_0(A_5))
      | ~ m1_subset_1(C_41,u1_struct_0(A_5))
      | ~ m1_subset_1(B_29,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5)
      | ~ v1_lattice3(A_5)
      | ~ v5_orders_2(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_57,plain,(
    ! [A_86,D_87,C_88] :
      ( k10_lattice3(A_86,D_87,C_88) = D_87
      | ~ r1_orders_2(A_86,C_88,D_87)
      | ~ r1_orders_2(A_86,D_87,D_87)
      | ~ m1_subset_1(C_88,u1_struct_0(A_86))
      | ~ m1_subset_1(D_87,u1_struct_0(A_86))
      | ~ l1_orders_2(A_86)
      | ~ v1_lattice3(A_86)
      | ~ v5_orders_2(A_86)
      | v2_struct_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_51,c_6])).

tff(c_94,plain,(
    ! [A_104,B_105,C_106] :
      ( k10_lattice3(A_104,k10_lattice3(A_104,B_105,C_106),C_106) = k10_lattice3(A_104,B_105,C_106)
      | ~ r1_orders_2(A_104,k10_lattice3(A_104,B_105,C_106),k10_lattice3(A_104,B_105,C_106))
      | ~ m1_subset_1(k10_lattice3(A_104,B_105,C_106),u1_struct_0(A_104))
      | ~ v1_lattice3(A_104)
      | ~ v5_orders_2(A_104)
      | v2_struct_0(A_104)
      | ~ m1_subset_1(C_106,u1_struct_0(A_104))
      | ~ m1_subset_1(B_105,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104) ) ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_105,plain,(
    ! [A_111,B_112,C_113] :
      ( k10_lattice3(A_111,k10_lattice3(A_111,B_112,C_113),C_113) = k10_lattice3(A_111,B_112,C_113)
      | ~ r1_orders_2(A_111,C_113,k10_lattice3(A_111,B_112,C_113))
      | ~ r1_orders_2(A_111,B_112,k10_lattice3(A_111,B_112,C_113))
      | ~ m1_subset_1(k10_lattice3(A_111,B_112,C_113),u1_struct_0(A_111))
      | ~ v1_lattice3(A_111)
      | ~ v5_orders_2(A_111)
      | v2_struct_0(A_111)
      | ~ m1_subset_1(C_113,u1_struct_0(A_111))
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l1_orders_2(A_111) ) ),
    inference(resolution,[status(thm)],[c_74,c_94])).

tff(c_117,plain,(
    ! [A_114,C_115] :
      ( k10_lattice3(A_114,k10_lattice3(A_114,C_115,C_115),C_115) = k10_lattice3(A_114,C_115,C_115)
      | ~ r1_orders_2(A_114,C_115,k10_lattice3(A_114,C_115,C_115))
      | ~ m1_subset_1(k10_lattice3(A_114,C_115,C_115),u1_struct_0(A_114))
      | ~ v1_lattice3(A_114)
      | ~ v5_orders_2(A_114)
      | v2_struct_0(A_114)
      | ~ m1_subset_1(C_115,u1_struct_0(A_114))
      | ~ l1_orders_2(A_114) ) ),
    inference(resolution,[status(thm)],[c_36,c_105])).

tff(c_141,plain,(
    ! [A_120,B_121] :
      ( k10_lattice3(A_120,k10_lattice3(A_120,B_121,B_121),B_121) = k10_lattice3(A_120,B_121,B_121)
      | ~ m1_subset_1(k10_lattice3(A_120,B_121,B_121),u1_struct_0(A_120))
      | ~ v1_lattice3(A_120)
      | ~ v5_orders_2(A_120)
      | v2_struct_0(A_120)
      | ~ m1_subset_1(B_121,u1_struct_0(A_120))
      | ~ l1_orders_2(A_120) ) ),
    inference(resolution,[status(thm)],[c_40,c_117])).

tff(c_146,plain,(
    ! [A_122,C_123] :
      ( k10_lattice3(A_122,k10_lattice3(A_122,C_123,C_123),C_123) = k10_lattice3(A_122,C_123,C_123)
      | ~ v1_lattice3(A_122)
      | ~ v5_orders_2(A_122)
      | v2_struct_0(A_122)
      | ~ m1_subset_1(C_123,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122) ) ),
    inference(resolution,[status(thm)],[c_4,c_141])).

tff(c_152,plain,
    ( k10_lattice3('#skF_2',k10_lattice3('#skF_2','#skF_4','#skF_4'),'#skF_4') = k10_lattice3('#skF_2','#skF_4','#skF_4')
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_146])).

tff(c_159,plain,
    ( k10_lattice3('#skF_2',k10_lattice3('#skF_2','#skF_4','#skF_4'),'#skF_4') = k10_lattice3('#skF_2','#skF_4','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30,c_28,c_152])).

tff(c_163,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v1_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_167,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_167])).

tff(c_173,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_20,plain,(
    k10_lattice3('#skF_2','#skF_3','#skF_4') != k10_lattice3('#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_825,plain,(
    ! [A_143,B_144,C_145] :
      ( k10_lattice3(A_143,k10_lattice3(A_143,B_144,C_145),C_145) = k10_lattice3(A_143,B_144,C_145)
      | ~ r1_orders_2(A_143,B_144,k10_lattice3(A_143,B_144,C_145))
      | ~ m1_subset_1(k10_lattice3(A_143,B_144,C_145),u1_struct_0(A_143))
      | ~ v1_lattice3(A_143)
      | ~ v5_orders_2(A_143)
      | v2_struct_0(A_143)
      | ~ m1_subset_1(C_145,u1_struct_0(A_143))
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | ~ l1_orders_2(A_143) ) ),
    inference(resolution,[status(thm)],[c_40,c_105])).

tff(c_879,plain,(
    ! [A_146,B_147,C_148] :
      ( k10_lattice3(A_146,k10_lattice3(A_146,B_147,C_148),C_148) = k10_lattice3(A_146,B_147,C_148)
      | ~ m1_subset_1(k10_lattice3(A_146,B_147,C_148),u1_struct_0(A_146))
      | ~ v1_lattice3(A_146)
      | ~ v5_orders_2(A_146)
      | v2_struct_0(A_146)
      | ~ m1_subset_1(C_148,u1_struct_0(A_146))
      | ~ m1_subset_1(B_147,u1_struct_0(A_146))
      | ~ l1_orders_2(A_146) ) ),
    inference(resolution,[status(thm)],[c_36,c_825])).

tff(c_984,plain,(
    ! [A_151,B_152,C_153] :
      ( k10_lattice3(A_151,k10_lattice3(A_151,B_152,C_153),C_153) = k10_lattice3(A_151,B_152,C_153)
      | ~ v1_lattice3(A_151)
      | ~ v5_orders_2(A_151)
      | v2_struct_0(A_151)
      | ~ m1_subset_1(C_153,u1_struct_0(A_151))
      | ~ m1_subset_1(B_152,u1_struct_0(A_151))
      | ~ l1_orders_2(A_151) ) ),
    inference(resolution,[status(thm)],[c_4,c_879])).

tff(c_994,plain,(
    ! [B_152] :
      ( k10_lattice3('#skF_2',k10_lattice3('#skF_2',B_152,'#skF_4'),'#skF_4') = k10_lattice3('#skF_2',B_152,'#skF_4')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_984])).

tff(c_1009,plain,(
    ! [B_152] :
      ( k10_lattice3('#skF_2',k10_lattice3('#skF_2',B_152,'#skF_4'),'#skF_4') = k10_lattice3('#skF_2',B_152,'#skF_4')
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(B_152,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30,c_28,c_994])).

tff(c_1069,plain,(
    ! [B_157] :
      ( k10_lattice3('#skF_2',k10_lattice3('#skF_2',B_157,'#skF_4'),'#skF_4') = k10_lattice3('#skF_2',B_157,'#skF_4')
      | ~ m1_subset_1(B_157,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_1009])).

tff(c_1102,plain,(
    k10_lattice3('#skF_2',k10_lattice3('#skF_2','#skF_3','#skF_4'),'#skF_4') = k10_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1069])).

tff(c_1124,plain,
    ( r1_orders_2('#skF_2','#skF_4',k10_lattice3('#skF_2','#skF_3','#skF_4'))
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k10_lattice3('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1102,c_40])).

tff(c_1154,plain,
    ( r1_orders_2('#skF_2','#skF_4',k10_lattice3('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2')
    | ~ m1_subset_1(k10_lattice3('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_30,c_28,c_1124])).

tff(c_1155,plain,
    ( r1_orders_2('#skF_2','#skF_4',k10_lattice3('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1(k10_lattice3('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_1154])).

tff(c_1162,plain,(
    ~ m1_subset_1(k10_lattice3('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1155])).

tff(c_1199,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_1162])).

tff(c_1203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_1199])).

tff(c_1205,plain,(
    m1_subset_1(k10_lattice3('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1155])).

tff(c_1204,plain,(
    r1_orders_2('#skF_2','#skF_4',k10_lattice3('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1155])).

tff(c_1127,plain,
    ( r1_orders_2('#skF_2',k10_lattice3('#skF_2','#skF_3','#skF_4'),k10_lattice3('#skF_2','#skF_3','#skF_4'))
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k10_lattice3('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1102,c_36])).

tff(c_1157,plain,
    ( r1_orders_2('#skF_2',k10_lattice3('#skF_2','#skF_3','#skF_4'),k10_lattice3('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2')
    | ~ m1_subset_1(k10_lattice3('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_30,c_28,c_1127])).

tff(c_1158,plain,
    ( r1_orders_2('#skF_2',k10_lattice3('#skF_2','#skF_3','#skF_4'),k10_lattice3('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1(k10_lattice3('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_1157])).

tff(c_2058,plain,(
    r1_orders_2('#skF_2',k10_lattice3('#skF_2','#skF_3','#skF_4'),k10_lattice3('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1205,c_1158])).

tff(c_69,plain,(
    ! [A_2,B_3,C_4] :
      ( k10_lattice3(A_2,k10_lattice3(A_2,B_3,C_4),B_3) = k10_lattice3(A_2,B_3,C_4)
      | ~ r1_orders_2(A_2,k10_lattice3(A_2,B_3,C_4),k10_lattice3(A_2,B_3,C_4))
      | ~ m1_subset_1(k10_lattice3(A_2,B_3,C_4),u1_struct_0(A_2))
      | ~ v1_lattice3(A_2)
      | ~ v5_orders_2(A_2)
      | v2_struct_0(A_2)
      | ~ m1_subset_1(C_4,u1_struct_0(A_2))
      | ~ m1_subset_1(B_3,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2) ) ),
    inference(resolution,[status(thm)],[c_36,c_57])).

tff(c_2065,plain,
    ( k10_lattice3('#skF_2',k10_lattice3('#skF_2','#skF_3','#skF_4'),'#skF_3') = k10_lattice3('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1(k10_lattice3('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_2058,c_69])).

tff(c_2080,plain,
    ( k10_lattice3('#skF_2',k10_lattice3('#skF_2','#skF_3','#skF_4'),'#skF_3') = k10_lattice3('#skF_2','#skF_3','#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_30,c_28,c_1205,c_2065])).

tff(c_2081,plain,(
    k10_lattice3('#skF_2',k10_lattice3('#skF_2','#skF_3','#skF_4'),'#skF_3') = k10_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_2080])).

tff(c_2117,plain,
    ( r1_orders_2('#skF_2','#skF_3',k10_lattice3('#skF_2','#skF_3','#skF_4'))
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k10_lattice3('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2081,c_40])).

tff(c_2156,plain,
    ( r1_orders_2('#skF_2','#skF_3',k10_lattice3('#skF_2','#skF_3','#skF_4'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1205,c_24,c_30,c_28,c_2117])).

tff(c_2157,plain,(
    r1_orders_2('#skF_2','#skF_3',k10_lattice3('#skF_2','#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_2156])).

tff(c_12,plain,(
    ! [A_5,B_29,C_41,D_47] :
      ( m1_subset_1('#skF_1'(A_5,B_29,C_41,D_47),u1_struct_0(A_5))
      | k10_lattice3(A_5,B_29,C_41) = D_47
      | ~ r1_orders_2(A_5,C_41,D_47)
      | ~ r1_orders_2(A_5,B_29,D_47)
      | ~ m1_subset_1(D_47,u1_struct_0(A_5))
      | ~ m1_subset_1(C_41,u1_struct_0(A_5))
      | ~ m1_subset_1(B_29,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5)
      | ~ v1_lattice3(A_5)
      | ~ v5_orders_2(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_5,C_41,B_29,D_47] :
      ( r1_orders_2(A_5,C_41,'#skF_1'(A_5,B_29,C_41,D_47))
      | k10_lattice3(A_5,B_29,C_41) = D_47
      | ~ r1_orders_2(A_5,C_41,D_47)
      | ~ r1_orders_2(A_5,B_29,D_47)
      | ~ m1_subset_1(D_47,u1_struct_0(A_5))
      | ~ m1_subset_1(C_41,u1_struct_0(A_5))
      | ~ m1_subset_1(B_29,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5)
      | ~ v1_lattice3(A_5)
      | ~ v5_orders_2(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_5,B_29,C_41,D_47] :
      ( r1_orders_2(A_5,B_29,'#skF_1'(A_5,B_29,C_41,D_47))
      | k10_lattice3(A_5,B_29,C_41) = D_47
      | ~ r1_orders_2(A_5,C_41,D_47)
      | ~ r1_orders_2(A_5,B_29,D_47)
      | ~ m1_subset_1(D_47,u1_struct_0(A_5))
      | ~ m1_subset_1(C_41,u1_struct_0(A_5))
      | ~ m1_subset_1(B_29,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5)
      | ~ v1_lattice3(A_5)
      | ~ v5_orders_2(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_75,plain,(
    ! [A_97,B_98,C_99,E_100] :
      ( r1_orders_2(A_97,k10_lattice3(A_97,B_98,C_99),E_100)
      | ~ r1_orders_2(A_97,C_99,E_100)
      | ~ r1_orders_2(A_97,B_98,E_100)
      | ~ m1_subset_1(E_100,u1_struct_0(A_97))
      | ~ v1_lattice3(A_97)
      | ~ v5_orders_2(A_97)
      | v2_struct_0(A_97)
      | ~ m1_subset_1(C_99,u1_struct_0(A_97))
      | ~ m1_subset_1(B_98,u1_struct_0(A_97))
      | ~ l1_orders_2(A_97) ) ),
    inference(resolution,[status(thm)],[c_4,c_71])).

tff(c_780,plain,(
    ! [C_140,A_138,B_142,B_141,C_139] :
      ( k10_lattice3(A_138,B_142,C_139) = k10_lattice3(A_138,B_141,C_140)
      | ~ r1_orders_2(A_138,C_139,k10_lattice3(A_138,B_141,C_140))
      | ~ r1_orders_2(A_138,B_142,k10_lattice3(A_138,B_141,C_140))
      | ~ m1_subset_1(k10_lattice3(A_138,B_141,C_140),u1_struct_0(A_138))
      | ~ m1_subset_1(C_139,u1_struct_0(A_138))
      | ~ m1_subset_1(B_142,u1_struct_0(A_138))
      | ~ r1_orders_2(A_138,C_140,'#skF_1'(A_138,B_142,C_139,k10_lattice3(A_138,B_141,C_140)))
      | ~ r1_orders_2(A_138,B_141,'#skF_1'(A_138,B_142,C_139,k10_lattice3(A_138,B_141,C_140)))
      | ~ m1_subset_1('#skF_1'(A_138,B_142,C_139,k10_lattice3(A_138,B_141,C_140)),u1_struct_0(A_138))
      | ~ v1_lattice3(A_138)
      | ~ v5_orders_2(A_138)
      | v2_struct_0(A_138)
      | ~ m1_subset_1(C_140,u1_struct_0(A_138))
      | ~ m1_subset_1(B_141,u1_struct_0(A_138))
      | ~ l1_orders_2(A_138) ) ),
    inference(resolution,[status(thm)],[c_75,c_6])).

tff(c_2327,plain,(
    ! [A_170,B_171,B_172,C_173] :
      ( ~ r1_orders_2(A_170,B_171,'#skF_1'(A_170,B_172,C_173,k10_lattice3(A_170,B_171,B_172)))
      | ~ m1_subset_1('#skF_1'(A_170,B_172,C_173,k10_lattice3(A_170,B_171,B_172)),u1_struct_0(A_170))
      | ~ m1_subset_1(B_171,u1_struct_0(A_170))
      | k10_lattice3(A_170,B_172,C_173) = k10_lattice3(A_170,B_171,B_172)
      | ~ r1_orders_2(A_170,C_173,k10_lattice3(A_170,B_171,B_172))
      | ~ r1_orders_2(A_170,B_172,k10_lattice3(A_170,B_171,B_172))
      | ~ m1_subset_1(k10_lattice3(A_170,B_171,B_172),u1_struct_0(A_170))
      | ~ m1_subset_1(C_173,u1_struct_0(A_170))
      | ~ m1_subset_1(B_172,u1_struct_0(A_170))
      | ~ l1_orders_2(A_170)
      | ~ v1_lattice3(A_170)
      | ~ v5_orders_2(A_170)
      | v2_struct_0(A_170) ) ),
    inference(resolution,[status(thm)],[c_10,c_780])).

tff(c_7619,plain,(
    ! [A_231,B_232,C_233] :
      ( ~ m1_subset_1('#skF_1'(A_231,B_232,C_233,k10_lattice3(A_231,C_233,B_232)),u1_struct_0(A_231))
      | k10_lattice3(A_231,C_233,B_232) = k10_lattice3(A_231,B_232,C_233)
      | ~ r1_orders_2(A_231,C_233,k10_lattice3(A_231,C_233,B_232))
      | ~ r1_orders_2(A_231,B_232,k10_lattice3(A_231,C_233,B_232))
      | ~ m1_subset_1(k10_lattice3(A_231,C_233,B_232),u1_struct_0(A_231))
      | ~ m1_subset_1(C_233,u1_struct_0(A_231))
      | ~ m1_subset_1(B_232,u1_struct_0(A_231))
      | ~ l1_orders_2(A_231)
      | ~ v1_lattice3(A_231)
      | ~ v5_orders_2(A_231)
      | v2_struct_0(A_231) ) ),
    inference(resolution,[status(thm)],[c_8,c_2327])).

tff(c_21697,plain,(
    ! [A_330,C_331,B_332] :
      ( k10_lattice3(A_330,C_331,B_332) = k10_lattice3(A_330,B_332,C_331)
      | ~ r1_orders_2(A_330,C_331,k10_lattice3(A_330,C_331,B_332))
      | ~ r1_orders_2(A_330,B_332,k10_lattice3(A_330,C_331,B_332))
      | ~ m1_subset_1(k10_lattice3(A_330,C_331,B_332),u1_struct_0(A_330))
      | ~ m1_subset_1(C_331,u1_struct_0(A_330))
      | ~ m1_subset_1(B_332,u1_struct_0(A_330))
      | ~ l1_orders_2(A_330)
      | ~ v1_lattice3(A_330)
      | ~ v5_orders_2(A_330)
      | v2_struct_0(A_330) ) ),
    inference(resolution,[status(thm)],[c_12,c_7619])).

tff(c_21837,plain,
    ( k10_lattice3('#skF_2','#skF_3','#skF_4') = k10_lattice3('#skF_2','#skF_4','#skF_3')
    | ~ r1_orders_2('#skF_2','#skF_4',k10_lattice3('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1(k10_lattice3('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2157,c_21697])).

tff(c_22096,plain,
    ( k10_lattice3('#skF_2','#skF_3','#skF_4') = k10_lattice3('#skF_2','#skF_4','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_22,c_24,c_1205,c_1204,c_21837])).

tff(c_22098,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_20,c_22096])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:21:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.32/7.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.32/7.30  
% 15.32/7.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.32/7.30  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v2_struct_0 > v1_lattice3 > l1_orders_2 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 15.32/7.30  
% 15.32/7.30  %Foreground sorts:
% 15.32/7.30  
% 15.32/7.30  
% 15.32/7.30  %Background operators:
% 15.32/7.30  
% 15.32/7.30  
% 15.32/7.30  %Foreground operators:
% 15.32/7.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.32/7.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.32/7.30  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 15.32/7.30  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 15.32/7.30  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 15.32/7.30  tff('#skF_2', type, '#skF_2': $i).
% 15.32/7.30  tff('#skF_3', type, '#skF_3': $i).
% 15.32/7.30  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 15.32/7.30  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 15.32/7.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.32/7.30  tff('#skF_4', type, '#skF_4': $i).
% 15.32/7.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.32/7.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 15.32/7.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.32/7.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.32/7.31  
% 15.46/7.33  tff(f_88, negated_conjecture, ~(![A]: (((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k10_lattice3(A, B, C) = k10_lattice3(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_lattice3)).
% 15.46/7.33  tff(f_40, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k10_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 15.46/7.33  tff(f_73, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 15.46/7.33  tff(f_32, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 15.46/7.33  tff(c_26, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.46/7.33  tff(c_28, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.46/7.33  tff(c_30, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.46/7.33  tff(c_22, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.46/7.33  tff(c_4, plain, (![A_2, B_3, C_4]: (m1_subset_1(k10_lattice3(A_2, B_3, C_4), u1_struct_0(A_2)) | ~m1_subset_1(C_4, u1_struct_0(A_2)) | ~m1_subset_1(B_3, u1_struct_0(A_2)) | ~l1_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.46/7.33  tff(c_37, plain, (![A_62, C_63, B_64]: (r1_orders_2(A_62, C_63, k10_lattice3(A_62, B_64, C_63)) | ~m1_subset_1(k10_lattice3(A_62, B_64, C_63), u1_struct_0(A_62)) | ~m1_subset_1(C_63, u1_struct_0(A_62)) | ~m1_subset_1(B_64, u1_struct_0(A_62)) | ~l1_orders_2(A_62) | ~v1_lattice3(A_62) | ~v5_orders_2(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.46/7.33  tff(c_40, plain, (![A_2, C_4, B_3]: (r1_orders_2(A_2, C_4, k10_lattice3(A_2, B_3, C_4)) | ~v1_lattice3(A_2) | ~v5_orders_2(A_2) | v2_struct_0(A_2) | ~m1_subset_1(C_4, u1_struct_0(A_2)) | ~m1_subset_1(B_3, u1_struct_0(A_2)) | ~l1_orders_2(A_2))), inference(resolution, [status(thm)], [c_4, c_37])).
% 15.46/7.33  tff(c_33, plain, (![A_59, B_60, C_61]: (r1_orders_2(A_59, B_60, k10_lattice3(A_59, B_60, C_61)) | ~m1_subset_1(k10_lattice3(A_59, B_60, C_61), u1_struct_0(A_59)) | ~m1_subset_1(C_61, u1_struct_0(A_59)) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | ~v1_lattice3(A_59) | ~v5_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.46/7.33  tff(c_36, plain, (![A_2, B_3, C_4]: (r1_orders_2(A_2, B_3, k10_lattice3(A_2, B_3, C_4)) | ~v1_lattice3(A_2) | ~v5_orders_2(A_2) | v2_struct_0(A_2) | ~m1_subset_1(C_4, u1_struct_0(A_2)) | ~m1_subset_1(B_3, u1_struct_0(A_2)) | ~l1_orders_2(A_2))), inference(resolution, [status(thm)], [c_4, c_33])).
% 15.46/7.33  tff(c_71, plain, (![A_93, B_94, C_95, E_96]: (r1_orders_2(A_93, k10_lattice3(A_93, B_94, C_95), E_96) | ~r1_orders_2(A_93, C_95, E_96) | ~r1_orders_2(A_93, B_94, E_96) | ~m1_subset_1(E_96, u1_struct_0(A_93)) | ~m1_subset_1(k10_lattice3(A_93, B_94, C_95), u1_struct_0(A_93)) | ~m1_subset_1(C_95, u1_struct_0(A_93)) | ~m1_subset_1(B_94, u1_struct_0(A_93)) | ~l1_orders_2(A_93) | ~v1_lattice3(A_93) | ~v5_orders_2(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.46/7.33  tff(c_74, plain, (![A_2, B_3, C_4, E_96]: (r1_orders_2(A_2, k10_lattice3(A_2, B_3, C_4), E_96) | ~r1_orders_2(A_2, C_4, E_96) | ~r1_orders_2(A_2, B_3, E_96) | ~m1_subset_1(E_96, u1_struct_0(A_2)) | ~v1_lattice3(A_2) | ~v5_orders_2(A_2) | v2_struct_0(A_2) | ~m1_subset_1(C_4, u1_struct_0(A_2)) | ~m1_subset_1(B_3, u1_struct_0(A_2)) | ~l1_orders_2(A_2))), inference(resolution, [status(thm)], [c_4, c_71])).
% 15.46/7.33  tff(c_51, plain, (![A_82, B_83, C_84, D_85]: (r1_orders_2(A_82, B_83, '#skF_1'(A_82, B_83, C_84, D_85)) | k10_lattice3(A_82, B_83, C_84)=D_85 | ~r1_orders_2(A_82, C_84, D_85) | ~r1_orders_2(A_82, B_83, D_85) | ~m1_subset_1(D_85, u1_struct_0(A_82)) | ~m1_subset_1(C_84, u1_struct_0(A_82)) | ~m1_subset_1(B_83, u1_struct_0(A_82)) | ~l1_orders_2(A_82) | ~v1_lattice3(A_82) | ~v5_orders_2(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.46/7.33  tff(c_6, plain, (![A_5, D_47, B_29, C_41]: (~r1_orders_2(A_5, D_47, '#skF_1'(A_5, B_29, C_41, D_47)) | k10_lattice3(A_5, B_29, C_41)=D_47 | ~r1_orders_2(A_5, C_41, D_47) | ~r1_orders_2(A_5, B_29, D_47) | ~m1_subset_1(D_47, u1_struct_0(A_5)) | ~m1_subset_1(C_41, u1_struct_0(A_5)) | ~m1_subset_1(B_29, u1_struct_0(A_5)) | ~l1_orders_2(A_5) | ~v1_lattice3(A_5) | ~v5_orders_2(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.46/7.33  tff(c_57, plain, (![A_86, D_87, C_88]: (k10_lattice3(A_86, D_87, C_88)=D_87 | ~r1_orders_2(A_86, C_88, D_87) | ~r1_orders_2(A_86, D_87, D_87) | ~m1_subset_1(C_88, u1_struct_0(A_86)) | ~m1_subset_1(D_87, u1_struct_0(A_86)) | ~l1_orders_2(A_86) | ~v1_lattice3(A_86) | ~v5_orders_2(A_86) | v2_struct_0(A_86))), inference(resolution, [status(thm)], [c_51, c_6])).
% 15.46/7.33  tff(c_94, plain, (![A_104, B_105, C_106]: (k10_lattice3(A_104, k10_lattice3(A_104, B_105, C_106), C_106)=k10_lattice3(A_104, B_105, C_106) | ~r1_orders_2(A_104, k10_lattice3(A_104, B_105, C_106), k10_lattice3(A_104, B_105, C_106)) | ~m1_subset_1(k10_lattice3(A_104, B_105, C_106), u1_struct_0(A_104)) | ~v1_lattice3(A_104) | ~v5_orders_2(A_104) | v2_struct_0(A_104) | ~m1_subset_1(C_106, u1_struct_0(A_104)) | ~m1_subset_1(B_105, u1_struct_0(A_104)) | ~l1_orders_2(A_104))), inference(resolution, [status(thm)], [c_40, c_57])).
% 15.46/7.33  tff(c_105, plain, (![A_111, B_112, C_113]: (k10_lattice3(A_111, k10_lattice3(A_111, B_112, C_113), C_113)=k10_lattice3(A_111, B_112, C_113) | ~r1_orders_2(A_111, C_113, k10_lattice3(A_111, B_112, C_113)) | ~r1_orders_2(A_111, B_112, k10_lattice3(A_111, B_112, C_113)) | ~m1_subset_1(k10_lattice3(A_111, B_112, C_113), u1_struct_0(A_111)) | ~v1_lattice3(A_111) | ~v5_orders_2(A_111) | v2_struct_0(A_111) | ~m1_subset_1(C_113, u1_struct_0(A_111)) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_orders_2(A_111))), inference(resolution, [status(thm)], [c_74, c_94])).
% 15.46/7.33  tff(c_117, plain, (![A_114, C_115]: (k10_lattice3(A_114, k10_lattice3(A_114, C_115, C_115), C_115)=k10_lattice3(A_114, C_115, C_115) | ~r1_orders_2(A_114, C_115, k10_lattice3(A_114, C_115, C_115)) | ~m1_subset_1(k10_lattice3(A_114, C_115, C_115), u1_struct_0(A_114)) | ~v1_lattice3(A_114) | ~v5_orders_2(A_114) | v2_struct_0(A_114) | ~m1_subset_1(C_115, u1_struct_0(A_114)) | ~l1_orders_2(A_114))), inference(resolution, [status(thm)], [c_36, c_105])).
% 15.46/7.33  tff(c_141, plain, (![A_120, B_121]: (k10_lattice3(A_120, k10_lattice3(A_120, B_121, B_121), B_121)=k10_lattice3(A_120, B_121, B_121) | ~m1_subset_1(k10_lattice3(A_120, B_121, B_121), u1_struct_0(A_120)) | ~v1_lattice3(A_120) | ~v5_orders_2(A_120) | v2_struct_0(A_120) | ~m1_subset_1(B_121, u1_struct_0(A_120)) | ~l1_orders_2(A_120))), inference(resolution, [status(thm)], [c_40, c_117])).
% 15.46/7.33  tff(c_146, plain, (![A_122, C_123]: (k10_lattice3(A_122, k10_lattice3(A_122, C_123, C_123), C_123)=k10_lattice3(A_122, C_123, C_123) | ~v1_lattice3(A_122) | ~v5_orders_2(A_122) | v2_struct_0(A_122) | ~m1_subset_1(C_123, u1_struct_0(A_122)) | ~l1_orders_2(A_122))), inference(resolution, [status(thm)], [c_4, c_141])).
% 15.46/7.33  tff(c_152, plain, (k10_lattice3('#skF_2', k10_lattice3('#skF_2', '#skF_4', '#skF_4'), '#skF_4')=k10_lattice3('#skF_2', '#skF_4', '#skF_4') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_22, c_146])).
% 15.46/7.33  tff(c_159, plain, (k10_lattice3('#skF_2', k10_lattice3('#skF_2', '#skF_4', '#skF_4'), '#skF_4')=k10_lattice3('#skF_2', '#skF_4', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30, c_28, c_152])).
% 15.46/7.33  tff(c_163, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_159])).
% 15.46/7.33  tff(c_2, plain, (![A_1]: (~v2_struct_0(A_1) | ~v1_lattice3(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.46/7.33  tff(c_167, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_163, c_2])).
% 15.46/7.33  tff(c_171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_167])).
% 15.46/7.33  tff(c_173, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_159])).
% 15.46/7.33  tff(c_20, plain, (k10_lattice3('#skF_2', '#skF_3', '#skF_4')!=k10_lattice3('#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.46/7.33  tff(c_24, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.46/7.33  tff(c_825, plain, (![A_143, B_144, C_145]: (k10_lattice3(A_143, k10_lattice3(A_143, B_144, C_145), C_145)=k10_lattice3(A_143, B_144, C_145) | ~r1_orders_2(A_143, B_144, k10_lattice3(A_143, B_144, C_145)) | ~m1_subset_1(k10_lattice3(A_143, B_144, C_145), u1_struct_0(A_143)) | ~v1_lattice3(A_143) | ~v5_orders_2(A_143) | v2_struct_0(A_143) | ~m1_subset_1(C_145, u1_struct_0(A_143)) | ~m1_subset_1(B_144, u1_struct_0(A_143)) | ~l1_orders_2(A_143))), inference(resolution, [status(thm)], [c_40, c_105])).
% 15.46/7.33  tff(c_879, plain, (![A_146, B_147, C_148]: (k10_lattice3(A_146, k10_lattice3(A_146, B_147, C_148), C_148)=k10_lattice3(A_146, B_147, C_148) | ~m1_subset_1(k10_lattice3(A_146, B_147, C_148), u1_struct_0(A_146)) | ~v1_lattice3(A_146) | ~v5_orders_2(A_146) | v2_struct_0(A_146) | ~m1_subset_1(C_148, u1_struct_0(A_146)) | ~m1_subset_1(B_147, u1_struct_0(A_146)) | ~l1_orders_2(A_146))), inference(resolution, [status(thm)], [c_36, c_825])).
% 15.46/7.33  tff(c_984, plain, (![A_151, B_152, C_153]: (k10_lattice3(A_151, k10_lattice3(A_151, B_152, C_153), C_153)=k10_lattice3(A_151, B_152, C_153) | ~v1_lattice3(A_151) | ~v5_orders_2(A_151) | v2_struct_0(A_151) | ~m1_subset_1(C_153, u1_struct_0(A_151)) | ~m1_subset_1(B_152, u1_struct_0(A_151)) | ~l1_orders_2(A_151))), inference(resolution, [status(thm)], [c_4, c_879])).
% 15.46/7.33  tff(c_994, plain, (![B_152]: (k10_lattice3('#skF_2', k10_lattice3('#skF_2', B_152, '#skF_4'), '#skF_4')=k10_lattice3('#skF_2', B_152, '#skF_4') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1(B_152, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_984])).
% 15.46/7.33  tff(c_1009, plain, (![B_152]: (k10_lattice3('#skF_2', k10_lattice3('#skF_2', B_152, '#skF_4'), '#skF_4')=k10_lattice3('#skF_2', B_152, '#skF_4') | v2_struct_0('#skF_2') | ~m1_subset_1(B_152, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30, c_28, c_994])).
% 15.46/7.33  tff(c_1069, plain, (![B_157]: (k10_lattice3('#skF_2', k10_lattice3('#skF_2', B_157, '#skF_4'), '#skF_4')=k10_lattice3('#skF_2', B_157, '#skF_4') | ~m1_subset_1(B_157, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_173, c_1009])).
% 15.46/7.33  tff(c_1102, plain, (k10_lattice3('#skF_2', k10_lattice3('#skF_2', '#skF_3', '#skF_4'), '#skF_4')=k10_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_1069])).
% 15.46/7.33  tff(c_1124, plain, (r1_orders_2('#skF_2', '#skF_4', k10_lattice3('#skF_2', '#skF_3', '#skF_4')) | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1(k10_lattice3('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1102, c_40])).
% 15.46/7.33  tff(c_1154, plain, (r1_orders_2('#skF_2', '#skF_4', k10_lattice3('#skF_2', '#skF_3', '#skF_4')) | v2_struct_0('#skF_2') | ~m1_subset_1(k10_lattice3('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_30, c_28, c_1124])).
% 15.46/7.33  tff(c_1155, plain, (r1_orders_2('#skF_2', '#skF_4', k10_lattice3('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(k10_lattice3('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_173, c_1154])).
% 15.46/7.33  tff(c_1162, plain, (~m1_subset_1(k10_lattice3('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1155])).
% 15.46/7.33  tff(c_1199, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_4, c_1162])).
% 15.46/7.33  tff(c_1203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_1199])).
% 15.46/7.33  tff(c_1205, plain, (m1_subset_1(k10_lattice3('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1155])).
% 15.46/7.33  tff(c_1204, plain, (r1_orders_2('#skF_2', '#skF_4', k10_lattice3('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_1155])).
% 15.46/7.33  tff(c_1127, plain, (r1_orders_2('#skF_2', k10_lattice3('#skF_2', '#skF_3', '#skF_4'), k10_lattice3('#skF_2', '#skF_3', '#skF_4')) | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1(k10_lattice3('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1102, c_36])).
% 15.46/7.33  tff(c_1157, plain, (r1_orders_2('#skF_2', k10_lattice3('#skF_2', '#skF_3', '#skF_4'), k10_lattice3('#skF_2', '#skF_3', '#skF_4')) | v2_struct_0('#skF_2') | ~m1_subset_1(k10_lattice3('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_30, c_28, c_1127])).
% 15.46/7.33  tff(c_1158, plain, (r1_orders_2('#skF_2', k10_lattice3('#skF_2', '#skF_3', '#skF_4'), k10_lattice3('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(k10_lattice3('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_173, c_1157])).
% 15.46/7.33  tff(c_2058, plain, (r1_orders_2('#skF_2', k10_lattice3('#skF_2', '#skF_3', '#skF_4'), k10_lattice3('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1205, c_1158])).
% 15.46/7.33  tff(c_69, plain, (![A_2, B_3, C_4]: (k10_lattice3(A_2, k10_lattice3(A_2, B_3, C_4), B_3)=k10_lattice3(A_2, B_3, C_4) | ~r1_orders_2(A_2, k10_lattice3(A_2, B_3, C_4), k10_lattice3(A_2, B_3, C_4)) | ~m1_subset_1(k10_lattice3(A_2, B_3, C_4), u1_struct_0(A_2)) | ~v1_lattice3(A_2) | ~v5_orders_2(A_2) | v2_struct_0(A_2) | ~m1_subset_1(C_4, u1_struct_0(A_2)) | ~m1_subset_1(B_3, u1_struct_0(A_2)) | ~l1_orders_2(A_2))), inference(resolution, [status(thm)], [c_36, c_57])).
% 15.46/7.33  tff(c_2065, plain, (k10_lattice3('#skF_2', k10_lattice3('#skF_2', '#skF_3', '#skF_4'), '#skF_3')=k10_lattice3('#skF_2', '#skF_3', '#skF_4') | ~m1_subset_1(k10_lattice3('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_2058, c_69])).
% 15.46/7.33  tff(c_2080, plain, (k10_lattice3('#skF_2', k10_lattice3('#skF_2', '#skF_3', '#skF_4'), '#skF_3')=k10_lattice3('#skF_2', '#skF_3', '#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_30, c_28, c_1205, c_2065])).
% 15.46/7.33  tff(c_2081, plain, (k10_lattice3('#skF_2', k10_lattice3('#skF_2', '#skF_3', '#skF_4'), '#skF_3')=k10_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_173, c_2080])).
% 15.46/7.33  tff(c_2117, plain, (r1_orders_2('#skF_2', '#skF_3', k10_lattice3('#skF_2', '#skF_3', '#skF_4')) | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1(k10_lattice3('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2081, c_40])).
% 15.46/7.33  tff(c_2156, plain, (r1_orders_2('#skF_2', '#skF_3', k10_lattice3('#skF_2', '#skF_3', '#skF_4')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1205, c_24, c_30, c_28, c_2117])).
% 15.46/7.33  tff(c_2157, plain, (r1_orders_2('#skF_2', '#skF_3', k10_lattice3('#skF_2', '#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_173, c_2156])).
% 15.46/7.33  tff(c_12, plain, (![A_5, B_29, C_41, D_47]: (m1_subset_1('#skF_1'(A_5, B_29, C_41, D_47), u1_struct_0(A_5)) | k10_lattice3(A_5, B_29, C_41)=D_47 | ~r1_orders_2(A_5, C_41, D_47) | ~r1_orders_2(A_5, B_29, D_47) | ~m1_subset_1(D_47, u1_struct_0(A_5)) | ~m1_subset_1(C_41, u1_struct_0(A_5)) | ~m1_subset_1(B_29, u1_struct_0(A_5)) | ~l1_orders_2(A_5) | ~v1_lattice3(A_5) | ~v5_orders_2(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.46/7.33  tff(c_8, plain, (![A_5, C_41, B_29, D_47]: (r1_orders_2(A_5, C_41, '#skF_1'(A_5, B_29, C_41, D_47)) | k10_lattice3(A_5, B_29, C_41)=D_47 | ~r1_orders_2(A_5, C_41, D_47) | ~r1_orders_2(A_5, B_29, D_47) | ~m1_subset_1(D_47, u1_struct_0(A_5)) | ~m1_subset_1(C_41, u1_struct_0(A_5)) | ~m1_subset_1(B_29, u1_struct_0(A_5)) | ~l1_orders_2(A_5) | ~v1_lattice3(A_5) | ~v5_orders_2(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.46/7.33  tff(c_10, plain, (![A_5, B_29, C_41, D_47]: (r1_orders_2(A_5, B_29, '#skF_1'(A_5, B_29, C_41, D_47)) | k10_lattice3(A_5, B_29, C_41)=D_47 | ~r1_orders_2(A_5, C_41, D_47) | ~r1_orders_2(A_5, B_29, D_47) | ~m1_subset_1(D_47, u1_struct_0(A_5)) | ~m1_subset_1(C_41, u1_struct_0(A_5)) | ~m1_subset_1(B_29, u1_struct_0(A_5)) | ~l1_orders_2(A_5) | ~v1_lattice3(A_5) | ~v5_orders_2(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.46/7.33  tff(c_75, plain, (![A_97, B_98, C_99, E_100]: (r1_orders_2(A_97, k10_lattice3(A_97, B_98, C_99), E_100) | ~r1_orders_2(A_97, C_99, E_100) | ~r1_orders_2(A_97, B_98, E_100) | ~m1_subset_1(E_100, u1_struct_0(A_97)) | ~v1_lattice3(A_97) | ~v5_orders_2(A_97) | v2_struct_0(A_97) | ~m1_subset_1(C_99, u1_struct_0(A_97)) | ~m1_subset_1(B_98, u1_struct_0(A_97)) | ~l1_orders_2(A_97))), inference(resolution, [status(thm)], [c_4, c_71])).
% 15.46/7.33  tff(c_780, plain, (![C_140, A_138, B_142, B_141, C_139]: (k10_lattice3(A_138, B_142, C_139)=k10_lattice3(A_138, B_141, C_140) | ~r1_orders_2(A_138, C_139, k10_lattice3(A_138, B_141, C_140)) | ~r1_orders_2(A_138, B_142, k10_lattice3(A_138, B_141, C_140)) | ~m1_subset_1(k10_lattice3(A_138, B_141, C_140), u1_struct_0(A_138)) | ~m1_subset_1(C_139, u1_struct_0(A_138)) | ~m1_subset_1(B_142, u1_struct_0(A_138)) | ~r1_orders_2(A_138, C_140, '#skF_1'(A_138, B_142, C_139, k10_lattice3(A_138, B_141, C_140))) | ~r1_orders_2(A_138, B_141, '#skF_1'(A_138, B_142, C_139, k10_lattice3(A_138, B_141, C_140))) | ~m1_subset_1('#skF_1'(A_138, B_142, C_139, k10_lattice3(A_138, B_141, C_140)), u1_struct_0(A_138)) | ~v1_lattice3(A_138) | ~v5_orders_2(A_138) | v2_struct_0(A_138) | ~m1_subset_1(C_140, u1_struct_0(A_138)) | ~m1_subset_1(B_141, u1_struct_0(A_138)) | ~l1_orders_2(A_138))), inference(resolution, [status(thm)], [c_75, c_6])).
% 15.46/7.33  tff(c_2327, plain, (![A_170, B_171, B_172, C_173]: (~r1_orders_2(A_170, B_171, '#skF_1'(A_170, B_172, C_173, k10_lattice3(A_170, B_171, B_172))) | ~m1_subset_1('#skF_1'(A_170, B_172, C_173, k10_lattice3(A_170, B_171, B_172)), u1_struct_0(A_170)) | ~m1_subset_1(B_171, u1_struct_0(A_170)) | k10_lattice3(A_170, B_172, C_173)=k10_lattice3(A_170, B_171, B_172) | ~r1_orders_2(A_170, C_173, k10_lattice3(A_170, B_171, B_172)) | ~r1_orders_2(A_170, B_172, k10_lattice3(A_170, B_171, B_172)) | ~m1_subset_1(k10_lattice3(A_170, B_171, B_172), u1_struct_0(A_170)) | ~m1_subset_1(C_173, u1_struct_0(A_170)) | ~m1_subset_1(B_172, u1_struct_0(A_170)) | ~l1_orders_2(A_170) | ~v1_lattice3(A_170) | ~v5_orders_2(A_170) | v2_struct_0(A_170))), inference(resolution, [status(thm)], [c_10, c_780])).
% 15.46/7.33  tff(c_7619, plain, (![A_231, B_232, C_233]: (~m1_subset_1('#skF_1'(A_231, B_232, C_233, k10_lattice3(A_231, C_233, B_232)), u1_struct_0(A_231)) | k10_lattice3(A_231, C_233, B_232)=k10_lattice3(A_231, B_232, C_233) | ~r1_orders_2(A_231, C_233, k10_lattice3(A_231, C_233, B_232)) | ~r1_orders_2(A_231, B_232, k10_lattice3(A_231, C_233, B_232)) | ~m1_subset_1(k10_lattice3(A_231, C_233, B_232), u1_struct_0(A_231)) | ~m1_subset_1(C_233, u1_struct_0(A_231)) | ~m1_subset_1(B_232, u1_struct_0(A_231)) | ~l1_orders_2(A_231) | ~v1_lattice3(A_231) | ~v5_orders_2(A_231) | v2_struct_0(A_231))), inference(resolution, [status(thm)], [c_8, c_2327])).
% 15.46/7.33  tff(c_21697, plain, (![A_330, C_331, B_332]: (k10_lattice3(A_330, C_331, B_332)=k10_lattice3(A_330, B_332, C_331) | ~r1_orders_2(A_330, C_331, k10_lattice3(A_330, C_331, B_332)) | ~r1_orders_2(A_330, B_332, k10_lattice3(A_330, C_331, B_332)) | ~m1_subset_1(k10_lattice3(A_330, C_331, B_332), u1_struct_0(A_330)) | ~m1_subset_1(C_331, u1_struct_0(A_330)) | ~m1_subset_1(B_332, u1_struct_0(A_330)) | ~l1_orders_2(A_330) | ~v1_lattice3(A_330) | ~v5_orders_2(A_330) | v2_struct_0(A_330))), inference(resolution, [status(thm)], [c_12, c_7619])).
% 15.46/7.33  tff(c_21837, plain, (k10_lattice3('#skF_2', '#skF_3', '#skF_4')=k10_lattice3('#skF_2', '#skF_4', '#skF_3') | ~r1_orders_2('#skF_2', '#skF_4', k10_lattice3('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(k10_lattice3('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_2157, c_21697])).
% 15.46/7.33  tff(c_22096, plain, (k10_lattice3('#skF_2', '#skF_3', '#skF_4')=k10_lattice3('#skF_2', '#skF_4', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_22, c_24, c_1205, c_1204, c_21837])).
% 15.46/7.33  tff(c_22098, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_20, c_22096])).
% 15.46/7.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.46/7.33  
% 15.46/7.33  Inference rules
% 15.46/7.33  ----------------------
% 15.46/7.33  #Ref     : 0
% 15.46/7.33  #Sup     : 4246
% 15.46/7.33  #Fact    : 0
% 15.46/7.33  #Define  : 0
% 15.46/7.33  #Split   : 24
% 15.46/7.33  #Chain   : 0
% 15.46/7.33  #Close   : 0
% 15.46/7.33  
% 15.46/7.33  Ordering : KBO
% 15.46/7.33  
% 15.46/7.33  Simplification rules
% 15.46/7.33  ----------------------
% 15.46/7.33  #Subsume      : 206
% 15.46/7.33  #Demod        : 27467
% 15.46/7.33  #Tautology    : 1732
% 15.46/7.33  #SimpNegUnit  : 2720
% 15.46/7.33  #BackRed      : 2
% 15.46/7.33  
% 15.46/7.33  #Partial instantiations: 0
% 15.46/7.33  #Strategies tried      : 1
% 15.46/7.33  
% 15.46/7.33  Timing (in seconds)
% 15.46/7.33  ----------------------
% 15.46/7.33  Preprocessing        : 0.30
% 15.46/7.33  Parsing              : 0.16
% 15.46/7.33  CNF conversion       : 0.03
% 15.46/7.33  Main loop            : 6.25
% 15.46/7.33  Inferencing          : 0.83
% 15.46/7.33  Reduction            : 3.59
% 15.46/7.33  Demodulation         : 3.21
% 15.46/7.33  BG Simplification    : 0.15
% 15.46/7.33  Subsumption          : 1.51
% 15.46/7.33  Abstraction          : 0.33
% 15.46/7.33  MUC search           : 0.00
% 15.46/7.33  Cooper               : 0.00
% 15.46/7.33  Total                : 6.59
% 15.46/7.33  Index Insertion      : 0.00
% 15.46/7.33  Index Deletion       : 0.00
% 15.46/7.33  Index Matching       : 0.00
% 15.46/7.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
