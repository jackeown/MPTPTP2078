%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:01 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 189 expanded)
%              Number of leaves         :   22 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  177 ( 740 expanded)
%              Number of equality atoms :   22 (  87 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_0)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,B,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_77,axiom,(
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

tff(c_26,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_28,plain,(
    v1_lattice3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_295,plain,(
    ! [A_96,B_97] :
      ( r1_orders_2(A_96,B_97,B_97)
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_orders_2(A_96)
      | ~ v3_orders_2(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_297,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_295])).

tff(c_302,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_297])).

tff(c_306,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_302])).

tff(c_4,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_309,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_306,c_4])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_309])).

tff(c_315,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_44,plain,(
    ! [A_59,B_60] :
      ( r1_orders_2(A_59,B_60,B_60)
      | ~ m1_subset_1(B_60,u1_struct_0(A_59))
      | ~ l1_orders_2(A_59)
      | ~ v3_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_44])).

tff(c_51,plain,
    ( r1_orders_2('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_46])).

tff(c_55,plain,(
    v2_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_51])).

tff(c_58,plain,
    ( ~ v1_lattice3('#skF_2')
    | ~ l1_orders_2('#skF_2') ),
    inference(resolution,[status(thm)],[c_55,c_4])).

tff(c_62,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_58])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_30,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_65,plain,(
    ! [A_61,B_62,C_63] :
      ( k13_lattice3(A_61,B_62,C_63) = k10_lattice3(A_61,B_62,C_63)
      | ~ m1_subset_1(C_63,u1_struct_0(A_61))
      | ~ m1_subset_1(B_62,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61)
      | ~ v1_lattice3(A_61)
      | ~ v5_orders_2(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_69,plain,(
    ! [B_62] :
      ( k13_lattice3('#skF_2',B_62,'#skF_4') = k10_lattice3('#skF_2',B_62,'#skF_4')
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_65])).

tff(c_94,plain,(
    ! [B_65] :
      ( k13_lattice3('#skF_2',B_65,'#skF_4') = k10_lattice3('#skF_2',B_65,'#skF_4')
      | ~ m1_subset_1(B_65,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_69])).

tff(c_101,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = k10_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_94])).

tff(c_34,plain,
    ( ~ r1_orders_2('#skF_2','#skF_4','#skF_3')
    | k13_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_103,plain,(
    k10_lattice3('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_42])).

tff(c_63,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_51])).

tff(c_40,plain,
    ( k13_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3'
    | r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_43,plain,(
    r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40])).

tff(c_255,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( r1_orders_2(A_89,B_90,'#skF_1'(A_89,B_90,C_91,D_92))
      | k10_lattice3(A_89,B_90,C_91) = D_92
      | ~ r1_orders_2(A_89,C_91,D_92)
      | ~ r1_orders_2(A_89,B_90,D_92)
      | ~ m1_subset_1(D_92,u1_struct_0(A_89))
      | ~ m1_subset_1(C_91,u1_struct_0(A_89))
      | ~ m1_subset_1(B_90,u1_struct_0(A_89))
      | ~ l1_orders_2(A_89)
      | ~ v1_lattice3(A_89)
      | ~ v5_orders_2(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

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
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_261,plain,(
    ! [A_93,D_94,C_95] :
      ( k10_lattice3(A_93,D_94,C_95) = D_94
      | ~ r1_orders_2(A_93,C_95,D_94)
      | ~ r1_orders_2(A_93,D_94,D_94)
      | ~ m1_subset_1(C_95,u1_struct_0(A_93))
      | ~ m1_subset_1(D_94,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93)
      | ~ v1_lattice3(A_93)
      | ~ v5_orders_2(A_93)
      | v2_struct_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_255,c_6])).

tff(c_271,plain,
    ( k10_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3'
    | ~ r1_orders_2('#skF_2','#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_43,c_261])).

tff(c_284,plain,
    ( k10_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_63,c_271])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_103,c_284])).

tff(c_287,plain,(
    ~ r1_orders_2('#skF_2','#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_288,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_317,plain,(
    ! [A_98,B_99,C_100] :
      ( k13_lattice3(A_98,B_99,C_100) = k10_lattice3(A_98,B_99,C_100)
      | ~ m1_subset_1(C_100,u1_struct_0(A_98))
      | ~ m1_subset_1(B_99,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98)
      | ~ v1_lattice3(A_98)
      | ~ v5_orders_2(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_321,plain,(
    ! [B_99] :
      ( k13_lattice3('#skF_2',B_99,'#skF_4') = k10_lattice3('#skF_2',B_99,'#skF_4')
      | ~ m1_subset_1(B_99,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v1_lattice3('#skF_2')
      | ~ v5_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_317])).

tff(c_346,plain,(
    ! [B_105] :
      ( k13_lattice3('#skF_2',B_105,'#skF_4') = k10_lattice3('#skF_2',B_105,'#skF_4')
      | ~ m1_subset_1(B_105,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_321])).

tff(c_349,plain,(
    k13_lattice3('#skF_2','#skF_3','#skF_4') = k10_lattice3('#skF_2','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_346])).

tff(c_354,plain,(
    k10_lattice3('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_349])).

tff(c_16,plain,(
    ! [A_5,C_41,B_29] :
      ( r1_orders_2(A_5,C_41,k10_lattice3(A_5,B_29,C_41))
      | ~ m1_subset_1(k10_lattice3(A_5,B_29,C_41),u1_struct_0(A_5))
      | ~ m1_subset_1(C_41,u1_struct_0(A_5))
      | ~ m1_subset_1(B_29,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5)
      | ~ v1_lattice3(A_5)
      | ~ v5_orders_2(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_358,plain,
    ( r1_orders_2('#skF_2','#skF_4',k10_lattice3('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | ~ v1_lattice3('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_16])).

tff(c_362,plain,
    ( r1_orders_2('#skF_2','#skF_4','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_22,c_24,c_354,c_358])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_287,c_362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:56:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.48  
% 2.60/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.49  %$ r1_orders_2 > m1_subset_1 > v5_orders_2 > v3_orders_2 > v2_struct_0 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.60/1.49  
% 2.60/1.49  %Foreground sorts:
% 2.60/1.49  
% 2.60/1.49  
% 2.60/1.49  %Background operators:
% 2.60/1.49  
% 2.60/1.49  
% 2.60/1.49  %Foreground operators:
% 2.60/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.60/1.49  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.60/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.49  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 2.60/1.49  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.60/1.49  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 2.60/1.49  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.60/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.49  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.60/1.49  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.60/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.60/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.60/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.60/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.49  
% 2.77/1.50  tff(f_108, negated_conjecture, ~(![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((B = k13_lattice3(A, B, C)) <=> r1_orders_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_yellow_0)).
% 2.77/1.50  tff(f_37, axiom, (![A]: (((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 2.77/1.50  tff(f_44, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 2.77/1.50  tff(f_89, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 2.77/1.50  tff(f_77, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 2.77/1.50  tff(c_26, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.77/1.50  tff(c_28, plain, (v1_lattice3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.77/1.50  tff(c_32, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.77/1.50  tff(c_24, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.77/1.50  tff(c_295, plain, (![A_96, B_97]: (r1_orders_2(A_96, B_97, B_97) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l1_orders_2(A_96) | ~v3_orders_2(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.77/1.50  tff(c_297, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_295])).
% 2.77/1.50  tff(c_302, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_297])).
% 2.77/1.50  tff(c_306, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_302])).
% 2.77/1.50  tff(c_4, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.77/1.50  tff(c_309, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_306, c_4])).
% 2.77/1.50  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_309])).
% 2.77/1.50  tff(c_315, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_302])).
% 2.77/1.50  tff(c_44, plain, (![A_59, B_60]: (r1_orders_2(A_59, B_60, B_60) | ~m1_subset_1(B_60, u1_struct_0(A_59)) | ~l1_orders_2(A_59) | ~v3_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.77/1.50  tff(c_46, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~l1_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_44])).
% 2.77/1.50  tff(c_51, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_46])).
% 2.77/1.50  tff(c_55, plain, (v2_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_51])).
% 2.77/1.50  tff(c_58, plain, (~v1_lattice3('#skF_2') | ~l1_orders_2('#skF_2')), inference(resolution, [status(thm)], [c_55, c_4])).
% 2.77/1.50  tff(c_62, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_58])).
% 2.77/1.50  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_51])).
% 2.77/1.50  tff(c_30, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.77/1.50  tff(c_22, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.77/1.50  tff(c_65, plain, (![A_61, B_62, C_63]: (k13_lattice3(A_61, B_62, C_63)=k10_lattice3(A_61, B_62, C_63) | ~m1_subset_1(C_63, u1_struct_0(A_61)) | ~m1_subset_1(B_62, u1_struct_0(A_61)) | ~l1_orders_2(A_61) | ~v1_lattice3(A_61) | ~v5_orders_2(A_61))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.77/1.50  tff(c_69, plain, (![B_62]: (k13_lattice3('#skF_2', B_62, '#skF_4')=k10_lattice3('#skF_2', B_62, '#skF_4') | ~m1_subset_1(B_62, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_65])).
% 2.77/1.50  tff(c_94, plain, (![B_65]: (k13_lattice3('#skF_2', B_65, '#skF_4')=k10_lattice3('#skF_2', B_65, '#skF_4') | ~m1_subset_1(B_65, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_69])).
% 2.77/1.50  tff(c_101, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')=k10_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_94])).
% 2.77/1.50  tff(c_34, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3') | k13_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.77/1.50  tff(c_42, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_34])).
% 2.77/1.50  tff(c_103, plain, (k10_lattice3('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_42])).
% 2.77/1.50  tff(c_63, plain, (r1_orders_2('#skF_2', '#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_51])).
% 2.77/1.50  tff(c_40, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3' | r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.77/1.50  tff(c_43, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_40])).
% 2.77/1.50  tff(c_255, plain, (![A_89, B_90, C_91, D_92]: (r1_orders_2(A_89, B_90, '#skF_1'(A_89, B_90, C_91, D_92)) | k10_lattice3(A_89, B_90, C_91)=D_92 | ~r1_orders_2(A_89, C_91, D_92) | ~r1_orders_2(A_89, B_90, D_92) | ~m1_subset_1(D_92, u1_struct_0(A_89)) | ~m1_subset_1(C_91, u1_struct_0(A_89)) | ~m1_subset_1(B_90, u1_struct_0(A_89)) | ~l1_orders_2(A_89) | ~v1_lattice3(A_89) | ~v5_orders_2(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.77/1.50  tff(c_6, plain, (![A_5, D_47, B_29, C_41]: (~r1_orders_2(A_5, D_47, '#skF_1'(A_5, B_29, C_41, D_47)) | k10_lattice3(A_5, B_29, C_41)=D_47 | ~r1_orders_2(A_5, C_41, D_47) | ~r1_orders_2(A_5, B_29, D_47) | ~m1_subset_1(D_47, u1_struct_0(A_5)) | ~m1_subset_1(C_41, u1_struct_0(A_5)) | ~m1_subset_1(B_29, u1_struct_0(A_5)) | ~l1_orders_2(A_5) | ~v1_lattice3(A_5) | ~v5_orders_2(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.77/1.50  tff(c_261, plain, (![A_93, D_94, C_95]: (k10_lattice3(A_93, D_94, C_95)=D_94 | ~r1_orders_2(A_93, C_95, D_94) | ~r1_orders_2(A_93, D_94, D_94) | ~m1_subset_1(C_95, u1_struct_0(A_93)) | ~m1_subset_1(D_94, u1_struct_0(A_93)) | ~l1_orders_2(A_93) | ~v1_lattice3(A_93) | ~v5_orders_2(A_93) | v2_struct_0(A_93))), inference(resolution, [status(thm)], [c_255, c_6])).
% 2.77/1.50  tff(c_271, plain, (k10_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3' | ~r1_orders_2('#skF_2', '#skF_3', '#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_43, c_261])).
% 2.77/1.50  tff(c_284, plain, (k10_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_63, c_271])).
% 2.77/1.50  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_103, c_284])).
% 2.77/1.50  tff(c_287, plain, (~r1_orders_2('#skF_2', '#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.77/1.50  tff(c_288, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 2.77/1.50  tff(c_317, plain, (![A_98, B_99, C_100]: (k13_lattice3(A_98, B_99, C_100)=k10_lattice3(A_98, B_99, C_100) | ~m1_subset_1(C_100, u1_struct_0(A_98)) | ~m1_subset_1(B_99, u1_struct_0(A_98)) | ~l1_orders_2(A_98) | ~v1_lattice3(A_98) | ~v5_orders_2(A_98))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.77/1.50  tff(c_321, plain, (![B_99]: (k13_lattice3('#skF_2', B_99, '#skF_4')=k10_lattice3('#skF_2', B_99, '#skF_4') | ~m1_subset_1(B_99, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_317])).
% 2.77/1.50  tff(c_346, plain, (![B_105]: (k13_lattice3('#skF_2', B_105, '#skF_4')=k10_lattice3('#skF_2', B_105, '#skF_4') | ~m1_subset_1(B_105, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_321])).
% 2.77/1.50  tff(c_349, plain, (k13_lattice3('#skF_2', '#skF_3', '#skF_4')=k10_lattice3('#skF_2', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_346])).
% 2.77/1.50  tff(c_354, plain, (k10_lattice3('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_288, c_349])).
% 2.77/1.50  tff(c_16, plain, (![A_5, C_41, B_29]: (r1_orders_2(A_5, C_41, k10_lattice3(A_5, B_29, C_41)) | ~m1_subset_1(k10_lattice3(A_5, B_29, C_41), u1_struct_0(A_5)) | ~m1_subset_1(C_41, u1_struct_0(A_5)) | ~m1_subset_1(B_29, u1_struct_0(A_5)) | ~l1_orders_2(A_5) | ~v1_lattice3(A_5) | ~v5_orders_2(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.77/1.50  tff(c_358, plain, (r1_orders_2('#skF_2', '#skF_4', k10_lattice3('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v1_lattice3('#skF_2') | ~v5_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_354, c_16])).
% 2.77/1.50  tff(c_362, plain, (r1_orders_2('#skF_2', '#skF_4', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_22, c_24, c_354, c_358])).
% 2.77/1.50  tff(c_364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_315, c_287, c_362])).
% 2.77/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.50  
% 2.77/1.50  Inference rules
% 2.77/1.50  ----------------------
% 2.77/1.50  #Ref     : 0
% 2.77/1.50  #Sup     : 72
% 2.77/1.50  #Fact    : 0
% 2.77/1.50  #Define  : 0
% 2.77/1.50  #Split   : 4
% 2.77/1.50  #Chain   : 0
% 2.77/1.50  #Close   : 0
% 2.77/1.50  
% 2.77/1.50  Ordering : KBO
% 2.77/1.50  
% 2.77/1.50  Simplification rules
% 2.77/1.50  ----------------------
% 2.77/1.50  #Subsume      : 0
% 2.77/1.50  #Demod        : 126
% 2.77/1.50  #Tautology    : 38
% 2.77/1.50  #SimpNegUnit  : 20
% 2.77/1.50  #BackRed      : 4
% 2.77/1.50  
% 2.77/1.50  #Partial instantiations: 0
% 2.77/1.50  #Strategies tried      : 1
% 2.77/1.50  
% 2.77/1.50  Timing (in seconds)
% 2.77/1.50  ----------------------
% 2.77/1.51  Preprocessing        : 0.41
% 2.77/1.51  Parsing              : 0.21
% 2.77/1.51  CNF conversion       : 0.03
% 2.77/1.51  Main loop            : 0.25
% 2.77/1.51  Inferencing          : 0.09
% 2.77/1.51  Reduction            : 0.08
% 2.77/1.51  Demodulation         : 0.05
% 2.77/1.51  BG Simplification    : 0.02
% 2.77/1.51  Subsumption          : 0.05
% 2.77/1.51  Abstraction          : 0.02
% 2.77/1.51  MUC search           : 0.00
% 2.77/1.51  Cooper               : 0.00
% 2.77/1.51  Total                : 0.69
% 2.77/1.51  Index Insertion      : 0.00
% 2.77/1.51  Index Deletion       : 0.00
% 2.77/1.51  Index Matching       : 0.00
% 2.77/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
