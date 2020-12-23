%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:47 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 303 expanded)
%              Number of leaves         :   38 ( 121 expanded)
%              Depth                    :   14
%              Number of atoms          :  336 (1361 expanded)
%              Number of equality atoms :   26 (  94 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k1_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_165,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( ( r2_hidden(B,C)
                  & r3_lattice3(A,B,C) )
               => k16_lattice3(A,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

tff(f_47,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_lattices(A,B,C)
      <=> r1_lattices(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(f_68,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_145,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r3_lattice3(A,B,C)
             => r3_lattices(A,B,k16_lattice3(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattice3)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ( v4_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,B,C) = k1_lattices(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_lattices)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r2_hidden(B,C)
             => ( r3_lattices(A,B,k15_lattice3(A,C))
                & r3_lattices(A,k16_lattice3(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_lattice3)).

tff(c_44,plain,(
    k16_lattice3('#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_48,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_46,plain,(
    r3_lattice3('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_52,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_56,plain,(
    v10_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_54,plain,(
    v4_lattice3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_236,plain,(
    ! [A_87,B_88,C_89] :
      ( r3_lattices(A_87,B_88,C_89)
      | ~ r1_lattices(A_87,B_88,C_89)
      | ~ m1_subset_1(C_89,u1_struct_0(A_87))
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | ~ l3_lattices(A_87)
      | ~ v9_lattices(A_87)
      | ~ v8_lattices(A_87)
      | ~ v6_lattices(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_244,plain,(
    ! [B_88] :
      ( r3_lattices('#skF_3',B_88,'#skF_4')
      | ~ r1_lattices('#skF_3',B_88,'#skF_4')
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_3'))
      | ~ l3_lattices('#skF_3')
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_236])).

tff(c_250,plain,(
    ! [B_88] :
      ( r3_lattices('#skF_3',B_88,'#skF_4')
      | ~ r1_lattices('#skF_3',B_88,'#skF_4')
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_244])).

tff(c_251,plain,(
    ! [B_88] :
      ( r3_lattices('#skF_3',B_88,'#skF_4')
      | ~ r1_lattices('#skF_3',B_88,'#skF_4')
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_3'))
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | ~ v6_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_250])).

tff(c_252,plain,(
    ~ v6_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_251])).

tff(c_255,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_252])).

tff(c_258,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_255])).

tff(c_260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_258])).

tff(c_262,plain,(
    v6_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_261,plain,(
    ! [B_88] :
      ( ~ v8_lattices('#skF_3')
      | ~ v9_lattices('#skF_3')
      | r3_lattices('#skF_3',B_88,'#skF_4')
      | ~ r1_lattices('#skF_3',B_88,'#skF_4')
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_251])).

tff(c_263,plain,(
    ~ v9_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_261])).

tff(c_266,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_263])).

tff(c_269,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_266])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_269])).

tff(c_272,plain,(
    ! [B_88] :
      ( ~ v8_lattices('#skF_3')
      | r3_lattices('#skF_3',B_88,'#skF_4')
      | ~ r1_lattices('#skF_3',B_88,'#skF_4')
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_274,plain,(
    ~ v8_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_272])).

tff(c_277,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_274])).

tff(c_280,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_277])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_280])).

tff(c_284,plain,(
    v8_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_273,plain,(
    v9_lattices('#skF_3') ),
    inference(splitRight,[status(thm)],[c_261])).

tff(c_59,plain,(
    ! [A_44] :
      ( l2_lattices(A_44)
      | ~ l3_lattices(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_63,plain,(
    l2_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_59])).

tff(c_36,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k16_lattice3(A_24,B_25),u1_struct_0(A_24))
      | ~ l3_lattices(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_42,plain,(
    ! [A_33,B_37,C_39] :
      ( r3_lattices(A_33,B_37,k16_lattice3(A_33,C_39))
      | ~ r3_lattice3(A_33,B_37,C_39)
      | ~ m1_subset_1(B_37,u1_struct_0(A_33))
      | ~ l3_lattices(A_33)
      | ~ v4_lattice3(A_33)
      | ~ v10_lattices(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_285,plain,(
    ! [A_90,B_91,C_92] :
      ( r1_lattices(A_90,B_91,C_92)
      | ~ r3_lattices(A_90,B_91,C_92)
      | ~ m1_subset_1(C_92,u1_struct_0(A_90))
      | ~ m1_subset_1(B_91,u1_struct_0(A_90))
      | ~ l3_lattices(A_90)
      | ~ v9_lattices(A_90)
      | ~ v8_lattices(A_90)
      | ~ v6_lattices(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_390,plain,(
    ! [A_117,B_118,C_119] :
      ( r1_lattices(A_117,B_118,k16_lattice3(A_117,C_119))
      | ~ m1_subset_1(k16_lattice3(A_117,C_119),u1_struct_0(A_117))
      | ~ v9_lattices(A_117)
      | ~ v8_lattices(A_117)
      | ~ v6_lattices(A_117)
      | ~ r3_lattice3(A_117,B_118,C_119)
      | ~ m1_subset_1(B_118,u1_struct_0(A_117))
      | ~ l3_lattices(A_117)
      | ~ v4_lattice3(A_117)
      | ~ v10_lattices(A_117)
      | v2_struct_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_42,c_285])).

tff(c_394,plain,(
    ! [A_120,B_121,B_122] :
      ( r1_lattices(A_120,B_121,k16_lattice3(A_120,B_122))
      | ~ v9_lattices(A_120)
      | ~ v8_lattices(A_120)
      | ~ v6_lattices(A_120)
      | ~ r3_lattice3(A_120,B_121,B_122)
      | ~ m1_subset_1(B_121,u1_struct_0(A_120))
      | ~ v4_lattice3(A_120)
      | ~ v10_lattices(A_120)
      | ~ l3_lattices(A_120)
      | v2_struct_0(A_120) ) ),
    inference(resolution,[status(thm)],[c_36,c_390])).

tff(c_18,plain,(
    ! [A_2,B_6,C_8] :
      ( k1_lattices(A_2,B_6,C_8) = C_8
      | ~ r1_lattices(A_2,B_6,C_8)
      | ~ m1_subset_1(C_8,u1_struct_0(A_2))
      | ~ m1_subset_1(B_6,u1_struct_0(A_2))
      | ~ l2_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_448,plain,(
    ! [A_133,B_134,B_135] :
      ( k1_lattices(A_133,B_134,k16_lattice3(A_133,B_135)) = k16_lattice3(A_133,B_135)
      | ~ m1_subset_1(k16_lattice3(A_133,B_135),u1_struct_0(A_133))
      | ~ l2_lattices(A_133)
      | ~ v9_lattices(A_133)
      | ~ v8_lattices(A_133)
      | ~ v6_lattices(A_133)
      | ~ r3_lattice3(A_133,B_134,B_135)
      | ~ m1_subset_1(B_134,u1_struct_0(A_133))
      | ~ v4_lattice3(A_133)
      | ~ v10_lattices(A_133)
      | ~ l3_lattices(A_133)
      | v2_struct_0(A_133) ) ),
    inference(resolution,[status(thm)],[c_394,c_18])).

tff(c_452,plain,(
    ! [A_136,B_137,B_138] :
      ( k1_lattices(A_136,B_137,k16_lattice3(A_136,B_138)) = k16_lattice3(A_136,B_138)
      | ~ l2_lattices(A_136)
      | ~ v9_lattices(A_136)
      | ~ v8_lattices(A_136)
      | ~ v6_lattices(A_136)
      | ~ r3_lattice3(A_136,B_137,B_138)
      | ~ m1_subset_1(B_137,u1_struct_0(A_136))
      | ~ v4_lattice3(A_136)
      | ~ v10_lattices(A_136)
      | ~ l3_lattices(A_136)
      | v2_struct_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_36,c_448])).

tff(c_460,plain,(
    ! [B_138] :
      ( k1_lattices('#skF_3','#skF_4',k16_lattice3('#skF_3',B_138)) = k16_lattice3('#skF_3',B_138)
      | ~ l2_lattices('#skF_3')
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | ~ r3_lattice3('#skF_3','#skF_4',B_138)
      | ~ v4_lattice3('#skF_3')
      | ~ v10_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_452])).

tff(c_466,plain,(
    ! [B_138] :
      ( k1_lattices('#skF_3','#skF_4',k16_lattice3('#skF_3',B_138)) = k16_lattice3('#skF_3',B_138)
      | ~ r3_lattice3('#skF_3','#skF_4',B_138)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_54,c_262,c_284,c_273,c_63,c_460])).

tff(c_468,plain,(
    ! [B_139] :
      ( k1_lattices('#skF_3','#skF_4',k16_lattice3('#skF_3',B_139)) = k16_lattice3('#skF_3',B_139)
      | ~ r3_lattice3('#skF_3','#skF_4',B_139) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_466])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_137,plain,(
    ! [A_71,C_72,B_73] :
      ( k1_lattices(A_71,C_72,B_73) = k1_lattices(A_71,B_73,C_72)
      | ~ m1_subset_1(C_72,u1_struct_0(A_71))
      | ~ m1_subset_1(B_73,u1_struct_0(A_71))
      | ~ v4_lattices(A_71)
      | ~ l2_lattices(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_145,plain,(
    ! [B_73] :
      ( k1_lattices('#skF_3',B_73,'#skF_4') = k1_lattices('#skF_3','#skF_4',B_73)
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3')
      | ~ l2_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_137])).

tff(c_151,plain,(
    ! [B_73] :
      ( k1_lattices('#skF_3',B_73,'#skF_4') = k1_lattices('#skF_3','#skF_4',B_73)
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_145])).

tff(c_152,plain,(
    ! [B_73] :
      ( k1_lattices('#skF_3',B_73,'#skF_4') = k1_lattices('#skF_3','#skF_4',B_73)
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_3'))
      | ~ v4_lattices('#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_151])).

tff(c_154,plain,(
    ~ v4_lattices('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_157,plain,
    ( ~ v10_lattices('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l3_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_154])).

tff(c_160,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_157])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_160])).

tff(c_165,plain,(
    ! [B_77] :
      ( k1_lattices('#skF_3',B_77,'#skF_4') = k1_lattices('#skF_3','#skF_4',B_77)
      | ~ m1_subset_1(B_77,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_177,plain,(
    ! [B_25] :
      ( k1_lattices('#skF_3',k16_lattice3('#skF_3',B_25),'#skF_4') = k1_lattices('#skF_3','#skF_4',k16_lattice3('#skF_3',B_25))
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_36,c_165])).

tff(c_191,plain,(
    ! [B_25] :
      ( k1_lattices('#skF_3',k16_lattice3('#skF_3',B_25),'#skF_4') = k1_lattices('#skF_3','#skF_4',k16_lattice3('#skF_3',B_25))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_177])).

tff(c_192,plain,(
    ! [B_25] : k1_lattices('#skF_3',k16_lattice3('#skF_3',B_25),'#skF_4') = k1_lattices('#skF_3','#skF_4',k16_lattice3('#skF_3',B_25)) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_191])).

tff(c_38,plain,(
    ! [A_26,C_32,B_30] :
      ( r3_lattices(A_26,k16_lattice3(A_26,C_32),B_30)
      | ~ r2_hidden(B_30,C_32)
      | ~ m1_subset_1(B_30,u1_struct_0(A_26))
      | ~ l3_lattices(A_26)
      | ~ v4_lattice3(A_26)
      | ~ v10_lattices(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_382,plain,(
    ! [A_111,C_112,B_113] :
      ( r1_lattices(A_111,k16_lattice3(A_111,C_112),B_113)
      | ~ m1_subset_1(k16_lattice3(A_111,C_112),u1_struct_0(A_111))
      | ~ v9_lattices(A_111)
      | ~ v8_lattices(A_111)
      | ~ v6_lattices(A_111)
      | ~ r2_hidden(B_113,C_112)
      | ~ m1_subset_1(B_113,u1_struct_0(A_111))
      | ~ l3_lattices(A_111)
      | ~ v4_lattice3(A_111)
      | ~ v10_lattices(A_111)
      | v2_struct_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_38,c_285])).

tff(c_386,plain,(
    ! [A_114,B_115,B_116] :
      ( r1_lattices(A_114,k16_lattice3(A_114,B_115),B_116)
      | ~ v9_lattices(A_114)
      | ~ v8_lattices(A_114)
      | ~ v6_lattices(A_114)
      | ~ r2_hidden(B_116,B_115)
      | ~ m1_subset_1(B_116,u1_struct_0(A_114))
      | ~ v4_lattice3(A_114)
      | ~ v10_lattices(A_114)
      | ~ l3_lattices(A_114)
      | v2_struct_0(A_114) ) ),
    inference(resolution,[status(thm)],[c_36,c_382])).

tff(c_398,plain,(
    ! [A_123,B_124,B_125] :
      ( k1_lattices(A_123,k16_lattice3(A_123,B_124),B_125) = B_125
      | ~ m1_subset_1(k16_lattice3(A_123,B_124),u1_struct_0(A_123))
      | ~ l2_lattices(A_123)
      | ~ v9_lattices(A_123)
      | ~ v8_lattices(A_123)
      | ~ v6_lattices(A_123)
      | ~ r2_hidden(B_125,B_124)
      | ~ m1_subset_1(B_125,u1_struct_0(A_123))
      | ~ v4_lattice3(A_123)
      | ~ v10_lattices(A_123)
      | ~ l3_lattices(A_123)
      | v2_struct_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_386,c_18])).

tff(c_402,plain,(
    ! [A_126,B_127,B_128] :
      ( k1_lattices(A_126,k16_lattice3(A_126,B_127),B_128) = B_128
      | ~ l2_lattices(A_126)
      | ~ v9_lattices(A_126)
      | ~ v8_lattices(A_126)
      | ~ v6_lattices(A_126)
      | ~ r2_hidden(B_128,B_127)
      | ~ m1_subset_1(B_128,u1_struct_0(A_126))
      | ~ v4_lattice3(A_126)
      | ~ v10_lattices(A_126)
      | ~ l3_lattices(A_126)
      | v2_struct_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_36,c_398])).

tff(c_410,plain,(
    ! [B_127] :
      ( k1_lattices('#skF_3',k16_lattice3('#skF_3',B_127),'#skF_4') = '#skF_4'
      | ~ l2_lattices('#skF_3')
      | ~ v9_lattices('#skF_3')
      | ~ v8_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | ~ r2_hidden('#skF_4',B_127)
      | ~ v4_lattice3('#skF_3')
      | ~ v10_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_402])).

tff(c_416,plain,(
    ! [B_127] :
      ( k1_lattices('#skF_3','#skF_4',k16_lattice3('#skF_3',B_127)) = '#skF_4'
      | ~ r2_hidden('#skF_4',B_127)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_54,c_262,c_284,c_273,c_63,c_192,c_410])).

tff(c_417,plain,(
    ! [B_127] :
      ( k1_lattices('#skF_3','#skF_4',k16_lattice3('#skF_3',B_127)) = '#skF_4'
      | ~ r2_hidden('#skF_4',B_127) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_416])).

tff(c_483,plain,(
    ! [B_140] :
      ( k16_lattice3('#skF_3',B_140) = '#skF_4'
      | ~ r2_hidden('#skF_4',B_140)
      | ~ r3_lattice3('#skF_3','#skF_4',B_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_417])).

tff(c_486,plain,
    ( k16_lattice3('#skF_3','#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_483])).

tff(c_489,plain,(
    k16_lattice3('#skF_3','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_486])).

tff(c_491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.53  
% 3.23/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.53  %$ r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k1_lattices > k16_lattice3 > k15_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.23/1.53  
% 3.23/1.53  %Foreground sorts:
% 3.23/1.53  
% 3.23/1.53  
% 3.23/1.53  %Background operators:
% 3.23/1.53  
% 3.23/1.53  
% 3.23/1.53  %Foreground operators:
% 3.23/1.53  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.23/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.23/1.53  tff(l2_lattices, type, l2_lattices: $i > $o).
% 3.23/1.53  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.23/1.53  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 3.23/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.53  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.23/1.53  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 3.23/1.53  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 3.23/1.53  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 3.23/1.53  tff(l1_lattices, type, l1_lattices: $i > $o).
% 3.23/1.53  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.23/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.23/1.53  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.23/1.53  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.23/1.53  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.23/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.53  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 3.23/1.53  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.23/1.53  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.23/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.53  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.23/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.23/1.53  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 3.23/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.53  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.23/1.53  
% 3.30/1.55  tff(f_165, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r3_lattice3(A, B, C)) => (k16_lattice3(A, C) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_lattice3)).
% 3.30/1.55  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 3.30/1.55  tff(f_87, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 3.30/1.55  tff(f_68, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 3.30/1.55  tff(f_109, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 3.30/1.55  tff(f_145, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) => r3_lattices(A, B, k16_lattice3(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_lattice3)).
% 3.30/1.55  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 3.30/1.55  tff(f_102, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (v4_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, B, C) = k1_lattices(A, C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_lattices)).
% 3.30/1.55  tff(f_128, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 3.30/1.55  tff(c_44, plain, (k16_lattice3('#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.30/1.55  tff(c_48, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.30/1.55  tff(c_46, plain, (r3_lattice3('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.30/1.55  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.30/1.55  tff(c_52, plain, (l3_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.30/1.55  tff(c_56, plain, (v10_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.30/1.55  tff(c_54, plain, (v4_lattice3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.30/1.55  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.55  tff(c_50, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.30/1.55  tff(c_236, plain, (![A_87, B_88, C_89]: (r3_lattices(A_87, B_88, C_89) | ~r1_lattices(A_87, B_88, C_89) | ~m1_subset_1(C_89, u1_struct_0(A_87)) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | ~l3_lattices(A_87) | ~v9_lattices(A_87) | ~v8_lattices(A_87) | ~v6_lattices(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.30/1.55  tff(c_244, plain, (![B_88]: (r3_lattices('#skF_3', B_88, '#skF_4') | ~r1_lattices('#skF_3', B_88, '#skF_4') | ~m1_subset_1(B_88, u1_struct_0('#skF_3')) | ~l3_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_236])).
% 3.30/1.55  tff(c_250, plain, (![B_88]: (r3_lattices('#skF_3', B_88, '#skF_4') | ~r1_lattices('#skF_3', B_88, '#skF_4') | ~m1_subset_1(B_88, u1_struct_0('#skF_3')) | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_244])).
% 3.30/1.55  tff(c_251, plain, (![B_88]: (r3_lattices('#skF_3', B_88, '#skF_4') | ~r1_lattices('#skF_3', B_88, '#skF_4') | ~m1_subset_1(B_88, u1_struct_0('#skF_3')) | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_250])).
% 3.30/1.55  tff(c_252, plain, (~v6_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_251])).
% 3.30/1.55  tff(c_255, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_8, c_252])).
% 3.30/1.55  tff(c_258, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_255])).
% 3.30/1.55  tff(c_260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_258])).
% 3.30/1.55  tff(c_262, plain, (v6_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_251])).
% 3.30/1.55  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.55  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.55  tff(c_261, plain, (![B_88]: (~v8_lattices('#skF_3') | ~v9_lattices('#skF_3') | r3_lattices('#skF_3', B_88, '#skF_4') | ~r1_lattices('#skF_3', B_88, '#skF_4') | ~m1_subset_1(B_88, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_251])).
% 3.30/1.55  tff(c_263, plain, (~v9_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_261])).
% 3.30/1.55  tff(c_266, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_2, c_263])).
% 3.30/1.55  tff(c_269, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_266])).
% 3.30/1.55  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_269])).
% 3.30/1.55  tff(c_272, plain, (![B_88]: (~v8_lattices('#skF_3') | r3_lattices('#skF_3', B_88, '#skF_4') | ~r1_lattices('#skF_3', B_88, '#skF_4') | ~m1_subset_1(B_88, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_261])).
% 3.30/1.55  tff(c_274, plain, (~v8_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_272])).
% 3.30/1.55  tff(c_277, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_4, c_274])).
% 3.30/1.55  tff(c_280, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_277])).
% 3.30/1.55  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_280])).
% 3.30/1.55  tff(c_284, plain, (v8_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_272])).
% 3.30/1.55  tff(c_273, plain, (v9_lattices('#skF_3')), inference(splitRight, [status(thm)], [c_261])).
% 3.30/1.55  tff(c_59, plain, (![A_44]: (l2_lattices(A_44) | ~l3_lattices(A_44))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.30/1.55  tff(c_63, plain, (l2_lattices('#skF_3')), inference(resolution, [status(thm)], [c_52, c_59])).
% 3.30/1.55  tff(c_36, plain, (![A_24, B_25]: (m1_subset_1(k16_lattice3(A_24, B_25), u1_struct_0(A_24)) | ~l3_lattices(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.30/1.55  tff(c_42, plain, (![A_33, B_37, C_39]: (r3_lattices(A_33, B_37, k16_lattice3(A_33, C_39)) | ~r3_lattice3(A_33, B_37, C_39) | ~m1_subset_1(B_37, u1_struct_0(A_33)) | ~l3_lattices(A_33) | ~v4_lattice3(A_33) | ~v10_lattices(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.30/1.55  tff(c_285, plain, (![A_90, B_91, C_92]: (r1_lattices(A_90, B_91, C_92) | ~r3_lattices(A_90, B_91, C_92) | ~m1_subset_1(C_92, u1_struct_0(A_90)) | ~m1_subset_1(B_91, u1_struct_0(A_90)) | ~l3_lattices(A_90) | ~v9_lattices(A_90) | ~v8_lattices(A_90) | ~v6_lattices(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.30/1.55  tff(c_390, plain, (![A_117, B_118, C_119]: (r1_lattices(A_117, B_118, k16_lattice3(A_117, C_119)) | ~m1_subset_1(k16_lattice3(A_117, C_119), u1_struct_0(A_117)) | ~v9_lattices(A_117) | ~v8_lattices(A_117) | ~v6_lattices(A_117) | ~r3_lattice3(A_117, B_118, C_119) | ~m1_subset_1(B_118, u1_struct_0(A_117)) | ~l3_lattices(A_117) | ~v4_lattice3(A_117) | ~v10_lattices(A_117) | v2_struct_0(A_117))), inference(resolution, [status(thm)], [c_42, c_285])).
% 3.30/1.55  tff(c_394, plain, (![A_120, B_121, B_122]: (r1_lattices(A_120, B_121, k16_lattice3(A_120, B_122)) | ~v9_lattices(A_120) | ~v8_lattices(A_120) | ~v6_lattices(A_120) | ~r3_lattice3(A_120, B_121, B_122) | ~m1_subset_1(B_121, u1_struct_0(A_120)) | ~v4_lattice3(A_120) | ~v10_lattices(A_120) | ~l3_lattices(A_120) | v2_struct_0(A_120))), inference(resolution, [status(thm)], [c_36, c_390])).
% 3.30/1.55  tff(c_18, plain, (![A_2, B_6, C_8]: (k1_lattices(A_2, B_6, C_8)=C_8 | ~r1_lattices(A_2, B_6, C_8) | ~m1_subset_1(C_8, u1_struct_0(A_2)) | ~m1_subset_1(B_6, u1_struct_0(A_2)) | ~l2_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.30/1.55  tff(c_448, plain, (![A_133, B_134, B_135]: (k1_lattices(A_133, B_134, k16_lattice3(A_133, B_135))=k16_lattice3(A_133, B_135) | ~m1_subset_1(k16_lattice3(A_133, B_135), u1_struct_0(A_133)) | ~l2_lattices(A_133) | ~v9_lattices(A_133) | ~v8_lattices(A_133) | ~v6_lattices(A_133) | ~r3_lattice3(A_133, B_134, B_135) | ~m1_subset_1(B_134, u1_struct_0(A_133)) | ~v4_lattice3(A_133) | ~v10_lattices(A_133) | ~l3_lattices(A_133) | v2_struct_0(A_133))), inference(resolution, [status(thm)], [c_394, c_18])).
% 3.30/1.55  tff(c_452, plain, (![A_136, B_137, B_138]: (k1_lattices(A_136, B_137, k16_lattice3(A_136, B_138))=k16_lattice3(A_136, B_138) | ~l2_lattices(A_136) | ~v9_lattices(A_136) | ~v8_lattices(A_136) | ~v6_lattices(A_136) | ~r3_lattice3(A_136, B_137, B_138) | ~m1_subset_1(B_137, u1_struct_0(A_136)) | ~v4_lattice3(A_136) | ~v10_lattices(A_136) | ~l3_lattices(A_136) | v2_struct_0(A_136))), inference(resolution, [status(thm)], [c_36, c_448])).
% 3.30/1.55  tff(c_460, plain, (![B_138]: (k1_lattices('#skF_3', '#skF_4', k16_lattice3('#skF_3', B_138))=k16_lattice3('#skF_3', B_138) | ~l2_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | ~r3_lattice3('#skF_3', '#skF_4', B_138) | ~v4_lattice3('#skF_3') | ~v10_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_452])).
% 3.30/1.55  tff(c_466, plain, (![B_138]: (k1_lattices('#skF_3', '#skF_4', k16_lattice3('#skF_3', B_138))=k16_lattice3('#skF_3', B_138) | ~r3_lattice3('#skF_3', '#skF_4', B_138) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_54, c_262, c_284, c_273, c_63, c_460])).
% 3.30/1.55  tff(c_468, plain, (![B_139]: (k1_lattices('#skF_3', '#skF_4', k16_lattice3('#skF_3', B_139))=k16_lattice3('#skF_3', B_139) | ~r3_lattice3('#skF_3', '#skF_4', B_139))), inference(negUnitSimplification, [status(thm)], [c_58, c_466])).
% 3.30/1.55  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.55  tff(c_137, plain, (![A_71, C_72, B_73]: (k1_lattices(A_71, C_72, B_73)=k1_lattices(A_71, B_73, C_72) | ~m1_subset_1(C_72, u1_struct_0(A_71)) | ~m1_subset_1(B_73, u1_struct_0(A_71)) | ~v4_lattices(A_71) | ~l2_lattices(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.30/1.55  tff(c_145, plain, (![B_73]: (k1_lattices('#skF_3', B_73, '#skF_4')=k1_lattices('#skF_3', '#skF_4', B_73) | ~m1_subset_1(B_73, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3') | ~l2_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_137])).
% 3.30/1.55  tff(c_151, plain, (![B_73]: (k1_lattices('#skF_3', B_73, '#skF_4')=k1_lattices('#skF_3', '#skF_4', B_73) | ~m1_subset_1(B_73, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_145])).
% 3.30/1.55  tff(c_152, plain, (![B_73]: (k1_lattices('#skF_3', B_73, '#skF_4')=k1_lattices('#skF_3', '#skF_4', B_73) | ~m1_subset_1(B_73, u1_struct_0('#skF_3')) | ~v4_lattices('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_151])).
% 3.30/1.55  tff(c_154, plain, (~v4_lattices('#skF_3')), inference(splitLeft, [status(thm)], [c_152])).
% 3.30/1.55  tff(c_157, plain, (~v10_lattices('#skF_3') | v2_struct_0('#skF_3') | ~l3_lattices('#skF_3')), inference(resolution, [status(thm)], [c_12, c_154])).
% 3.30/1.55  tff(c_160, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_157])).
% 3.30/1.55  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_160])).
% 3.30/1.55  tff(c_165, plain, (![B_77]: (k1_lattices('#skF_3', B_77, '#skF_4')=k1_lattices('#skF_3', '#skF_4', B_77) | ~m1_subset_1(B_77, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_152])).
% 3.30/1.55  tff(c_177, plain, (![B_25]: (k1_lattices('#skF_3', k16_lattice3('#skF_3', B_25), '#skF_4')=k1_lattices('#skF_3', '#skF_4', k16_lattice3('#skF_3', B_25)) | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_36, c_165])).
% 3.30/1.55  tff(c_191, plain, (![B_25]: (k1_lattices('#skF_3', k16_lattice3('#skF_3', B_25), '#skF_4')=k1_lattices('#skF_3', '#skF_4', k16_lattice3('#skF_3', B_25)) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_177])).
% 3.30/1.55  tff(c_192, plain, (![B_25]: (k1_lattices('#skF_3', k16_lattice3('#skF_3', B_25), '#skF_4')=k1_lattices('#skF_3', '#skF_4', k16_lattice3('#skF_3', B_25)))), inference(negUnitSimplification, [status(thm)], [c_58, c_191])).
% 3.30/1.55  tff(c_38, plain, (![A_26, C_32, B_30]: (r3_lattices(A_26, k16_lattice3(A_26, C_32), B_30) | ~r2_hidden(B_30, C_32) | ~m1_subset_1(B_30, u1_struct_0(A_26)) | ~l3_lattices(A_26) | ~v4_lattice3(A_26) | ~v10_lattices(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.30/1.55  tff(c_382, plain, (![A_111, C_112, B_113]: (r1_lattices(A_111, k16_lattice3(A_111, C_112), B_113) | ~m1_subset_1(k16_lattice3(A_111, C_112), u1_struct_0(A_111)) | ~v9_lattices(A_111) | ~v8_lattices(A_111) | ~v6_lattices(A_111) | ~r2_hidden(B_113, C_112) | ~m1_subset_1(B_113, u1_struct_0(A_111)) | ~l3_lattices(A_111) | ~v4_lattice3(A_111) | ~v10_lattices(A_111) | v2_struct_0(A_111))), inference(resolution, [status(thm)], [c_38, c_285])).
% 3.30/1.55  tff(c_386, plain, (![A_114, B_115, B_116]: (r1_lattices(A_114, k16_lattice3(A_114, B_115), B_116) | ~v9_lattices(A_114) | ~v8_lattices(A_114) | ~v6_lattices(A_114) | ~r2_hidden(B_116, B_115) | ~m1_subset_1(B_116, u1_struct_0(A_114)) | ~v4_lattice3(A_114) | ~v10_lattices(A_114) | ~l3_lattices(A_114) | v2_struct_0(A_114))), inference(resolution, [status(thm)], [c_36, c_382])).
% 3.30/1.55  tff(c_398, plain, (![A_123, B_124, B_125]: (k1_lattices(A_123, k16_lattice3(A_123, B_124), B_125)=B_125 | ~m1_subset_1(k16_lattice3(A_123, B_124), u1_struct_0(A_123)) | ~l2_lattices(A_123) | ~v9_lattices(A_123) | ~v8_lattices(A_123) | ~v6_lattices(A_123) | ~r2_hidden(B_125, B_124) | ~m1_subset_1(B_125, u1_struct_0(A_123)) | ~v4_lattice3(A_123) | ~v10_lattices(A_123) | ~l3_lattices(A_123) | v2_struct_0(A_123))), inference(resolution, [status(thm)], [c_386, c_18])).
% 3.30/1.55  tff(c_402, plain, (![A_126, B_127, B_128]: (k1_lattices(A_126, k16_lattice3(A_126, B_127), B_128)=B_128 | ~l2_lattices(A_126) | ~v9_lattices(A_126) | ~v8_lattices(A_126) | ~v6_lattices(A_126) | ~r2_hidden(B_128, B_127) | ~m1_subset_1(B_128, u1_struct_0(A_126)) | ~v4_lattice3(A_126) | ~v10_lattices(A_126) | ~l3_lattices(A_126) | v2_struct_0(A_126))), inference(resolution, [status(thm)], [c_36, c_398])).
% 3.30/1.55  tff(c_410, plain, (![B_127]: (k1_lattices('#skF_3', k16_lattice3('#skF_3', B_127), '#skF_4')='#skF_4' | ~l2_lattices('#skF_3') | ~v9_lattices('#skF_3') | ~v8_lattices('#skF_3') | ~v6_lattices('#skF_3') | ~r2_hidden('#skF_4', B_127) | ~v4_lattice3('#skF_3') | ~v10_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_402])).
% 3.30/1.55  tff(c_416, plain, (![B_127]: (k1_lattices('#skF_3', '#skF_4', k16_lattice3('#skF_3', B_127))='#skF_4' | ~r2_hidden('#skF_4', B_127) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_56, c_54, c_262, c_284, c_273, c_63, c_192, c_410])).
% 3.30/1.55  tff(c_417, plain, (![B_127]: (k1_lattices('#skF_3', '#skF_4', k16_lattice3('#skF_3', B_127))='#skF_4' | ~r2_hidden('#skF_4', B_127))), inference(negUnitSimplification, [status(thm)], [c_58, c_416])).
% 3.30/1.55  tff(c_483, plain, (![B_140]: (k16_lattice3('#skF_3', B_140)='#skF_4' | ~r2_hidden('#skF_4', B_140) | ~r3_lattice3('#skF_3', '#skF_4', B_140))), inference(superposition, [status(thm), theory('equality')], [c_468, c_417])).
% 3.30/1.55  tff(c_486, plain, (k16_lattice3('#skF_3', '#skF_5')='#skF_4' | ~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_483])).
% 3.30/1.55  tff(c_489, plain, (k16_lattice3('#skF_3', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_486])).
% 3.30/1.55  tff(c_491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_489])).
% 3.30/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.55  
% 3.30/1.55  Inference rules
% 3.30/1.55  ----------------------
% 3.30/1.55  #Ref     : 0
% 3.30/1.55  #Sup     : 83
% 3.30/1.55  #Fact    : 0
% 3.30/1.55  #Define  : 0
% 3.30/1.55  #Split   : 8
% 3.30/1.55  #Chain   : 0
% 3.30/1.55  #Close   : 0
% 3.30/1.55  
% 3.30/1.55  Ordering : KBO
% 3.30/1.55  
% 3.30/1.55  Simplification rules
% 3.30/1.55  ----------------------
% 3.30/1.55  #Subsume      : 8
% 3.30/1.55  #Demod        : 55
% 3.30/1.55  #Tautology    : 36
% 3.30/1.55  #SimpNegUnit  : 23
% 3.30/1.55  #BackRed      : 1
% 3.30/1.55  
% 3.30/1.55  #Partial instantiations: 0
% 3.30/1.55  #Strategies tried      : 1
% 3.30/1.55  
% 3.30/1.55  Timing (in seconds)
% 3.30/1.55  ----------------------
% 3.30/1.55  Preprocessing        : 0.39
% 3.30/1.55  Parsing              : 0.19
% 3.30/1.55  CNF conversion       : 0.03
% 3.30/1.55  Main loop            : 0.34
% 3.30/1.55  Inferencing          : 0.14
% 3.30/1.55  Reduction            : 0.09
% 3.30/1.55  Demodulation         : 0.06
% 3.30/1.55  BG Simplification    : 0.03
% 3.30/1.55  Subsumption          : 0.06
% 3.30/1.55  Abstraction          : 0.02
% 3.30/1.55  MUC search           : 0.00
% 3.30/1.55  Cooper               : 0.00
% 3.30/1.55  Total                : 0.77
% 3.30/1.55  Index Insertion      : 0.00
% 3.30/1.56  Index Deletion       : 0.00
% 3.30/1.56  Index Matching       : 0.00
% 3.30/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
