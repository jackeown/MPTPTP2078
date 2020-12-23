%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:45 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 353 expanded)
%              Number of leaves         :   39 ( 139 expanded)
%              Depth                    :   13
%              Number of atoms          :  368 (1563 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff(a_2_2_lattice3,type,(
    a_2_2_lattice3: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_193,negated_conjecture,(
    ~ ! [A] :
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

tff(f_137,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k16_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

tff(f_161,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( B = k16_lattice3(A,C)
            <=> ( r3_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r3_lattice3(A,D,C)
                     => r3_lattices(A,D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r3_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

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

tff(f_66,axiom,(
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

tff(f_173,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] : k15_lattice3(A,B) = k16_lattice3(A,a_2_2_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

tff(f_130,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B,C] :
            ( m1_subset_1(C,u1_struct_0(A))
           => ( C = k15_lattice3(A,B)
            <=> ( r4_lattice3(A,C,B)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r4_lattice3(A,D,B)
                     => r1_lattices(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( r4_lattice3(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_hidden(D,C)
                   => r1_lattices(A,D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_66,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_70,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_68,plain,(
    v4_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_46,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k16_lattice3(A_61,B_62),u1_struct_0(A_61))
      | ~ l3_lattices(A_61)
      | v2_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_637,plain,(
    ! [A_257,C_258] :
      ( r3_lattice3(A_257,k16_lattice3(A_257,C_258),C_258)
      | ~ m1_subset_1(k16_lattice3(A_257,C_258),u1_struct_0(A_257))
      | ~ l3_lattices(A_257)
      | ~ v4_lattice3(A_257)
      | ~ v10_lattices(A_257)
      | v2_struct_0(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_642,plain,(
    ! [A_61,B_62] :
      ( r3_lattice3(A_61,k16_lattice3(A_61,B_62),B_62)
      | ~ v4_lattice3(A_61)
      | ~ v10_lattices(A_61)
      | ~ l3_lattices(A_61)
      | v2_struct_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_46,c_637])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_62,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_647,plain,(
    ! [A_261,B_262,D_263,C_264] :
      ( r1_lattices(A_261,B_262,D_263)
      | ~ r2_hidden(D_263,C_264)
      | ~ m1_subset_1(D_263,u1_struct_0(A_261))
      | ~ r3_lattice3(A_261,B_262,C_264)
      | ~ m1_subset_1(B_262,u1_struct_0(A_261))
      | ~ l3_lattices(A_261)
      | v2_struct_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_657,plain,(
    ! [A_265,B_266] :
      ( r1_lattices(A_265,B_266,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_265))
      | ~ r3_lattice3(A_265,B_266,'#skF_7')
      | ~ m1_subset_1(B_266,u1_struct_0(A_265))
      | ~ l3_lattices(A_265)
      | v2_struct_0(A_265) ) ),
    inference(resolution,[status(thm)],[c_62,c_647])).

tff(c_659,plain,(
    ! [B_266] :
      ( r1_lattices('#skF_5',B_266,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_266,'#skF_7')
      | ~ m1_subset_1(B_266,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_657])).

tff(c_662,plain,(
    ! [B_266] :
      ( r1_lattices('#skF_5',B_266,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_266,'#skF_7')
      | ~ m1_subset_1(B_266,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_659])).

tff(c_664,plain,(
    ! [B_267] :
      ( r1_lattices('#skF_5',B_267,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_267,'#skF_7')
      | ~ m1_subset_1(B_267,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_662])).

tff(c_680,plain,(
    ! [B_62] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5',B_62),'#skF_6')
      | ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5',B_62),'#skF_7')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_664])).

tff(c_698,plain,(
    ! [B_62] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5',B_62),'#skF_6')
      | ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5',B_62),'#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_680])).

tff(c_713,plain,(
    ! [B_273] :
      ( r1_lattices('#skF_5',k16_lattice3('#skF_5',B_273),'#skF_6')
      | ~ r3_lattice3('#skF_5',k16_lattice3('#skF_5',B_273),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_698])).

tff(c_717,plain,
    ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_642,c_713])).

tff(c_724,plain,
    ( r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_717])).

tff(c_725,plain,(
    r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_724])).

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

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_791,plain,(
    ! [A_279,B_280,C_281] :
      ( r3_lattices(A_279,B_280,C_281)
      | ~ r1_lattices(A_279,B_280,C_281)
      | ~ m1_subset_1(C_281,u1_struct_0(A_279))
      | ~ m1_subset_1(B_280,u1_struct_0(A_279))
      | ~ l3_lattices(A_279)
      | ~ v9_lattices(A_279)
      | ~ v8_lattices(A_279)
      | ~ v6_lattices(A_279)
      | v2_struct_0(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_801,plain,(
    ! [B_280] :
      ( r3_lattices('#skF_5',B_280,'#skF_6')
      | ~ r1_lattices('#skF_5',B_280,'#skF_6')
      | ~ m1_subset_1(B_280,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_791])).

tff(c_808,plain,(
    ! [B_280] :
      ( r3_lattices('#skF_5',B_280,'#skF_6')
      | ~ r1_lattices('#skF_5',B_280,'#skF_6')
      | ~ m1_subset_1(B_280,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_801])).

tff(c_809,plain,(
    ! [B_280] :
      ( r3_lattices('#skF_5',B_280,'#skF_6')
      | ~ r1_lattices('#skF_5',B_280,'#skF_6')
      | ~ m1_subset_1(B_280,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_808])).

tff(c_826,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_809])).

tff(c_830,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_826])).

tff(c_833,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_830])).

tff(c_835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_833])).

tff(c_836,plain,(
    ! [B_280] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_280,'#skF_6')
      | ~ r1_lattices('#skF_5',B_280,'#skF_6')
      | ~ m1_subset_1(B_280,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_809])).

tff(c_838,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_836])).

tff(c_841,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_838])).

tff(c_844,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_841])).

tff(c_846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_844])).

tff(c_847,plain,(
    ! [B_280] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_280,'#skF_6')
      | ~ r1_lattices('#skF_5',B_280,'#skF_6')
      | ~ m1_subset_1(B_280,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_836])).

tff(c_856,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_847])).

tff(c_859,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_856])).

tff(c_862,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_859])).

tff(c_864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_862])).

tff(c_868,plain,(
    ! [B_291] :
      ( r3_lattices('#skF_5',B_291,'#skF_6')
      | ~ r1_lattices('#skF_5',B_291,'#skF_6')
      | ~ m1_subset_1(B_291,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_847])).

tff(c_884,plain,(
    ! [B_62] :
      ( r3_lattices('#skF_5',k16_lattice3('#skF_5',B_62),'#skF_6')
      | ~ r1_lattices('#skF_5',k16_lattice3('#skF_5',B_62),'#skF_6')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_868])).

tff(c_902,plain,(
    ! [B_62] :
      ( r3_lattices('#skF_5',k16_lattice3('#skF_5',B_62),'#skF_6')
      | ~ r1_lattices('#skF_5',k16_lattice3('#skF_5',B_62),'#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_884])).

tff(c_913,plain,(
    ! [B_293] :
      ( r3_lattices('#skF_5',k16_lattice3('#skF_5',B_293),'#skF_6')
      | ~ r1_lattices('#skF_5',k16_lattice3('#skF_5',B_293),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_902])).

tff(c_275,plain,(
    ! [A_150,B_151,C_152] :
      ( r3_lattices(A_150,B_151,C_152)
      | ~ r1_lattices(A_150,B_151,C_152)
      | ~ m1_subset_1(C_152,u1_struct_0(A_150))
      | ~ m1_subset_1(B_151,u1_struct_0(A_150))
      | ~ l3_lattices(A_150)
      | ~ v9_lattices(A_150)
      | ~ v8_lattices(A_150)
      | ~ v6_lattices(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_285,plain,(
    ! [B_151] :
      ( r3_lattices('#skF_5',B_151,'#skF_6')
      | ~ r1_lattices('#skF_5',B_151,'#skF_6')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_275])).

tff(c_292,plain,(
    ! [B_151] :
      ( r3_lattices('#skF_5',B_151,'#skF_6')
      | ~ r1_lattices('#skF_5',B_151,'#skF_6')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_285])).

tff(c_293,plain,(
    ! [B_151] :
      ( r3_lattices('#skF_5',B_151,'#skF_6')
      | ~ r1_lattices('#skF_5',B_151,'#skF_6')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_292])).

tff(c_294,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_297,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_294])).

tff(c_300,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_297])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_300])).

tff(c_304,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_303,plain,(
    ! [B_151] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_151,'#skF_6')
      | ~ r1_lattices('#skF_5',B_151,'#skF_6')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_306,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_309,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_306])).

tff(c_312,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_309])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_312])).

tff(c_315,plain,(
    ! [B_151] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_151,'#skF_6')
      | ~ r1_lattices('#skF_5',B_151,'#skF_6')
      | ~ m1_subset_1(B_151,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_317,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_320,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_317])).

tff(c_323,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_320])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_323])).

tff(c_327,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_316,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_81,plain,(
    ! [A_100,B_101] :
      ( k16_lattice3(A_100,a_2_2_lattice3(A_100,B_101)) = k15_lattice3(A_100,B_101)
      | ~ l3_lattices(A_100)
      | ~ v4_lattice3(A_100)
      | ~ v10_lattices(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_87,plain,(
    ! [A_100,B_101] :
      ( m1_subset_1(k15_lattice3(A_100,B_101),u1_struct_0(A_100))
      | ~ l3_lattices(A_100)
      | v2_struct_0(A_100)
      | ~ l3_lattices(A_100)
      | ~ v4_lattice3(A_100)
      | ~ v10_lattices(A_100)
      | v2_struct_0(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_46])).

tff(c_100,plain,(
    ! [A_122,B_123] :
      ( r4_lattice3(A_122,k15_lattice3(A_122,B_123),B_123)
      | ~ m1_subset_1(k15_lattice3(A_122,B_123),u1_struct_0(A_122))
      | ~ v4_lattice3(A_122)
      | ~ v10_lattices(A_122)
      | ~ l3_lattices(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_103,plain,(
    ! [A_100,B_101] :
      ( r4_lattice3(A_100,k15_lattice3(A_100,B_101),B_101)
      | ~ l3_lattices(A_100)
      | ~ v4_lattice3(A_100)
      | ~ v10_lattices(A_100)
      | v2_struct_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_87,c_100])).

tff(c_187,plain,(
    ! [A_139,D_140,B_141,C_142] :
      ( r1_lattices(A_139,D_140,B_141)
      | ~ r2_hidden(D_140,C_142)
      | ~ m1_subset_1(D_140,u1_struct_0(A_139))
      | ~ r4_lattice3(A_139,B_141,C_142)
      | ~ m1_subset_1(B_141,u1_struct_0(A_139))
      | ~ l3_lattices(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_205,plain,(
    ! [A_144,B_145] :
      ( r1_lattices(A_144,'#skF_6',B_145)
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_144))
      | ~ r4_lattice3(A_144,B_145,'#skF_7')
      | ~ m1_subset_1(B_145,u1_struct_0(A_144))
      | ~ l3_lattices(A_144)
      | v2_struct_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_62,c_187])).

tff(c_207,plain,(
    ! [B_145] :
      ( r1_lattices('#skF_5','#skF_6',B_145)
      | ~ r4_lattice3('#skF_5',B_145,'#skF_7')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_205])).

tff(c_210,plain,(
    ! [B_145] :
      ( r1_lattices('#skF_5','#skF_6',B_145)
      | ~ r4_lattice3('#skF_5',B_145,'#skF_7')
      | ~ m1_subset_1(B_145,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_207])).

tff(c_212,plain,(
    ! [B_146] :
      ( r1_lattices('#skF_5','#skF_6',B_146)
      | ~ r4_lattice3('#skF_5',B_146,'#skF_7')
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_210])).

tff(c_224,plain,(
    ! [B_101] :
      ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5',B_101))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',B_101),'#skF_7')
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_87,c_212])).

tff(c_242,plain,(
    ! [B_101] :
      ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5',B_101))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',B_101),'#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_224])).

tff(c_258,plain,(
    ! [B_148] :
      ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5',B_148))
      | ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5',B_148),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_242])).

tff(c_262,plain,
    ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_103,c_258])).

tff(c_265,plain,
    ( r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_262])).

tff(c_266,plain,(
    r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_265])).

tff(c_590,plain,(
    ! [A_223,B_224,B_225] :
      ( r3_lattices(A_223,B_224,k15_lattice3(A_223,B_225))
      | ~ r1_lattices(A_223,B_224,k15_lattice3(A_223,B_225))
      | ~ m1_subset_1(B_224,u1_struct_0(A_223))
      | ~ v9_lattices(A_223)
      | ~ v8_lattices(A_223)
      | ~ v6_lattices(A_223)
      | ~ l3_lattices(A_223)
      | ~ v4_lattice3(A_223)
      | ~ v10_lattices(A_223)
      | v2_struct_0(A_223) ) ),
    inference(resolution,[status(thm)],[c_87,c_275])).

tff(c_60,plain,
    ( ~ r3_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ r3_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_76,plain,(
    ~ r3_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_599,plain,
    ( ~ r1_lattices('#skF_5','#skF_6',k15_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_590,c_76])).

tff(c_604,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_304,c_327,c_316,c_64,c_266,c_599])).

tff(c_606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_604])).

tff(c_607,plain,(
    ~ r3_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_918,plain,(
    ~ r1_lattices('#skF_5',k16_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_913,c_607])).

tff(c_930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_918])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n002.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 12:30:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.56  
% 3.70/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.57  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 3.70/1.57  
% 3.70/1.57  %Foreground sorts:
% 3.70/1.57  
% 3.70/1.57  
% 3.70/1.57  %Background operators:
% 3.70/1.57  
% 3.70/1.57  
% 3.70/1.57  %Foreground operators:
% 3.70/1.57  tff(l3_lattices, type, l3_lattices: $i > $o).
% 3.70/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.70/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.70/1.57  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 3.70/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.57  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 3.70/1.57  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 3.70/1.57  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.70/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.70/1.57  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 3.70/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.70/1.57  tff(v4_lattices, type, v4_lattices: $i > $o).
% 3.70/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.70/1.57  tff(v6_lattices, type, v6_lattices: $i > $o).
% 3.70/1.57  tff(v9_lattices, type, v9_lattices: $i > $o).
% 3.70/1.57  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 3.70/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.70/1.57  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 3.70/1.57  tff(v5_lattices, type, v5_lattices: $i > $o).
% 3.70/1.57  tff(v10_lattices, type, v10_lattices: $i > $o).
% 3.70/1.57  tff(a_2_2_lattice3, type, a_2_2_lattice3: ($i * $i) > $i).
% 3.70/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.70/1.57  tff(v8_lattices, type, v8_lattices: $i > $o).
% 3.70/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.70/1.57  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 3.70/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.57  tff(v7_lattices, type, v7_lattices: $i > $o).
% 3.70/1.57  
% 3.70/1.59  tff(f_193, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_lattice3)).
% 3.70/1.59  tff(f_137, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k16_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k16_lattice3)).
% 3.70/1.59  tff(f_161, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 3.70/1.59  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_lattice3)).
% 3.70/1.59  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 3.70/1.59  tff(f_66, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 3.70/1.59  tff(f_173, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (k15_lattice3(A, B) = k16_lattice3(A, a_2_2_lattice3(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_lattice3)).
% 3.70/1.59  tff(f_130, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 3.70/1.59  tff(f_102, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_lattice3)).
% 3.70/1.59  tff(c_72, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.70/1.59  tff(c_66, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.70/1.59  tff(c_70, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.70/1.59  tff(c_68, plain, (v4_lattice3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.70/1.59  tff(c_46, plain, (![A_61, B_62]: (m1_subset_1(k16_lattice3(A_61, B_62), u1_struct_0(A_61)) | ~l3_lattices(A_61) | v2_struct_0(A_61))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.70/1.59  tff(c_637, plain, (![A_257, C_258]: (r3_lattice3(A_257, k16_lattice3(A_257, C_258), C_258) | ~m1_subset_1(k16_lattice3(A_257, C_258), u1_struct_0(A_257)) | ~l3_lattices(A_257) | ~v4_lattice3(A_257) | ~v10_lattices(A_257) | v2_struct_0(A_257))), inference(cnfTransformation, [status(thm)], [f_161])).
% 3.70/1.59  tff(c_642, plain, (![A_61, B_62]: (r3_lattice3(A_61, k16_lattice3(A_61, B_62), B_62) | ~v4_lattice3(A_61) | ~v10_lattices(A_61) | ~l3_lattices(A_61) | v2_struct_0(A_61))), inference(resolution, [status(thm)], [c_46, c_637])).
% 3.70/1.59  tff(c_64, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.70/1.59  tff(c_62, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.70/1.59  tff(c_647, plain, (![A_261, B_262, D_263, C_264]: (r1_lattices(A_261, B_262, D_263) | ~r2_hidden(D_263, C_264) | ~m1_subset_1(D_263, u1_struct_0(A_261)) | ~r3_lattice3(A_261, B_262, C_264) | ~m1_subset_1(B_262, u1_struct_0(A_261)) | ~l3_lattices(A_261) | v2_struct_0(A_261))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.70/1.59  tff(c_657, plain, (![A_265, B_266]: (r1_lattices(A_265, B_266, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0(A_265)) | ~r3_lattice3(A_265, B_266, '#skF_7') | ~m1_subset_1(B_266, u1_struct_0(A_265)) | ~l3_lattices(A_265) | v2_struct_0(A_265))), inference(resolution, [status(thm)], [c_62, c_647])).
% 3.70/1.59  tff(c_659, plain, (![B_266]: (r1_lattices('#skF_5', B_266, '#skF_6') | ~r3_lattice3('#skF_5', B_266, '#skF_7') | ~m1_subset_1(B_266, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_657])).
% 3.70/1.59  tff(c_662, plain, (![B_266]: (r1_lattices('#skF_5', B_266, '#skF_6') | ~r3_lattice3('#skF_5', B_266, '#skF_7') | ~m1_subset_1(B_266, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_659])).
% 3.70/1.59  tff(c_664, plain, (![B_267]: (r1_lattices('#skF_5', B_267, '#skF_6') | ~r3_lattice3('#skF_5', B_267, '#skF_7') | ~m1_subset_1(B_267, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_662])).
% 3.70/1.59  tff(c_680, plain, (![B_62]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', B_62), '#skF_6') | ~r3_lattice3('#skF_5', k16_lattice3('#skF_5', B_62), '#skF_7') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_664])).
% 3.70/1.59  tff(c_698, plain, (![B_62]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', B_62), '#skF_6') | ~r3_lattice3('#skF_5', k16_lattice3('#skF_5', B_62), '#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_680])).
% 3.70/1.59  tff(c_713, plain, (![B_273]: (r1_lattices('#skF_5', k16_lattice3('#skF_5', B_273), '#skF_6') | ~r3_lattice3('#skF_5', k16_lattice3('#skF_5', B_273), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_698])).
% 3.70/1.59  tff(c_717, plain, (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_642, c_713])).
% 3.70/1.59  tff(c_724, plain, (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_717])).
% 3.70/1.59  tff(c_725, plain, (r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_72, c_724])).
% 3.70/1.59  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.70/1.59  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.70/1.59  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.70/1.59  tff(c_791, plain, (![A_279, B_280, C_281]: (r3_lattices(A_279, B_280, C_281) | ~r1_lattices(A_279, B_280, C_281) | ~m1_subset_1(C_281, u1_struct_0(A_279)) | ~m1_subset_1(B_280, u1_struct_0(A_279)) | ~l3_lattices(A_279) | ~v9_lattices(A_279) | ~v8_lattices(A_279) | ~v6_lattices(A_279) | v2_struct_0(A_279))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.70/1.59  tff(c_801, plain, (![B_280]: (r3_lattices('#skF_5', B_280, '#skF_6') | ~r1_lattices('#skF_5', B_280, '#skF_6') | ~m1_subset_1(B_280, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_791])).
% 3.70/1.59  tff(c_808, plain, (![B_280]: (r3_lattices('#skF_5', B_280, '#skF_6') | ~r1_lattices('#skF_5', B_280, '#skF_6') | ~m1_subset_1(B_280, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_801])).
% 3.70/1.59  tff(c_809, plain, (![B_280]: (r3_lattices('#skF_5', B_280, '#skF_6') | ~r1_lattices('#skF_5', B_280, '#skF_6') | ~m1_subset_1(B_280, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_808])).
% 3.70/1.59  tff(c_826, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_809])).
% 3.70/1.59  tff(c_830, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_826])).
% 3.70/1.59  tff(c_833, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_830])).
% 3.70/1.59  tff(c_835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_833])).
% 3.70/1.59  tff(c_836, plain, (![B_280]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_280, '#skF_6') | ~r1_lattices('#skF_5', B_280, '#skF_6') | ~m1_subset_1(B_280, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_809])).
% 3.70/1.59  tff(c_838, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_836])).
% 3.70/1.59  tff(c_841, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_838])).
% 3.70/1.59  tff(c_844, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_841])).
% 3.70/1.59  tff(c_846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_844])).
% 3.70/1.59  tff(c_847, plain, (![B_280]: (~v8_lattices('#skF_5') | r3_lattices('#skF_5', B_280, '#skF_6') | ~r1_lattices('#skF_5', B_280, '#skF_6') | ~m1_subset_1(B_280, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_836])).
% 3.70/1.59  tff(c_856, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_847])).
% 3.70/1.59  tff(c_859, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_856])).
% 3.70/1.59  tff(c_862, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_859])).
% 3.70/1.59  tff(c_864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_862])).
% 3.70/1.59  tff(c_868, plain, (![B_291]: (r3_lattices('#skF_5', B_291, '#skF_6') | ~r1_lattices('#skF_5', B_291, '#skF_6') | ~m1_subset_1(B_291, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_847])).
% 3.70/1.59  tff(c_884, plain, (![B_62]: (r3_lattices('#skF_5', k16_lattice3('#skF_5', B_62), '#skF_6') | ~r1_lattices('#skF_5', k16_lattice3('#skF_5', B_62), '#skF_6') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_46, c_868])).
% 3.70/1.59  tff(c_902, plain, (![B_62]: (r3_lattices('#skF_5', k16_lattice3('#skF_5', B_62), '#skF_6') | ~r1_lattices('#skF_5', k16_lattice3('#skF_5', B_62), '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_884])).
% 3.70/1.59  tff(c_913, plain, (![B_293]: (r3_lattices('#skF_5', k16_lattice3('#skF_5', B_293), '#skF_6') | ~r1_lattices('#skF_5', k16_lattice3('#skF_5', B_293), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_902])).
% 3.70/1.59  tff(c_275, plain, (![A_150, B_151, C_152]: (r3_lattices(A_150, B_151, C_152) | ~r1_lattices(A_150, B_151, C_152) | ~m1_subset_1(C_152, u1_struct_0(A_150)) | ~m1_subset_1(B_151, u1_struct_0(A_150)) | ~l3_lattices(A_150) | ~v9_lattices(A_150) | ~v8_lattices(A_150) | ~v6_lattices(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.70/1.59  tff(c_285, plain, (![B_151]: (r3_lattices('#skF_5', B_151, '#skF_6') | ~r1_lattices('#skF_5', B_151, '#skF_6') | ~m1_subset_1(B_151, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_275])).
% 3.70/1.59  tff(c_292, plain, (![B_151]: (r3_lattices('#skF_5', B_151, '#skF_6') | ~r1_lattices('#skF_5', B_151, '#skF_6') | ~m1_subset_1(B_151, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_285])).
% 3.70/1.59  tff(c_293, plain, (![B_151]: (r3_lattices('#skF_5', B_151, '#skF_6') | ~r1_lattices('#skF_5', B_151, '#skF_6') | ~m1_subset_1(B_151, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72, c_292])).
% 3.70/1.59  tff(c_294, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_293])).
% 3.70/1.59  tff(c_297, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_294])).
% 3.70/1.59  tff(c_300, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_297])).
% 3.70/1.59  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_300])).
% 3.70/1.59  tff(c_304, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_293])).
% 3.70/1.59  tff(c_303, plain, (![B_151]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_151, '#skF_6') | ~r1_lattices('#skF_5', B_151, '#skF_6') | ~m1_subset_1(B_151, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_293])).
% 3.70/1.59  tff(c_306, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_303])).
% 3.70/1.59  tff(c_309, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_306])).
% 3.70/1.59  tff(c_312, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_309])).
% 3.70/1.59  tff(c_314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_312])).
% 3.70/1.59  tff(c_315, plain, (![B_151]: (~v8_lattices('#skF_5') | r3_lattices('#skF_5', B_151, '#skF_6') | ~r1_lattices('#skF_5', B_151, '#skF_6') | ~m1_subset_1(B_151, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_303])).
% 3.70/1.59  tff(c_317, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_315])).
% 3.70/1.59  tff(c_320, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_317])).
% 3.70/1.59  tff(c_323, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_320])).
% 3.70/1.59  tff(c_325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_323])).
% 3.70/1.59  tff(c_327, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_315])).
% 3.70/1.59  tff(c_316, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_303])).
% 3.70/1.59  tff(c_81, plain, (![A_100, B_101]: (k16_lattice3(A_100, a_2_2_lattice3(A_100, B_101))=k15_lattice3(A_100, B_101) | ~l3_lattices(A_100) | ~v4_lattice3(A_100) | ~v10_lattices(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_173])).
% 3.70/1.59  tff(c_87, plain, (![A_100, B_101]: (m1_subset_1(k15_lattice3(A_100, B_101), u1_struct_0(A_100)) | ~l3_lattices(A_100) | v2_struct_0(A_100) | ~l3_lattices(A_100) | ~v4_lattice3(A_100) | ~v10_lattices(A_100) | v2_struct_0(A_100))), inference(superposition, [status(thm), theory('equality')], [c_81, c_46])).
% 3.70/1.59  tff(c_100, plain, (![A_122, B_123]: (r4_lattice3(A_122, k15_lattice3(A_122, B_123), B_123) | ~m1_subset_1(k15_lattice3(A_122, B_123), u1_struct_0(A_122)) | ~v4_lattice3(A_122) | ~v10_lattices(A_122) | ~l3_lattices(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.70/1.59  tff(c_103, plain, (![A_100, B_101]: (r4_lattice3(A_100, k15_lattice3(A_100, B_101), B_101) | ~l3_lattices(A_100) | ~v4_lattice3(A_100) | ~v10_lattices(A_100) | v2_struct_0(A_100))), inference(resolution, [status(thm)], [c_87, c_100])).
% 3.70/1.59  tff(c_187, plain, (![A_139, D_140, B_141, C_142]: (r1_lattices(A_139, D_140, B_141) | ~r2_hidden(D_140, C_142) | ~m1_subset_1(D_140, u1_struct_0(A_139)) | ~r4_lattice3(A_139, B_141, C_142) | ~m1_subset_1(B_141, u1_struct_0(A_139)) | ~l3_lattices(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.70/1.59  tff(c_205, plain, (![A_144, B_145]: (r1_lattices(A_144, '#skF_6', B_145) | ~m1_subset_1('#skF_6', u1_struct_0(A_144)) | ~r4_lattice3(A_144, B_145, '#skF_7') | ~m1_subset_1(B_145, u1_struct_0(A_144)) | ~l3_lattices(A_144) | v2_struct_0(A_144))), inference(resolution, [status(thm)], [c_62, c_187])).
% 3.70/1.59  tff(c_207, plain, (![B_145]: (r1_lattices('#skF_5', '#skF_6', B_145) | ~r4_lattice3('#skF_5', B_145, '#skF_7') | ~m1_subset_1(B_145, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_205])).
% 3.70/1.59  tff(c_210, plain, (![B_145]: (r1_lattices('#skF_5', '#skF_6', B_145) | ~r4_lattice3('#skF_5', B_145, '#skF_7') | ~m1_subset_1(B_145, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_207])).
% 3.70/1.59  tff(c_212, plain, (![B_146]: (r1_lattices('#skF_5', '#skF_6', B_146) | ~r4_lattice3('#skF_5', B_146, '#skF_7') | ~m1_subset_1(B_146, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_72, c_210])).
% 3.70/1.59  tff(c_224, plain, (![B_101]: (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', B_101)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', B_101), '#skF_7') | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_87, c_212])).
% 3.70/1.59  tff(c_242, plain, (![B_101]: (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', B_101)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', B_101), '#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_224])).
% 3.70/1.59  tff(c_258, plain, (![B_148]: (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', B_148)) | ~r4_lattice3('#skF_5', k15_lattice3('#skF_5', B_148), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_242])).
% 3.70/1.59  tff(c_262, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_103, c_258])).
% 3.70/1.59  tff(c_265, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_262])).
% 3.70/1.59  tff(c_266, plain, (r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_265])).
% 3.70/1.59  tff(c_590, plain, (![A_223, B_224, B_225]: (r3_lattices(A_223, B_224, k15_lattice3(A_223, B_225)) | ~r1_lattices(A_223, B_224, k15_lattice3(A_223, B_225)) | ~m1_subset_1(B_224, u1_struct_0(A_223)) | ~v9_lattices(A_223) | ~v8_lattices(A_223) | ~v6_lattices(A_223) | ~l3_lattices(A_223) | ~v4_lattice3(A_223) | ~v10_lattices(A_223) | v2_struct_0(A_223))), inference(resolution, [status(thm)], [c_87, c_275])).
% 3.70/1.59  tff(c_60, plain, (~r3_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~r3_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_193])).
% 3.70/1.59  tff(c_76, plain, (~r3_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_60])).
% 3.70/1.59  tff(c_599, plain, (~r1_lattices('#skF_5', '#skF_6', k15_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_590, c_76])).
% 3.70/1.59  tff(c_604, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_304, c_327, c_316, c_64, c_266, c_599])).
% 3.70/1.59  tff(c_606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_604])).
% 3.70/1.59  tff(c_607, plain, (~r3_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_60])).
% 3.70/1.59  tff(c_918, plain, (~r1_lattices('#skF_5', k16_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_913, c_607])).
% 3.70/1.59  tff(c_930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_725, c_918])).
% 3.70/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.59  
% 3.70/1.59  Inference rules
% 3.70/1.59  ----------------------
% 3.70/1.59  #Ref     : 0
% 3.70/1.59  #Sup     : 130
% 3.70/1.59  #Fact    : 0
% 3.70/1.59  #Define  : 0
% 3.70/1.59  #Split   : 13
% 3.70/1.59  #Chain   : 0
% 3.70/1.59  #Close   : 0
% 3.70/1.59  
% 3.70/1.59  Ordering : KBO
% 3.70/1.59  
% 3.70/1.59  Simplification rules
% 3.70/1.59  ----------------------
% 3.70/1.59  #Subsume      : 14
% 3.70/1.59  #Demod        : 188
% 3.70/1.59  #Tautology    : 16
% 3.70/1.59  #SimpNegUnit  : 71
% 3.70/1.59  #BackRed      : 0
% 3.70/1.59  
% 3.70/1.59  #Partial instantiations: 0
% 3.70/1.59  #Strategies tried      : 1
% 3.70/1.59  
% 3.70/1.59  Timing (in seconds)
% 3.70/1.59  ----------------------
% 3.70/1.60  Preprocessing        : 0.35
% 3.70/1.60  Parsing              : 0.18
% 3.70/1.60  CNF conversion       : 0.03
% 3.70/1.60  Main loop            : 0.47
% 3.70/1.60  Inferencing          : 0.20
% 3.70/1.60  Reduction            : 0.13
% 3.70/1.60  Demodulation         : 0.08
% 3.70/1.60  BG Simplification    : 0.03
% 3.70/1.60  Subsumption          : 0.08
% 3.70/1.60  Abstraction          : 0.02
% 3.70/1.60  MUC search           : 0.00
% 3.70/1.60  Cooper               : 0.00
% 3.70/1.60  Total                : 0.87
% 3.70/1.60  Index Insertion      : 0.00
% 3.70/1.60  Index Deletion       : 0.00
% 3.70/1.60  Index Matching       : 0.00
% 3.70/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
