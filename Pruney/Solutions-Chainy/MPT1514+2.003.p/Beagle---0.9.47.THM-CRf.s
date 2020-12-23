%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:51 EST 2020

% Result     : Theorem 8.39s
% Output     : CNFRefutation 8.66s
% Verified   : 
% Statistics : Number of formulae       :  151 (1156 expanded)
%              Number of leaves         :   42 ( 434 expanded)
%              Depth                    :   26
%              Number of atoms          :  461 (6073 expanded)
%              Number of equality atoms :   19 ( 118 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_8 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

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

tff(a_2_5_lattice3,type,(
    a_2_5_lattice3: ( $i * $i ) > $i )).

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

tff(a_2_6_lattice3,type,(
    a_2_6_lattice3: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_204,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v4_lattice3(A)
          & l3_lattices(A) )
       => ! [B,C] :
            ( ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ~ ( r2_hidden(D,B)
                    & ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ~ ( r3_lattices(A,D,E)
                            & r2_hidden(E,C) ) ) ) )
           => r3_lattices(A,k15_lattice3(A,B),k15_lattice3(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => m1_subset_1(k15_lattice3(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

tff(f_144,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] : k15_lattice3(A,B) = k16_lattice3(A,a_2_2_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

tff(f_163,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & v4_lattice3(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_2_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r4_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

tff(f_84,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v10_lattices(B)
        & v4_lattice3(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_5_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ? [E] :
                ( m1_subset_1(E,u1_struct_0(B))
                & r3_lattices(B,D,E)
                & r2_hidden(E,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(f_177,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( k15_lattice3(A,B) = k15_lattice3(A,a_2_5_lattice3(A,B))
          & k16_lattice3(A,B) = k16_lattice3(A,a_2_6_lattice3(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_66,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_64,plain,(
    v4_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_62,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_28,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k15_lattice3(A_27,B_28),u1_struct_0(A_27))
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_50,plain,(
    ! [A_48,B_50] :
      ( k16_lattice3(A_48,a_2_2_lattice3(A_48,B_50)) = k15_lattice3(A_48,B_50)
      | ~ l3_lattices(A_48)
      | ~ v4_lattice3(A_48)
      | ~ v10_lattices(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_167,plain,(
    ! [A_124,C_125,B_126] :
      ( r3_lattices(A_124,k16_lattice3(A_124,C_125),B_126)
      | ~ r2_hidden(B_126,C_125)
      | ~ m1_subset_1(B_126,u1_struct_0(A_124))
      | ~ l3_lattices(A_124)
      | ~ v4_lattice3(A_124)
      | ~ v10_lattices(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_332,plain,(
    ! [A_163,B_164,B_165] :
      ( r3_lattices(A_163,k15_lattice3(A_163,B_164),B_165)
      | ~ r2_hidden(B_165,a_2_2_lattice3(A_163,B_164))
      | ~ m1_subset_1(B_165,u1_struct_0(A_163))
      | ~ l3_lattices(A_163)
      | ~ v4_lattice3(A_163)
      | ~ v10_lattices(A_163)
      | v2_struct_0(A_163)
      | ~ l3_lattices(A_163)
      | ~ v4_lattice3(A_163)
      | ~ v10_lattices(A_163)
      | v2_struct_0(A_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_167])).

tff(c_60,plain,(
    ~ r3_lattices('#skF_5',k15_lattice3('#skF_5','#skF_6'),k15_lattice3('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_337,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_5','#skF_7'),a_2_2_lattice3('#skF_5','#skF_6'))
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_332,c_60])).

tff(c_344,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_5','#skF_7'),a_2_2_lattice3('#skF_5','#skF_6'))
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_337])).

tff(c_345,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_5','#skF_7'),a_2_2_lattice3('#skF_5','#skF_6'))
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_344])).

tff(c_346,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_345])).

tff(c_349,plain,
    ( ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_346])).

tff(c_352,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_349])).

tff(c_354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_352])).

tff(c_356,plain,(
    m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_30,plain,(
    ! [D_34,B_30,C_31] :
      ( r2_hidden(D_34,a_2_2_lattice3(B_30,C_31))
      | ~ r4_lattice3(B_30,D_34,C_31)
      | ~ m1_subset_1(D_34,u1_struct_0(B_30))
      | ~ l3_lattices(B_30)
      | ~ v4_lattice3(B_30)
      | ~ v10_lattices(B_30)
      | v2_struct_0(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_355,plain,(
    ~ r2_hidden(k15_lattice3('#skF_5','#skF_7'),a_2_2_lattice3('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_345])).

tff(c_365,plain,
    ( ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_355])).

tff(c_368,plain,
    ( ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_356,c_365])).

tff(c_369,plain,(
    ~ r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_368])).

tff(c_24,plain,(
    ! [A_5,B_17,C_23] :
      ( r2_hidden('#skF_1'(A_5,B_17,C_23),C_23)
      | r4_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    ! [A_5,B_17,C_23] :
      ( m1_subset_1('#skF_1'(A_5,B_17,C_23),u1_struct_0(A_5))
      | r4_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_74,plain,(
    ! [D_72] :
      ( m1_subset_1('#skF_8'(D_72),u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_72,'#skF_6')
      | ~ m1_subset_1(D_72,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_72,plain,(
    ! [D_72] :
      ( r3_lattices('#skF_5',D_72,'#skF_8'(D_72))
      | ~ r2_hidden(D_72,'#skF_6')
      | ~ m1_subset_1(D_72,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_70,plain,(
    ! [D_72] :
      ( r2_hidden('#skF_8'(D_72),'#skF_7')
      | ~ r2_hidden(D_72,'#skF_6')
      | ~ m1_subset_1(D_72,u1_struct_0('#skF_5')) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_311,plain,(
    ! [D_154,B_155,C_156,E_157] :
      ( r2_hidden(D_154,a_2_5_lattice3(B_155,C_156))
      | ~ r2_hidden(E_157,C_156)
      | ~ r3_lattices(B_155,D_154,E_157)
      | ~ m1_subset_1(E_157,u1_struct_0(B_155))
      | ~ m1_subset_1(D_154,u1_struct_0(B_155))
      | ~ l3_lattices(B_155)
      | ~ v4_lattice3(B_155)
      | ~ v10_lattices(B_155)
      | v2_struct_0(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_411,plain,(
    ! [D_176,B_177,D_178] :
      ( r2_hidden(D_176,a_2_5_lattice3(B_177,'#skF_7'))
      | ~ r3_lattices(B_177,D_176,'#skF_8'(D_178))
      | ~ m1_subset_1('#skF_8'(D_178),u1_struct_0(B_177))
      | ~ m1_subset_1(D_176,u1_struct_0(B_177))
      | ~ l3_lattices(B_177)
      | ~ v4_lattice3(B_177)
      | ~ v10_lattices(B_177)
      | v2_struct_0(B_177)
      | ~ r2_hidden(D_178,'#skF_6')
      | ~ m1_subset_1(D_178,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_70,c_311])).

tff(c_424,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1('#skF_8'(D_72),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(D_72,'#skF_6')
      | ~ m1_subset_1(D_72,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_72,c_411])).

tff(c_434,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1('#skF_8'(D_72),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(D_72,'#skF_6')
      | ~ m1_subset_1(D_72,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_424])).

tff(c_436,plain,(
    ! [D_179] :
      ( r2_hidden(D_179,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1('#skF_8'(D_179),u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_179,'#skF_6')
      | ~ m1_subset_1(D_179,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_434])).

tff(c_440,plain,(
    ! [D_72] :
      ( r2_hidden(D_72,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ r2_hidden(D_72,'#skF_6')
      | ~ m1_subset_1(D_72,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_74,c_436])).

tff(c_441,plain,(
    ! [D_180] :
      ( r2_hidden(D_180,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ r2_hidden(D_180,'#skF_6')
      | ~ m1_subset_1(D_180,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_74,c_436])).

tff(c_46,plain,(
    ! [A_35,B_36,C_37] :
      ( '#skF_3'(A_35,B_36,C_37) = A_35
      | ~ r2_hidden(A_35,a_2_5_lattice3(B_36,C_37))
      | ~ l3_lattices(B_36)
      | ~ v4_lattice3(B_36)
      | ~ v10_lattices(B_36)
      | v2_struct_0(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_451,plain,(
    ! [D_180] :
      ( '#skF_3'(D_180,'#skF_5','#skF_7') = D_180
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(D_180,'#skF_6')
      | ~ m1_subset_1(D_180,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_441,c_46])).

tff(c_459,plain,(
    ! [D_180] :
      ( '#skF_3'(D_180,'#skF_5','#skF_7') = D_180
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(D_180,'#skF_6')
      | ~ m1_subset_1(D_180,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_451])).

tff(c_461,plain,(
    ! [D_181] :
      ( '#skF_3'(D_181,'#skF_5','#skF_7') = D_181
      | ~ r2_hidden(D_181,'#skF_6')
      | ~ m1_subset_1(D_181,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_459])).

tff(c_483,plain,(
    ! [B_17,C_23] :
      ( '#skF_3'('#skF_1'('#skF_5',B_17,C_23),'#skF_5','#skF_7') = '#skF_1'('#skF_5',B_17,C_23)
      | ~ r2_hidden('#skF_1'('#skF_5',B_17,C_23),'#skF_6')
      | r4_lattice3('#skF_5',B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_461])).

tff(c_507,plain,(
    ! [B_17,C_23] :
      ( '#skF_3'('#skF_1'('#skF_5',B_17,C_23),'#skF_5','#skF_7') = '#skF_1'('#skF_5',B_17,C_23)
      | ~ r2_hidden('#skF_1'('#skF_5',B_17,C_23),'#skF_6')
      | r4_lattice3('#skF_5',B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_483])).

tff(c_1179,plain,(
    ! [B_244,C_245] :
      ( '#skF_3'('#skF_1'('#skF_5',B_244,C_245),'#skF_5','#skF_7') = '#skF_1'('#skF_5',B_244,C_245)
      | ~ r2_hidden('#skF_1'('#skF_5',B_244,C_245),'#skF_6')
      | r4_lattice3('#skF_5',B_244,C_245)
      | ~ m1_subset_1(B_244,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_507])).

tff(c_1183,plain,(
    ! [B_17] :
      ( '#skF_3'('#skF_1'('#skF_5',B_17,'#skF_6'),'#skF_5','#skF_7') = '#skF_1'('#skF_5',B_17,'#skF_6')
      | r4_lattice3('#skF_5',B_17,'#skF_6')
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_1179])).

tff(c_1186,plain,(
    ! [B_17] :
      ( '#skF_3'('#skF_1'('#skF_5',B_17,'#skF_6'),'#skF_5','#skF_7') = '#skF_1'('#skF_5',B_17,'#skF_6')
      | r4_lattice3('#skF_5',B_17,'#skF_6')
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1183])).

tff(c_1188,plain,(
    ! [B_246] :
      ( '#skF_3'('#skF_1'('#skF_5',B_246,'#skF_6'),'#skF_5','#skF_7') = '#skF_1'('#skF_5',B_246,'#skF_6')
      | r4_lattice3('#skF_5',B_246,'#skF_6')
      | ~ m1_subset_1(B_246,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1186])).

tff(c_1212,plain,
    ( '#skF_3'('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),'#skF_5','#skF_7') = '#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_356,c_1188])).

tff(c_1248,plain,(
    '#skF_3'('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),'#skF_5','#skF_7') = '#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_1212])).

tff(c_48,plain,(
    ! [A_35,B_36,C_37] :
      ( m1_subset_1('#skF_3'(A_35,B_36,C_37),u1_struct_0(B_36))
      | ~ r2_hidden(A_35,a_2_5_lattice3(B_36,C_37))
      | ~ l3_lattices(B_36)
      | ~ v4_lattice3(B_36)
      | ~ v10_lattices(B_36)
      | v2_struct_0(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1281,plain,
    ( m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),a_2_5_lattice3('#skF_5','#skF_7'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1248,c_48])).

tff(c_1289,plain,
    ( m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),a_2_5_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_1281])).

tff(c_1290,plain,
    ( m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),a_2_5_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1289])).

tff(c_1292,plain,(
    ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),a_2_5_lattice3('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1290])).

tff(c_1296,plain,
    ( ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),'#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_440,c_1292])).

tff(c_1316,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1296])).

tff(c_1319,plain,
    ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_1316])).

tff(c_1322,plain,
    ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_356,c_1319])).

tff(c_1324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_369,c_1322])).

tff(c_1325,plain,(
    ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1296])).

tff(c_1329,plain,
    ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1325])).

tff(c_1332,plain,
    ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_356,c_1329])).

tff(c_1334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_369,c_1332])).

tff(c_1335,plain,(
    m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1290])).

tff(c_1336,plain,(
    r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),a_2_5_lattice3('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1290])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_145,plain,(
    ! [A_121,B_122,C_123] :
      ( r3_lattices(A_121,B_122,k15_lattice3(A_121,C_123))
      | ~ r2_hidden(B_122,C_123)
      | ~ m1_subset_1(B_122,u1_struct_0(A_121))
      | ~ l3_lattices(A_121)
      | ~ v4_lattice3(A_121)
      | ~ v10_lattices(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_148,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v4_lattice3('#skF_5')
    | ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_145,c_60])).

tff(c_154,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_148])).

tff(c_155,plain,
    ( ~ r2_hidden(k15_lattice3('#skF_5','#skF_6'),'#skF_7')
    | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_154])).

tff(c_156,plain,(
    ~ m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_159,plain,
    ( ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_156])).

tff(c_162,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_159])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_162])).

tff(c_166,plain,(
    m1_subset_1(k15_lattice3('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_197,plain,(
    ! [A_140,B_141,C_142] :
      ( r3_lattices(A_140,B_141,C_142)
      | ~ r1_lattices(A_140,B_141,C_142)
      | ~ m1_subset_1(C_142,u1_struct_0(A_140))
      | ~ m1_subset_1(B_141,u1_struct_0(A_140))
      | ~ l3_lattices(A_140)
      | ~ v9_lattices(A_140)
      | ~ v8_lattices(A_140)
      | ~ v6_lattices(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_199,plain,(
    ! [B_141] :
      ( r3_lattices('#skF_5',B_141,k15_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_141,k15_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_166,c_197])).

tff(c_214,plain,(
    ! [B_141] :
      ( r3_lattices('#skF_5',B_141,k15_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_141,k15_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_199])).

tff(c_215,plain,(
    ! [B_141] :
      ( r3_lattices('#skF_5',B_141,k15_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_141,k15_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_214])).

tff(c_225,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_228,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_225])).

tff(c_231,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_66,c_228])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_231])).

tff(c_235,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_215])).

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

tff(c_234,plain,(
    ! [B_141] :
      ( ~ v8_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | r3_lattices('#skF_5',B_141,k15_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_141,k15_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_236,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_239,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_236])).

tff(c_242,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_66,c_239])).

tff(c_244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_242])).

tff(c_245,plain,(
    ! [B_141] :
      ( ~ v8_lattices('#skF_5')
      | r3_lattices('#skF_5',B_141,k15_lattice3('#skF_5','#skF_6'))
      | ~ r1_lattices('#skF_5',B_141,k15_lattice3('#skF_5','#skF_6'))
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_263,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_245])).

tff(c_266,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_263])).

tff(c_269,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_66,c_266])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_269])).

tff(c_273,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_245])).

tff(c_246,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_56,plain,(
    ! [A_58,B_60] :
      ( k15_lattice3(A_58,a_2_5_lattice3(A_58,B_60)) = k15_lattice3(A_58,B_60)
      | ~ l3_lattices(A_58)
      | ~ v4_lattice3(A_58)
      | ~ v10_lattices(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_393,plain,(
    ! [A_170,B_171,B_172] :
      ( r3_lattices(A_170,B_171,k15_lattice3(A_170,B_172))
      | ~ r2_hidden(B_171,a_2_5_lattice3(A_170,B_172))
      | ~ m1_subset_1(B_171,u1_struct_0(A_170))
      | ~ l3_lattices(A_170)
      | ~ v4_lattice3(A_170)
      | ~ v10_lattices(A_170)
      | v2_struct_0(A_170)
      | ~ l3_lattices(A_170)
      | ~ v4_lattice3(A_170)
      | ~ v10_lattices(A_170)
      | v2_struct_0(A_170) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_145])).

tff(c_18,plain,(
    ! [A_2,B_3,C_4] :
      ( r1_lattices(A_2,B_3,C_4)
      | ~ r3_lattices(A_2,B_3,C_4)
      | ~ m1_subset_1(C_4,u1_struct_0(A_2))
      | ~ m1_subset_1(B_3,u1_struct_0(A_2))
      | ~ l3_lattices(A_2)
      | ~ v9_lattices(A_2)
      | ~ v8_lattices(A_2)
      | ~ v6_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_5833,plain,(
    ! [A_457,B_458,B_459] :
      ( r1_lattices(A_457,B_458,k15_lattice3(A_457,B_459))
      | ~ m1_subset_1(k15_lattice3(A_457,B_459),u1_struct_0(A_457))
      | ~ v9_lattices(A_457)
      | ~ v8_lattices(A_457)
      | ~ v6_lattices(A_457)
      | ~ r2_hidden(B_458,a_2_5_lattice3(A_457,B_459))
      | ~ m1_subset_1(B_458,u1_struct_0(A_457))
      | ~ l3_lattices(A_457)
      | ~ v4_lattice3(A_457)
      | ~ v10_lattices(A_457)
      | v2_struct_0(A_457) ) ),
    inference(resolution,[status(thm)],[c_393,c_18])).

tff(c_5849,plain,(
    ! [B_458] :
      ( r1_lattices('#skF_5',B_458,k15_lattice3('#skF_5','#skF_7'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | ~ r2_hidden(B_458,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_458,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_356,c_5833])).

tff(c_5884,plain,(
    ! [B_458] :
      ( r1_lattices('#skF_5',B_458,k15_lattice3('#skF_5','#skF_7'))
      | ~ r2_hidden(B_458,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_458,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_235,c_273,c_246,c_5849])).

tff(c_5909,plain,(
    ! [B_460] :
      ( r1_lattices('#skF_5',B_460,k15_lattice3('#skF_5','#skF_7'))
      | ~ r2_hidden(B_460,a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_460,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5884])).

tff(c_22,plain,(
    ! [A_5,B_17,C_23] :
      ( ~ r1_lattices(A_5,'#skF_1'(A_5,B_17,C_23),B_17)
      | r4_lattice3(A_5,B_17,C_23)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l3_lattices(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5916,plain,(
    ! [C_23] :
      ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_23)
      | ~ m1_subset_1(k15_lattice3('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_23),a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_23),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_5909,c_22])).

tff(c_5922,plain,(
    ! [C_23] :
      ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_23)
      | v2_struct_0('#skF_5')
      | ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_23),a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_23),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_356,c_5916])).

tff(c_7221,plain,(
    ! [C_515] :
      ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_515)
      | ~ r2_hidden('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_515),a_2_5_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),C_515),u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5922])).

tff(c_7224,plain,
    ( r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1336,c_7221])).

tff(c_7234,plain,(
    r4_lattice3('#skF_5',k15_lattice3('#skF_5','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1335,c_7224])).

tff(c_7236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_369,c_7234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:11:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.39/2.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.39/2.97  
% 8.39/2.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.39/2.97  %$ r4_lattice3 > r3_lattices > r1_lattices > r2_hidden > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_6_lattice3 > a_2_5_lattice3 > a_2_2_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_8 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 8.39/2.97  
% 8.39/2.97  %Foreground sorts:
% 8.39/2.97  
% 8.39/2.97  
% 8.39/2.97  %Background operators:
% 8.39/2.97  
% 8.39/2.97  
% 8.39/2.97  %Foreground operators:
% 8.39/2.97  tff(l3_lattices, type, l3_lattices: $i > $o).
% 8.39/2.97  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.39/2.97  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.39/2.97  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 8.39/2.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.39/2.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.39/2.97  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 8.39/2.97  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 8.39/2.97  tff('#skF_8', type, '#skF_8': $i > $i).
% 8.39/2.97  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.39/2.97  tff('#skF_7', type, '#skF_7': $i).
% 8.39/2.97  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 8.39/2.97  tff('#skF_5', type, '#skF_5': $i).
% 8.39/2.97  tff(v4_lattices, type, v4_lattices: $i > $o).
% 8.39/2.97  tff('#skF_6', type, '#skF_6': $i).
% 8.39/2.97  tff(v6_lattices, type, v6_lattices: $i > $o).
% 8.39/2.97  tff(v9_lattices, type, v9_lattices: $i > $o).
% 8.39/2.97  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 8.39/2.97  tff(a_2_5_lattice3, type, a_2_5_lattice3: ($i * $i) > $i).
% 8.39/2.97  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.39/2.97  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 8.39/2.97  tff(v5_lattices, type, v5_lattices: $i > $o).
% 8.39/2.97  tff(v10_lattices, type, v10_lattices: $i > $o).
% 8.39/2.97  tff(a_2_2_lattice3, type, a_2_2_lattice3: ($i * $i) > $i).
% 8.39/2.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.39/2.97  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.39/2.97  tff(v8_lattices, type, v8_lattices: $i > $o).
% 8.39/2.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.39/2.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.39/2.97  tff(a_2_6_lattice3, type, a_2_6_lattice3: ($i * $i) > $i).
% 8.39/2.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.39/2.97  tff(v7_lattices, type, v7_lattices: $i > $o).
% 8.39/2.97  
% 8.66/3.00  tff(f_204, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: ((![D]: (m1_subset_1(D, u1_struct_0(A)) => ~(r2_hidden(D, B) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ~(r3_lattices(A, D, E) & r2_hidden(E, C))))))) => r3_lattices(A, k15_lattice3(A, B), k15_lattice3(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_lattice3)).
% 8.66/3.00  tff(f_91, axiom, (![A, B]: ((~v2_struct_0(A) & l3_lattices(A)) => m1_subset_1(k15_lattice3(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k15_lattice3)).
% 8.66/3.00  tff(f_144, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (k15_lattice3(A, B) = k16_lattice3(A, a_2_2_lattice3(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_lattice3)).
% 8.66/3.00  tff(f_163, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r2_hidden(B, C) => (r3_lattices(A, B, k15_lattice3(A, C)) & r3_lattices(A, k16_lattice3(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_lattice3)).
% 8.66/3.00  tff(f_109, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_2_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r4_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_2_lattice3)).
% 8.66/3.00  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 8.66/3.00  tff(f_132, axiom, (![A, B, C]: ((((~v2_struct_0(B) & v10_lattices(B)) & v4_lattice3(B)) & l3_lattices(B)) => (r2_hidden(A, a_2_5_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r3_lattices(B, D, E)) & r2_hidden(E, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_5_lattice3)).
% 8.66/3.00  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattices)).
% 8.66/3.00  tff(f_66, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 8.66/3.00  tff(f_177, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: ((k15_lattice3(A, B) = k15_lattice3(A, a_2_5_lattice3(A, B))) & (k16_lattice3(A, B) = k16_lattice3(A, a_2_6_lattice3(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_lattice3)).
% 8.66/3.00  tff(c_68, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 8.66/3.00  tff(c_66, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 8.66/3.00  tff(c_64, plain, (v4_lattice3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 8.66/3.00  tff(c_62, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_204])).
% 8.66/3.00  tff(c_28, plain, (![A_27, B_28]: (m1_subset_1(k15_lattice3(A_27, B_28), u1_struct_0(A_27)) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.66/3.00  tff(c_50, plain, (![A_48, B_50]: (k16_lattice3(A_48, a_2_2_lattice3(A_48, B_50))=k15_lattice3(A_48, B_50) | ~l3_lattices(A_48) | ~v4_lattice3(A_48) | ~v10_lattices(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.66/3.00  tff(c_167, plain, (![A_124, C_125, B_126]: (r3_lattices(A_124, k16_lattice3(A_124, C_125), B_126) | ~r2_hidden(B_126, C_125) | ~m1_subset_1(B_126, u1_struct_0(A_124)) | ~l3_lattices(A_124) | ~v4_lattice3(A_124) | ~v10_lattices(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.66/3.00  tff(c_332, plain, (![A_163, B_164, B_165]: (r3_lattices(A_163, k15_lattice3(A_163, B_164), B_165) | ~r2_hidden(B_165, a_2_2_lattice3(A_163, B_164)) | ~m1_subset_1(B_165, u1_struct_0(A_163)) | ~l3_lattices(A_163) | ~v4_lattice3(A_163) | ~v10_lattices(A_163) | v2_struct_0(A_163) | ~l3_lattices(A_163) | ~v4_lattice3(A_163) | ~v10_lattices(A_163) | v2_struct_0(A_163))), inference(superposition, [status(thm), theory('equality')], [c_50, c_167])).
% 8.66/3.00  tff(c_60, plain, (~r3_lattices('#skF_5', k15_lattice3('#skF_5', '#skF_6'), k15_lattice3('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_204])).
% 8.66/3.00  tff(c_337, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_7'), a_2_2_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_332, c_60])).
% 8.66/3.00  tff(c_344, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_7'), a_2_2_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_337])).
% 8.66/3.00  tff(c_345, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_7'), a_2_2_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_344])).
% 8.66/3.00  tff(c_346, plain, (~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_345])).
% 8.66/3.00  tff(c_349, plain, (~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_346])).
% 8.66/3.00  tff(c_352, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_349])).
% 8.66/3.00  tff(c_354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_352])).
% 8.66/3.00  tff(c_356, plain, (m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_345])).
% 8.66/3.00  tff(c_30, plain, (![D_34, B_30, C_31]: (r2_hidden(D_34, a_2_2_lattice3(B_30, C_31)) | ~r4_lattice3(B_30, D_34, C_31) | ~m1_subset_1(D_34, u1_struct_0(B_30)) | ~l3_lattices(B_30) | ~v4_lattice3(B_30) | ~v10_lattices(B_30) | v2_struct_0(B_30))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.66/3.00  tff(c_355, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_7'), a_2_2_lattice3('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_345])).
% 8.66/3.00  tff(c_365, plain, (~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_30, c_355])).
% 8.66/3.00  tff(c_368, plain, (~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_356, c_365])).
% 8.66/3.00  tff(c_369, plain, (~r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_368])).
% 8.66/3.00  tff(c_24, plain, (![A_5, B_17, C_23]: (r2_hidden('#skF_1'(A_5, B_17, C_23), C_23) | r4_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.66/3.00  tff(c_26, plain, (![A_5, B_17, C_23]: (m1_subset_1('#skF_1'(A_5, B_17, C_23), u1_struct_0(A_5)) | r4_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.66/3.00  tff(c_74, plain, (![D_72]: (m1_subset_1('#skF_8'(D_72), u1_struct_0('#skF_5')) | ~r2_hidden(D_72, '#skF_6') | ~m1_subset_1(D_72, u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 8.66/3.00  tff(c_72, plain, (![D_72]: (r3_lattices('#skF_5', D_72, '#skF_8'(D_72)) | ~r2_hidden(D_72, '#skF_6') | ~m1_subset_1(D_72, u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 8.66/3.00  tff(c_70, plain, (![D_72]: (r2_hidden('#skF_8'(D_72), '#skF_7') | ~r2_hidden(D_72, '#skF_6') | ~m1_subset_1(D_72, u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_204])).
% 8.66/3.00  tff(c_311, plain, (![D_154, B_155, C_156, E_157]: (r2_hidden(D_154, a_2_5_lattice3(B_155, C_156)) | ~r2_hidden(E_157, C_156) | ~r3_lattices(B_155, D_154, E_157) | ~m1_subset_1(E_157, u1_struct_0(B_155)) | ~m1_subset_1(D_154, u1_struct_0(B_155)) | ~l3_lattices(B_155) | ~v4_lattice3(B_155) | ~v10_lattices(B_155) | v2_struct_0(B_155))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.66/3.00  tff(c_411, plain, (![D_176, B_177, D_178]: (r2_hidden(D_176, a_2_5_lattice3(B_177, '#skF_7')) | ~r3_lattices(B_177, D_176, '#skF_8'(D_178)) | ~m1_subset_1('#skF_8'(D_178), u1_struct_0(B_177)) | ~m1_subset_1(D_176, u1_struct_0(B_177)) | ~l3_lattices(B_177) | ~v4_lattice3(B_177) | ~v10_lattices(B_177) | v2_struct_0(B_177) | ~r2_hidden(D_178, '#skF_6') | ~m1_subset_1(D_178, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_70, c_311])).
% 8.66/3.00  tff(c_424, plain, (![D_72]: (r2_hidden(D_72, a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_8'(D_72), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(D_72, '#skF_6') | ~m1_subset_1(D_72, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_72, c_411])).
% 8.66/3.00  tff(c_434, plain, (![D_72]: (r2_hidden(D_72, a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_8'(D_72), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~r2_hidden(D_72, '#skF_6') | ~m1_subset_1(D_72, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_424])).
% 8.66/3.00  tff(c_436, plain, (![D_179]: (r2_hidden(D_179, a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_8'(D_179), u1_struct_0('#skF_5')) | ~r2_hidden(D_179, '#skF_6') | ~m1_subset_1(D_179, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_434])).
% 8.66/3.00  tff(c_440, plain, (![D_72]: (r2_hidden(D_72, a_2_5_lattice3('#skF_5', '#skF_7')) | ~r2_hidden(D_72, '#skF_6') | ~m1_subset_1(D_72, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_74, c_436])).
% 8.66/3.00  tff(c_441, plain, (![D_180]: (r2_hidden(D_180, a_2_5_lattice3('#skF_5', '#skF_7')) | ~r2_hidden(D_180, '#skF_6') | ~m1_subset_1(D_180, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_74, c_436])).
% 8.66/3.00  tff(c_46, plain, (![A_35, B_36, C_37]: ('#skF_3'(A_35, B_36, C_37)=A_35 | ~r2_hidden(A_35, a_2_5_lattice3(B_36, C_37)) | ~l3_lattices(B_36) | ~v4_lattice3(B_36) | ~v10_lattices(B_36) | v2_struct_0(B_36))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.66/3.00  tff(c_451, plain, (![D_180]: ('#skF_3'(D_180, '#skF_5', '#skF_7')=D_180 | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(D_180, '#skF_6') | ~m1_subset_1(D_180, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_441, c_46])).
% 8.66/3.00  tff(c_459, plain, (![D_180]: ('#skF_3'(D_180, '#skF_5', '#skF_7')=D_180 | v2_struct_0('#skF_5') | ~r2_hidden(D_180, '#skF_6') | ~m1_subset_1(D_180, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_451])).
% 8.66/3.00  tff(c_461, plain, (![D_181]: ('#skF_3'(D_181, '#skF_5', '#skF_7')=D_181 | ~r2_hidden(D_181, '#skF_6') | ~m1_subset_1(D_181, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_459])).
% 8.66/3.00  tff(c_483, plain, (![B_17, C_23]: ('#skF_3'('#skF_1'('#skF_5', B_17, C_23), '#skF_5', '#skF_7')='#skF_1'('#skF_5', B_17, C_23) | ~r2_hidden('#skF_1'('#skF_5', B_17, C_23), '#skF_6') | r4_lattice3('#skF_5', B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_461])).
% 8.66/3.00  tff(c_507, plain, (![B_17, C_23]: ('#skF_3'('#skF_1'('#skF_5', B_17, C_23), '#skF_5', '#skF_7')='#skF_1'('#skF_5', B_17, C_23) | ~r2_hidden('#skF_1'('#skF_5', B_17, C_23), '#skF_6') | r4_lattice3('#skF_5', B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_483])).
% 8.66/3.00  tff(c_1179, plain, (![B_244, C_245]: ('#skF_3'('#skF_1'('#skF_5', B_244, C_245), '#skF_5', '#skF_7')='#skF_1'('#skF_5', B_244, C_245) | ~r2_hidden('#skF_1'('#skF_5', B_244, C_245), '#skF_6') | r4_lattice3('#skF_5', B_244, C_245) | ~m1_subset_1(B_244, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_507])).
% 8.66/3.00  tff(c_1183, plain, (![B_17]: ('#skF_3'('#skF_1'('#skF_5', B_17, '#skF_6'), '#skF_5', '#skF_7')='#skF_1'('#skF_5', B_17, '#skF_6') | r4_lattice3('#skF_5', B_17, '#skF_6') | ~m1_subset_1(B_17, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_1179])).
% 8.66/3.00  tff(c_1186, plain, (![B_17]: ('#skF_3'('#skF_1'('#skF_5', B_17, '#skF_6'), '#skF_5', '#skF_7')='#skF_1'('#skF_5', B_17, '#skF_6') | r4_lattice3('#skF_5', B_17, '#skF_6') | ~m1_subset_1(B_17, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1183])).
% 8.66/3.00  tff(c_1188, plain, (![B_246]: ('#skF_3'('#skF_1'('#skF_5', B_246, '#skF_6'), '#skF_5', '#skF_7')='#skF_1'('#skF_5', B_246, '#skF_6') | r4_lattice3('#skF_5', B_246, '#skF_6') | ~m1_subset_1(B_246, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_1186])).
% 8.66/3.00  tff(c_1212, plain, ('#skF_3'('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), '#skF_5', '#skF_7')='#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_356, c_1188])).
% 8.66/3.00  tff(c_1248, plain, ('#skF_3'('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), '#skF_5', '#skF_7')='#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_369, c_1212])).
% 8.66/3.00  tff(c_48, plain, (![A_35, B_36, C_37]: (m1_subset_1('#skF_3'(A_35, B_36, C_37), u1_struct_0(B_36)) | ~r2_hidden(A_35, a_2_5_lattice3(B_36, C_37)) | ~l3_lattices(B_36) | ~v4_lattice3(B_36) | ~v10_lattices(B_36) | v2_struct_0(B_36))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.66/3.00  tff(c_1281, plain, (m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), a_2_5_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1248, c_48])).
% 8.66/3.00  tff(c_1289, plain, (m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), a_2_5_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_1281])).
% 8.66/3.00  tff(c_1290, plain, (m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), a_2_5_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1289])).
% 8.66/3.00  tff(c_1292, plain, (~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), a_2_5_lattice3('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_1290])).
% 8.66/3.00  tff(c_1296, plain, (~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_440, c_1292])).
% 8.66/3.00  tff(c_1316, plain, (~m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_1296])).
% 8.66/3.00  tff(c_1319, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_26, c_1316])).
% 8.66/3.00  tff(c_1322, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_356, c_1319])).
% 8.66/3.00  tff(c_1324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_369, c_1322])).
% 8.66/3.00  tff(c_1325, plain, (~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_1296])).
% 8.66/3.00  tff(c_1329, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_24, c_1325])).
% 8.66/3.00  tff(c_1332, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_356, c_1329])).
% 8.66/3.00  tff(c_1334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_369, c_1332])).
% 8.66/3.00  tff(c_1335, plain, (m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1290])).
% 8.66/3.00  tff(c_1336, plain, (r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), a_2_5_lattice3('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_1290])).
% 8.66/3.00  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.66/3.00  tff(c_145, plain, (![A_121, B_122, C_123]: (r3_lattices(A_121, B_122, k15_lattice3(A_121, C_123)) | ~r2_hidden(B_122, C_123) | ~m1_subset_1(B_122, u1_struct_0(A_121)) | ~l3_lattices(A_121) | ~v4_lattice3(A_121) | ~v10_lattices(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_163])).
% 8.66/3.00  tff(c_148, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_6'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_145, c_60])).
% 8.66/3.00  tff(c_154, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_6'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_148])).
% 8.66/3.00  tff(c_155, plain, (~r2_hidden(k15_lattice3('#skF_5', '#skF_6'), '#skF_7') | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_154])).
% 8.66/3.00  tff(c_156, plain, (~m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_155])).
% 8.66/3.00  tff(c_159, plain, (~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_156])).
% 8.66/3.00  tff(c_162, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_159])).
% 8.66/3.00  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_162])).
% 8.66/3.00  tff(c_166, plain, (m1_subset_1(k15_lattice3('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_155])).
% 8.66/3.00  tff(c_197, plain, (![A_140, B_141, C_142]: (r3_lattices(A_140, B_141, C_142) | ~r1_lattices(A_140, B_141, C_142) | ~m1_subset_1(C_142, u1_struct_0(A_140)) | ~m1_subset_1(B_141, u1_struct_0(A_140)) | ~l3_lattices(A_140) | ~v9_lattices(A_140) | ~v8_lattices(A_140) | ~v6_lattices(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.66/3.00  tff(c_199, plain, (![B_141]: (r3_lattices('#skF_5', B_141, k15_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_141, k15_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_141, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_166, c_197])).
% 8.66/3.00  tff(c_214, plain, (![B_141]: (r3_lattices('#skF_5', B_141, k15_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_141, k15_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_141, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_199])).
% 8.66/3.00  tff(c_215, plain, (![B_141]: (r3_lattices('#skF_5', B_141, k15_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_141, k15_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_141, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_68, c_214])).
% 8.66/3.00  tff(c_225, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_215])).
% 8.66/3.00  tff(c_228, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_225])).
% 8.66/3.00  tff(c_231, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_66, c_228])).
% 8.66/3.00  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_231])).
% 8.66/3.00  tff(c_235, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_215])).
% 8.66/3.00  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.66/3.00  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.66/3.00  tff(c_234, plain, (![B_141]: (~v8_lattices('#skF_5') | ~v9_lattices('#skF_5') | r3_lattices('#skF_5', B_141, k15_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_141, k15_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_141, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_215])).
% 8.66/3.00  tff(c_236, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_234])).
% 8.66/3.00  tff(c_239, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_236])).
% 8.66/3.00  tff(c_242, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_66, c_239])).
% 8.66/3.00  tff(c_244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_242])).
% 8.66/3.00  tff(c_245, plain, (![B_141]: (~v8_lattices('#skF_5') | r3_lattices('#skF_5', B_141, k15_lattice3('#skF_5', '#skF_6')) | ~r1_lattices('#skF_5', B_141, k15_lattice3('#skF_5', '#skF_6')) | ~m1_subset_1(B_141, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_234])).
% 8.66/3.00  tff(c_263, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_245])).
% 8.66/3.00  tff(c_266, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_263])).
% 8.66/3.00  tff(c_269, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_66, c_266])).
% 8.66/3.00  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_269])).
% 8.66/3.00  tff(c_273, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_245])).
% 8.66/3.00  tff(c_246, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_234])).
% 8.66/3.00  tff(c_56, plain, (![A_58, B_60]: (k15_lattice3(A_58, a_2_5_lattice3(A_58, B_60))=k15_lattice3(A_58, B_60) | ~l3_lattices(A_58) | ~v4_lattice3(A_58) | ~v10_lattices(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_177])).
% 8.66/3.00  tff(c_393, plain, (![A_170, B_171, B_172]: (r3_lattices(A_170, B_171, k15_lattice3(A_170, B_172)) | ~r2_hidden(B_171, a_2_5_lattice3(A_170, B_172)) | ~m1_subset_1(B_171, u1_struct_0(A_170)) | ~l3_lattices(A_170) | ~v4_lattice3(A_170) | ~v10_lattices(A_170) | v2_struct_0(A_170) | ~l3_lattices(A_170) | ~v4_lattice3(A_170) | ~v10_lattices(A_170) | v2_struct_0(A_170))), inference(superposition, [status(thm), theory('equality')], [c_56, c_145])).
% 8.66/3.00  tff(c_18, plain, (![A_2, B_3, C_4]: (r1_lattices(A_2, B_3, C_4) | ~r3_lattices(A_2, B_3, C_4) | ~m1_subset_1(C_4, u1_struct_0(A_2)) | ~m1_subset_1(B_3, u1_struct_0(A_2)) | ~l3_lattices(A_2) | ~v9_lattices(A_2) | ~v8_lattices(A_2) | ~v6_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.66/3.00  tff(c_5833, plain, (![A_457, B_458, B_459]: (r1_lattices(A_457, B_458, k15_lattice3(A_457, B_459)) | ~m1_subset_1(k15_lattice3(A_457, B_459), u1_struct_0(A_457)) | ~v9_lattices(A_457) | ~v8_lattices(A_457) | ~v6_lattices(A_457) | ~r2_hidden(B_458, a_2_5_lattice3(A_457, B_459)) | ~m1_subset_1(B_458, u1_struct_0(A_457)) | ~l3_lattices(A_457) | ~v4_lattice3(A_457) | ~v10_lattices(A_457) | v2_struct_0(A_457))), inference(resolution, [status(thm)], [c_393, c_18])).
% 8.66/3.00  tff(c_5849, plain, (![B_458]: (r1_lattices('#skF_5', B_458, k15_lattice3('#skF_5', '#skF_7')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~r2_hidden(B_458, a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_458, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_356, c_5833])).
% 8.66/3.00  tff(c_5884, plain, (![B_458]: (r1_lattices('#skF_5', B_458, k15_lattice3('#skF_5', '#skF_7')) | ~r2_hidden(B_458, a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_458, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_235, c_273, c_246, c_5849])).
% 8.66/3.00  tff(c_5909, plain, (![B_460]: (r1_lattices('#skF_5', B_460, k15_lattice3('#skF_5', '#skF_7')) | ~r2_hidden(B_460, a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_460, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_5884])).
% 8.66/3.00  tff(c_22, plain, (![A_5, B_17, C_23]: (~r1_lattices(A_5, '#skF_1'(A_5, B_17, C_23), B_17) | r4_lattice3(A_5, B_17, C_23) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l3_lattices(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.66/3.00  tff(c_5916, plain, (![C_23]: (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_23) | ~m1_subset_1(k15_lattice3('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_23), a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_23), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_5909, c_22])).
% 8.66/3.00  tff(c_5922, plain, (![C_23]: (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_23) | v2_struct_0('#skF_5') | ~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_23), a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_23), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_356, c_5916])).
% 8.66/3.00  tff(c_7221, plain, (![C_515]: (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_515) | ~r2_hidden('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_515), a_2_5_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), C_515), u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_68, c_5922])).
% 8.66/3.00  tff(c_7224, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1336, c_7221])).
% 8.66/3.00  tff(c_7234, plain, (r4_lattice3('#skF_5', k15_lattice3('#skF_5', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1335, c_7224])).
% 8.66/3.00  tff(c_7236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_369, c_7234])).
% 8.66/3.00  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.66/3.00  
% 8.66/3.00  Inference rules
% 8.66/3.00  ----------------------
% 8.66/3.00  #Ref     : 0
% 8.66/3.00  #Sup     : 1394
% 8.66/3.00  #Fact    : 0
% 8.66/3.00  #Define  : 0
% 8.66/3.00  #Split   : 22
% 8.66/3.00  #Chain   : 0
% 8.66/3.00  #Close   : 0
% 8.66/3.00  
% 8.66/3.00  Ordering : KBO
% 8.66/3.00  
% 8.66/3.00  Simplification rules
% 8.66/3.00  ----------------------
% 8.66/3.00  #Subsume      : 226
% 8.66/3.00  #Demod        : 2436
% 8.66/3.00  #Tautology    : 210
% 8.66/3.00  #SimpNegUnit  : 614
% 8.66/3.00  #BackRed      : 0
% 8.66/3.00  
% 8.66/3.00  #Partial instantiations: 0
% 8.66/3.00  #Strategies tried      : 1
% 8.66/3.00  
% 8.66/3.00  Timing (in seconds)
% 8.66/3.00  ----------------------
% 8.66/3.00  Preprocessing        : 0.32
% 8.66/3.00  Parsing              : 0.17
% 8.66/3.00  CNF conversion       : 0.03
% 8.66/3.00  Main loop            : 1.89
% 8.66/3.00  Inferencing          : 0.66
% 8.66/3.00  Reduction            : 0.64
% 8.66/3.00  Demodulation         : 0.43
% 8.66/3.00  BG Simplification    : 0.06
% 8.66/3.00  Subsumption          : 0.40
% 8.66/3.00  Abstraction          : 0.09
% 8.66/3.00  MUC search           : 0.00
% 8.66/3.01  Cooper               : 0.00
% 8.66/3.01  Total                : 2.26
% 8.66/3.01  Index Insertion      : 0.00
% 8.66/3.01  Index Deletion       : 0.00
% 8.66/3.01  Index Matching       : 0.00
% 8.66/3.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
