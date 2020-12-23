%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:49 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 194 expanded)
%              Number of leaves         :   28 (  83 expanded)
%              Depth                    :   25
%              Number of atoms          :  202 ( 792 expanded)
%              Number of equality atoms :   15 (  70 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(a_2_1_lattice3,type,(
    a_2_1_lattice3: ( $i * $i ) > $i )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_1_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r3_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

tff(f_61,axiom,(
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

tff(f_43,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v4_lattice3(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( r2_hidden(B,C)
                & r4_lattice3(A,B,C) )
             => k15_lattice3(A,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] : k16_lattice3(A,B) = k15_lattice3(A,a_2_1_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattice3)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_30,plain,(
    k16_lattice3('#skF_4','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_38,plain,(
    l3_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_32,plain,(
    r3_lattice3('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_20,plain,(
    ! [D_53,B_49,C_50] :
      ( r2_hidden(D_53,a_2_1_lattice3(B_49,C_50))
      | ~ r3_lattice3(B_49,D_53,C_50)
      | ~ m1_subset_1(D_53,u1_struct_0(B_49))
      | ~ l3_lattices(B_49)
      | v2_struct_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,(
    v10_lattices('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_40,plain,(
    v4_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_14,plain,(
    ! [A_23,B_35,C_41] :
      ( r2_hidden('#skF_2'(A_23,B_35,C_41),C_41)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_88,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_hidden('#skF_2'(A_82,B_83,C_84),C_84)
      | r4_lattice3(A_82,B_83,C_84)
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l3_lattices(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [A_48,B_49,C_50] :
      ( '#skF_3'(A_48,B_49,C_50) = A_48
      | ~ r2_hidden(A_48,a_2_1_lattice3(B_49,C_50))
      | ~ l3_lattices(B_49)
      | v2_struct_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_389,plain,(
    ! [A_150,B_151,B_152,C_153] :
      ( '#skF_3'('#skF_2'(A_150,B_151,a_2_1_lattice3(B_152,C_153)),B_152,C_153) = '#skF_2'(A_150,B_151,a_2_1_lattice3(B_152,C_153))
      | ~ l3_lattices(B_152)
      | v2_struct_0(B_152)
      | r4_lattice3(A_150,B_151,a_2_1_lattice3(B_152,C_153))
      | ~ m1_subset_1(B_151,u1_struct_0(A_150))
      | ~ l3_lattices(A_150)
      | v2_struct_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_88,c_24])).

tff(c_22,plain,(
    ! [B_49,A_48,C_50] :
      ( r3_lattice3(B_49,'#skF_3'(A_48,B_49,C_50),C_50)
      | ~ r2_hidden(A_48,a_2_1_lattice3(B_49,C_50))
      | ~ l3_lattices(B_49)
      | v2_struct_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_26,plain,(
    ! [A_48,B_49,C_50] :
      ( m1_subset_1('#skF_3'(A_48,B_49,C_50),u1_struct_0(B_49))
      | ~ r2_hidden(A_48,a_2_1_lattice3(B_49,C_50))
      | ~ l3_lattices(B_49)
      | v2_struct_0(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_105,plain,(
    ! [A_103,B_104,D_105,C_106] :
      ( r1_lattices(A_103,B_104,D_105)
      | ~ r2_hidden(D_105,C_106)
      | ~ m1_subset_1(D_105,u1_struct_0(A_103))
      | ~ r3_lattice3(A_103,B_104,C_106)
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l3_lattices(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [A_107,B_108] :
      ( r1_lattices(A_107,B_108,'#skF_5')
      | ~ m1_subset_1('#skF_5',u1_struct_0(A_107))
      | ~ r3_lattice3(A_107,B_108,'#skF_6')
      | ~ m1_subset_1(B_108,u1_struct_0(A_107))
      | ~ l3_lattices(A_107)
      | v2_struct_0(A_107) ) ),
    inference(resolution,[status(thm)],[c_34,c_105])).

tff(c_120,plain,(
    ! [B_108] :
      ( r1_lattices('#skF_4',B_108,'#skF_5')
      | ~ r3_lattice3('#skF_4',B_108,'#skF_6')
      | ~ m1_subset_1(B_108,u1_struct_0('#skF_4'))
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_118])).

tff(c_123,plain,(
    ! [B_108] :
      ( r1_lattices('#skF_4',B_108,'#skF_5')
      | ~ r3_lattice3('#skF_4',B_108,'#skF_6')
      | ~ m1_subset_1(B_108,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_120])).

tff(c_125,plain,(
    ! [B_109] :
      ( r1_lattices('#skF_4',B_109,'#skF_5')
      | ~ r3_lattice3('#skF_4',B_109,'#skF_6')
      | ~ m1_subset_1(B_109,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_123])).

tff(c_137,plain,(
    ! [A_48,C_50] :
      ( r1_lattices('#skF_4','#skF_3'(A_48,'#skF_4',C_50),'#skF_5')
      | ~ r3_lattice3('#skF_4','#skF_3'(A_48,'#skF_4',C_50),'#skF_6')
      | ~ r2_hidden(A_48,a_2_1_lattice3('#skF_4',C_50))
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_125])).

tff(c_151,plain,(
    ! [A_48,C_50] :
      ( r1_lattices('#skF_4','#skF_3'(A_48,'#skF_4',C_50),'#skF_5')
      | ~ r3_lattice3('#skF_4','#skF_3'(A_48,'#skF_4',C_50),'#skF_6')
      | ~ r2_hidden(A_48,a_2_1_lattice3('#skF_4',C_50))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_137])).

tff(c_169,plain,(
    ! [A_114,C_115] :
      ( r1_lattices('#skF_4','#skF_3'(A_114,'#skF_4',C_115),'#skF_5')
      | ~ r3_lattice3('#skF_4','#skF_3'(A_114,'#skF_4',C_115),'#skF_6')
      | ~ r2_hidden(A_114,a_2_1_lattice3('#skF_4',C_115)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_151])).

tff(c_176,plain,(
    ! [A_48] :
      ( r1_lattices('#skF_4','#skF_3'(A_48,'#skF_4','#skF_6'),'#skF_5')
      | ~ r2_hidden(A_48,a_2_1_lattice3('#skF_4','#skF_6'))
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_169])).

tff(c_181,plain,(
    ! [A_48] :
      ( r1_lattices('#skF_4','#skF_3'(A_48,'#skF_4','#skF_6'),'#skF_5')
      | ~ r2_hidden(A_48,a_2_1_lattice3('#skF_4','#skF_6'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_176])).

tff(c_182,plain,(
    ! [A_48] :
      ( r1_lattices('#skF_4','#skF_3'(A_48,'#skF_4','#skF_6'),'#skF_5')
      | ~ r2_hidden(A_48,a_2_1_lattice3('#skF_4','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_181])).

tff(c_400,plain,(
    ! [A_150,B_151] :
      ( r1_lattices('#skF_4','#skF_2'(A_150,B_151,a_2_1_lattice3('#skF_4','#skF_6')),'#skF_5')
      | ~ r2_hidden('#skF_2'(A_150,B_151,a_2_1_lattice3('#skF_4','#skF_6')),a_2_1_lattice3('#skF_4','#skF_6'))
      | ~ l3_lattices('#skF_4')
      | v2_struct_0('#skF_4')
      | r4_lattice3(A_150,B_151,a_2_1_lattice3('#skF_4','#skF_6'))
      | ~ m1_subset_1(B_151,u1_struct_0(A_150))
      | ~ l3_lattices(A_150)
      | v2_struct_0(A_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_182])).

tff(c_419,plain,(
    ! [A_150,B_151] :
      ( r1_lattices('#skF_4','#skF_2'(A_150,B_151,a_2_1_lattice3('#skF_4','#skF_6')),'#skF_5')
      | ~ r2_hidden('#skF_2'(A_150,B_151,a_2_1_lattice3('#skF_4','#skF_6')),a_2_1_lattice3('#skF_4','#skF_6'))
      | v2_struct_0('#skF_4')
      | r4_lattice3(A_150,B_151,a_2_1_lattice3('#skF_4','#skF_6'))
      | ~ m1_subset_1(B_151,u1_struct_0(A_150))
      | ~ l3_lattices(A_150)
      | v2_struct_0(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_400])).

tff(c_457,plain,(
    ! [A_157,B_158] :
      ( r1_lattices('#skF_4','#skF_2'(A_157,B_158,a_2_1_lattice3('#skF_4','#skF_6')),'#skF_5')
      | ~ r2_hidden('#skF_2'(A_157,B_158,a_2_1_lattice3('#skF_4','#skF_6')),a_2_1_lattice3('#skF_4','#skF_6'))
      | r4_lattice3(A_157,B_158,a_2_1_lattice3('#skF_4','#skF_6'))
      | ~ m1_subset_1(B_158,u1_struct_0(A_157))
      | ~ l3_lattices(A_157)
      | v2_struct_0(A_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_419])).

tff(c_470,plain,(
    ! [A_159,B_160] :
      ( r1_lattices('#skF_4','#skF_2'(A_159,B_160,a_2_1_lattice3('#skF_4','#skF_6')),'#skF_5')
      | r4_lattice3(A_159,B_160,a_2_1_lattice3('#skF_4','#skF_6'))
      | ~ m1_subset_1(B_160,u1_struct_0(A_159))
      | ~ l3_lattices(A_159)
      | v2_struct_0(A_159) ) ),
    inference(resolution,[status(thm)],[c_14,c_457])).

tff(c_12,plain,(
    ! [A_23,B_35,C_41] :
      ( ~ r1_lattices(A_23,'#skF_2'(A_23,B_35,C_41),B_35)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_474,plain,
    ( r4_lattice3('#skF_4','#skF_5',a_2_1_lattice3('#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l3_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_470,c_12])).

tff(c_477,plain,
    ( r4_lattice3('#skF_4','#skF_5',a_2_1_lattice3('#skF_4','#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_474])).

tff(c_478,plain,(
    r4_lattice3('#skF_4','#skF_5',a_2_1_lattice3('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_477])).

tff(c_28,plain,(
    ! [A_54,C_60,B_58] :
      ( k15_lattice3(A_54,C_60) = B_58
      | ~ r4_lattice3(A_54,B_58,C_60)
      | ~ r2_hidden(B_58,C_60)
      | ~ m1_subset_1(B_58,u1_struct_0(A_54))
      | ~ l3_lattices(A_54)
      | ~ v4_lattice3(A_54)
      | ~ v10_lattices(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_480,plain,
    ( k15_lattice3('#skF_4',a_2_1_lattice3('#skF_4','#skF_6')) = '#skF_5'
    | ~ r2_hidden('#skF_5',a_2_1_lattice3('#skF_4','#skF_6'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l3_lattices('#skF_4')
    | ~ v4_lattice3('#skF_4')
    | ~ v10_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_478,c_28])).

tff(c_483,plain,
    ( k15_lattice3('#skF_4',a_2_1_lattice3('#skF_4','#skF_6')) = '#skF_5'
    | ~ r2_hidden('#skF_5',a_2_1_lattice3('#skF_4','#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_480])).

tff(c_484,plain,
    ( k15_lattice3('#skF_4',a_2_1_lattice3('#skF_4','#skF_6')) = '#skF_5'
    | ~ r2_hidden('#skF_5',a_2_1_lattice3('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_483])).

tff(c_485,plain,(
    ~ r2_hidden('#skF_5',a_2_1_lattice3('#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_484])).

tff(c_488,plain,
    ( ~ r3_lattice3('#skF_4','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l3_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_485])).

tff(c_491,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32,c_488])).

tff(c_493,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_491])).

tff(c_494,plain,(
    k15_lattice3('#skF_4',a_2_1_lattice3('#skF_4','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_484])).

tff(c_18,plain,(
    ! [A_45,B_47] :
      ( k15_lattice3(A_45,a_2_1_lattice3(A_45,B_47)) = k16_lattice3(A_45,B_47)
      | ~ l3_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_534,plain,
    ( k16_lattice3('#skF_4','#skF_6') = '#skF_5'
    | ~ l3_lattices('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_18])).

tff(c_541,plain,
    ( k16_lattice3('#skF_4','#skF_6') = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_534])).

tff(c_543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_30,c_541])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.41  
% 2.77/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.42  %$ r4_lattice3 > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.77/1.42  
% 2.77/1.42  %Foreground sorts:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Background operators:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Foreground operators:
% 2.77/1.42  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.77/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.77/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.42  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 2.77/1.42  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 2.77/1.42  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.77/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.77/1.42  tff(a_2_1_lattice3, type, a_2_1_lattice3: ($i * $i) > $i).
% 2.77/1.42  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 2.77/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.77/1.42  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 2.77/1.42  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.42  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.77/1.42  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 2.77/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.42  
% 2.77/1.43  tff(f_122, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r3_lattice3(A, B, C)) => (k16_lattice3(A, C) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_lattice3)).
% 2.77/1.43  tff(f_83, axiom, (![A, B, C]: ((~v2_struct_0(B) & l3_lattices(B)) => (r2_hidden(A, a_2_1_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r3_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 2.77/1.43  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 2.77/1.43  tff(f_43, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 2.77/1.43  tff(f_102, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r4_lattice3(A, B, C)) => (k15_lattice3(A, C) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_lattice3)).
% 2.77/1.43  tff(f_69, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (k16_lattice3(A, B) = k15_lattice3(A, a_2_1_lattice3(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d22_lattice3)).
% 2.77/1.43  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.77/1.43  tff(c_30, plain, (k16_lattice3('#skF_4', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.77/1.43  tff(c_38, plain, (l3_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.77/1.43  tff(c_36, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.77/1.43  tff(c_32, plain, (r3_lattice3('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.77/1.43  tff(c_20, plain, (![D_53, B_49, C_50]: (r2_hidden(D_53, a_2_1_lattice3(B_49, C_50)) | ~r3_lattice3(B_49, D_53, C_50) | ~m1_subset_1(D_53, u1_struct_0(B_49)) | ~l3_lattices(B_49) | v2_struct_0(B_49))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.77/1.43  tff(c_42, plain, (v10_lattices('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.77/1.43  tff(c_40, plain, (v4_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.77/1.43  tff(c_14, plain, (![A_23, B_35, C_41]: (r2_hidden('#skF_2'(A_23, B_35, C_41), C_41) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.77/1.43  tff(c_88, plain, (![A_82, B_83, C_84]: (r2_hidden('#skF_2'(A_82, B_83, C_84), C_84) | r4_lattice3(A_82, B_83, C_84) | ~m1_subset_1(B_83, u1_struct_0(A_82)) | ~l3_lattices(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.77/1.43  tff(c_24, plain, (![A_48, B_49, C_50]: ('#skF_3'(A_48, B_49, C_50)=A_48 | ~r2_hidden(A_48, a_2_1_lattice3(B_49, C_50)) | ~l3_lattices(B_49) | v2_struct_0(B_49))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.77/1.43  tff(c_389, plain, (![A_150, B_151, B_152, C_153]: ('#skF_3'('#skF_2'(A_150, B_151, a_2_1_lattice3(B_152, C_153)), B_152, C_153)='#skF_2'(A_150, B_151, a_2_1_lattice3(B_152, C_153)) | ~l3_lattices(B_152) | v2_struct_0(B_152) | r4_lattice3(A_150, B_151, a_2_1_lattice3(B_152, C_153)) | ~m1_subset_1(B_151, u1_struct_0(A_150)) | ~l3_lattices(A_150) | v2_struct_0(A_150))), inference(resolution, [status(thm)], [c_88, c_24])).
% 2.77/1.43  tff(c_22, plain, (![B_49, A_48, C_50]: (r3_lattice3(B_49, '#skF_3'(A_48, B_49, C_50), C_50) | ~r2_hidden(A_48, a_2_1_lattice3(B_49, C_50)) | ~l3_lattices(B_49) | v2_struct_0(B_49))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.77/1.43  tff(c_26, plain, (![A_48, B_49, C_50]: (m1_subset_1('#skF_3'(A_48, B_49, C_50), u1_struct_0(B_49)) | ~r2_hidden(A_48, a_2_1_lattice3(B_49, C_50)) | ~l3_lattices(B_49) | v2_struct_0(B_49))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.77/1.43  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.77/1.43  tff(c_105, plain, (![A_103, B_104, D_105, C_106]: (r1_lattices(A_103, B_104, D_105) | ~r2_hidden(D_105, C_106) | ~m1_subset_1(D_105, u1_struct_0(A_103)) | ~r3_lattice3(A_103, B_104, C_106) | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~l3_lattices(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.77/1.43  tff(c_118, plain, (![A_107, B_108]: (r1_lattices(A_107, B_108, '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0(A_107)) | ~r3_lattice3(A_107, B_108, '#skF_6') | ~m1_subset_1(B_108, u1_struct_0(A_107)) | ~l3_lattices(A_107) | v2_struct_0(A_107))), inference(resolution, [status(thm)], [c_34, c_105])).
% 2.77/1.43  tff(c_120, plain, (![B_108]: (r1_lattices('#skF_4', B_108, '#skF_5') | ~r3_lattice3('#skF_4', B_108, '#skF_6') | ~m1_subset_1(B_108, u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_118])).
% 2.77/1.43  tff(c_123, plain, (![B_108]: (r1_lattices('#skF_4', B_108, '#skF_5') | ~r3_lattice3('#skF_4', B_108, '#skF_6') | ~m1_subset_1(B_108, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_120])).
% 2.77/1.43  tff(c_125, plain, (![B_109]: (r1_lattices('#skF_4', B_109, '#skF_5') | ~r3_lattice3('#skF_4', B_109, '#skF_6') | ~m1_subset_1(B_109, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_44, c_123])).
% 2.77/1.43  tff(c_137, plain, (![A_48, C_50]: (r1_lattices('#skF_4', '#skF_3'(A_48, '#skF_4', C_50), '#skF_5') | ~r3_lattice3('#skF_4', '#skF_3'(A_48, '#skF_4', C_50), '#skF_6') | ~r2_hidden(A_48, a_2_1_lattice3('#skF_4', C_50)) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_125])).
% 2.77/1.43  tff(c_151, plain, (![A_48, C_50]: (r1_lattices('#skF_4', '#skF_3'(A_48, '#skF_4', C_50), '#skF_5') | ~r3_lattice3('#skF_4', '#skF_3'(A_48, '#skF_4', C_50), '#skF_6') | ~r2_hidden(A_48, a_2_1_lattice3('#skF_4', C_50)) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_137])).
% 2.77/1.43  tff(c_169, plain, (![A_114, C_115]: (r1_lattices('#skF_4', '#skF_3'(A_114, '#skF_4', C_115), '#skF_5') | ~r3_lattice3('#skF_4', '#skF_3'(A_114, '#skF_4', C_115), '#skF_6') | ~r2_hidden(A_114, a_2_1_lattice3('#skF_4', C_115)))), inference(negUnitSimplification, [status(thm)], [c_44, c_151])).
% 2.77/1.43  tff(c_176, plain, (![A_48]: (r1_lattices('#skF_4', '#skF_3'(A_48, '#skF_4', '#skF_6'), '#skF_5') | ~r2_hidden(A_48, a_2_1_lattice3('#skF_4', '#skF_6')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_169])).
% 2.77/1.43  tff(c_181, plain, (![A_48]: (r1_lattices('#skF_4', '#skF_3'(A_48, '#skF_4', '#skF_6'), '#skF_5') | ~r2_hidden(A_48, a_2_1_lattice3('#skF_4', '#skF_6')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_176])).
% 2.77/1.43  tff(c_182, plain, (![A_48]: (r1_lattices('#skF_4', '#skF_3'(A_48, '#skF_4', '#skF_6'), '#skF_5') | ~r2_hidden(A_48, a_2_1_lattice3('#skF_4', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_44, c_181])).
% 2.77/1.43  tff(c_400, plain, (![A_150, B_151]: (r1_lattices('#skF_4', '#skF_2'(A_150, B_151, a_2_1_lattice3('#skF_4', '#skF_6')), '#skF_5') | ~r2_hidden('#skF_2'(A_150, B_151, a_2_1_lattice3('#skF_4', '#skF_6')), a_2_1_lattice3('#skF_4', '#skF_6')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4') | r4_lattice3(A_150, B_151, a_2_1_lattice3('#skF_4', '#skF_6')) | ~m1_subset_1(B_151, u1_struct_0(A_150)) | ~l3_lattices(A_150) | v2_struct_0(A_150))), inference(superposition, [status(thm), theory('equality')], [c_389, c_182])).
% 2.77/1.43  tff(c_419, plain, (![A_150, B_151]: (r1_lattices('#skF_4', '#skF_2'(A_150, B_151, a_2_1_lattice3('#skF_4', '#skF_6')), '#skF_5') | ~r2_hidden('#skF_2'(A_150, B_151, a_2_1_lattice3('#skF_4', '#skF_6')), a_2_1_lattice3('#skF_4', '#skF_6')) | v2_struct_0('#skF_4') | r4_lattice3(A_150, B_151, a_2_1_lattice3('#skF_4', '#skF_6')) | ~m1_subset_1(B_151, u1_struct_0(A_150)) | ~l3_lattices(A_150) | v2_struct_0(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_400])).
% 2.77/1.43  tff(c_457, plain, (![A_157, B_158]: (r1_lattices('#skF_4', '#skF_2'(A_157, B_158, a_2_1_lattice3('#skF_4', '#skF_6')), '#skF_5') | ~r2_hidden('#skF_2'(A_157, B_158, a_2_1_lattice3('#skF_4', '#skF_6')), a_2_1_lattice3('#skF_4', '#skF_6')) | r4_lattice3(A_157, B_158, a_2_1_lattice3('#skF_4', '#skF_6')) | ~m1_subset_1(B_158, u1_struct_0(A_157)) | ~l3_lattices(A_157) | v2_struct_0(A_157))), inference(negUnitSimplification, [status(thm)], [c_44, c_419])).
% 2.77/1.43  tff(c_470, plain, (![A_159, B_160]: (r1_lattices('#skF_4', '#skF_2'(A_159, B_160, a_2_1_lattice3('#skF_4', '#skF_6')), '#skF_5') | r4_lattice3(A_159, B_160, a_2_1_lattice3('#skF_4', '#skF_6')) | ~m1_subset_1(B_160, u1_struct_0(A_159)) | ~l3_lattices(A_159) | v2_struct_0(A_159))), inference(resolution, [status(thm)], [c_14, c_457])).
% 2.77/1.43  tff(c_12, plain, (![A_23, B_35, C_41]: (~r1_lattices(A_23, '#skF_2'(A_23, B_35, C_41), B_35) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.77/1.43  tff(c_474, plain, (r4_lattice3('#skF_4', '#skF_5', a_2_1_lattice3('#skF_4', '#skF_6')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_470, c_12])).
% 2.77/1.43  tff(c_477, plain, (r4_lattice3('#skF_4', '#skF_5', a_2_1_lattice3('#skF_4', '#skF_6')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_474])).
% 2.77/1.43  tff(c_478, plain, (r4_lattice3('#skF_4', '#skF_5', a_2_1_lattice3('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_44, c_477])).
% 2.77/1.43  tff(c_28, plain, (![A_54, C_60, B_58]: (k15_lattice3(A_54, C_60)=B_58 | ~r4_lattice3(A_54, B_58, C_60) | ~r2_hidden(B_58, C_60) | ~m1_subset_1(B_58, u1_struct_0(A_54)) | ~l3_lattices(A_54) | ~v4_lattice3(A_54) | ~v10_lattices(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.77/1.43  tff(c_480, plain, (k15_lattice3('#skF_4', a_2_1_lattice3('#skF_4', '#skF_6'))='#skF_5' | ~r2_hidden('#skF_5', a_2_1_lattice3('#skF_4', '#skF_6')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | ~v4_lattice3('#skF_4') | ~v10_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_478, c_28])).
% 2.77/1.43  tff(c_483, plain, (k15_lattice3('#skF_4', a_2_1_lattice3('#skF_4', '#skF_6'))='#skF_5' | ~r2_hidden('#skF_5', a_2_1_lattice3('#skF_4', '#skF_6')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_480])).
% 2.77/1.43  tff(c_484, plain, (k15_lattice3('#skF_4', a_2_1_lattice3('#skF_4', '#skF_6'))='#skF_5' | ~r2_hidden('#skF_5', a_2_1_lattice3('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_44, c_483])).
% 2.77/1.43  tff(c_485, plain, (~r2_hidden('#skF_5', a_2_1_lattice3('#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_484])).
% 2.77/1.43  tff(c_488, plain, (~r3_lattice3('#skF_4', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_20, c_485])).
% 2.77/1.43  tff(c_491, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32, c_488])).
% 2.77/1.43  tff(c_493, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_491])).
% 2.77/1.43  tff(c_494, plain, (k15_lattice3('#skF_4', a_2_1_lattice3('#skF_4', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_484])).
% 2.77/1.43  tff(c_18, plain, (![A_45, B_47]: (k15_lattice3(A_45, a_2_1_lattice3(A_45, B_47))=k16_lattice3(A_45, B_47) | ~l3_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.77/1.43  tff(c_534, plain, (k16_lattice3('#skF_4', '#skF_6')='#skF_5' | ~l3_lattices('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_494, c_18])).
% 2.77/1.43  tff(c_541, plain, (k16_lattice3('#skF_4', '#skF_6')='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_534])).
% 2.77/1.43  tff(c_543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_30, c_541])).
% 2.77/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.43  
% 2.77/1.43  Inference rules
% 2.77/1.43  ----------------------
% 2.77/1.43  #Ref     : 0
% 2.77/1.43  #Sup     : 94
% 2.77/1.43  #Fact    : 0
% 2.77/1.43  #Define  : 0
% 2.77/1.43  #Split   : 1
% 2.77/1.43  #Chain   : 0
% 2.77/1.43  #Close   : 0
% 2.77/1.43  
% 2.77/1.43  Ordering : KBO
% 2.77/1.43  
% 2.77/1.43  Simplification rules
% 2.77/1.43  ----------------------
% 2.77/1.43  #Subsume      : 6
% 2.77/1.43  #Demod        : 85
% 2.77/1.43  #Tautology    : 29
% 2.77/1.43  #SimpNegUnit  : 34
% 2.77/1.43  #BackRed      : 0
% 2.77/1.43  
% 2.77/1.43  #Partial instantiations: 0
% 2.77/1.43  #Strategies tried      : 1
% 2.77/1.43  
% 2.77/1.43  Timing (in seconds)
% 2.77/1.43  ----------------------
% 2.77/1.44  Preprocessing        : 0.32
% 2.77/1.44  Parsing              : 0.18
% 2.77/1.44  CNF conversion       : 0.03
% 2.77/1.44  Main loop            : 0.34
% 2.77/1.44  Inferencing          : 0.14
% 2.77/1.44  Reduction            : 0.09
% 2.77/1.44  Demodulation         : 0.06
% 2.77/1.44  BG Simplification    : 0.02
% 2.77/1.44  Subsumption          : 0.07
% 2.77/1.44  Abstraction          : 0.02
% 2.77/1.44  MUC search           : 0.00
% 2.77/1.44  Cooper               : 0.00
% 2.77/1.44  Total                : 0.70
% 2.77/1.44  Index Insertion      : 0.00
% 2.77/1.44  Index Deletion       : 0.00
% 2.77/1.44  Index Matching       : 0.00
% 2.77/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
