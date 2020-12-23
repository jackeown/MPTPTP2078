%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:48 EST 2020

% Result     : Theorem 6.25s
% Output     : CNFRefutation 6.58s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 158 expanded)
%              Number of leaves         :   29 (  72 expanded)
%              Depth                    :   24
%              Number of atoms          :  336 ( 707 expanded)
%              Number of equality atoms :   25 (  65 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(f_131,negated_conjecture,(
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

tff(f_111,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & l3_lattices(B) )
     => ( r2_hidden(A,a_2_1_lattice3(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & r3_lattice3(B,D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

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

tff(f_89,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] : k16_lattice3(A,B) = k15_lattice3(A,a_2_1_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattice3)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_38,plain,(
    k16_lattice3('#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_46,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_40,plain,(
    r3_lattice3('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_14,plain,(
    ! [A_23,B_35,C_41] :
      ( r2_hidden('#skF_2'(A_23,B_35,C_41),C_41)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_96,plain,(
    ! [A_87,B_88,C_89] :
      ( r2_hidden('#skF_2'(A_87,B_88,C_89),C_89)
      | r4_lattice3(A_87,B_88,C_89)
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | ~ l3_lattices(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [A_60,B_61,C_62] :
      ( '#skF_4'(A_60,B_61,C_62) = A_60
      | ~ r2_hidden(A_60,a_2_1_lattice3(B_61,C_62))
      | ~ l3_lattices(B_61)
      | v2_struct_0(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_415,plain,(
    ! [A_169,B_170,B_171,C_172] :
      ( '#skF_4'('#skF_2'(A_169,B_170,a_2_1_lattice3(B_171,C_172)),B_171,C_172) = '#skF_2'(A_169,B_170,a_2_1_lattice3(B_171,C_172))
      | ~ l3_lattices(B_171)
      | v2_struct_0(B_171)
      | r4_lattice3(A_169,B_170,a_2_1_lattice3(B_171,C_172))
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l3_lattices(A_169)
      | v2_struct_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_96,c_34])).

tff(c_32,plain,(
    ! [B_61,A_60,C_62] :
      ( r3_lattice3(B_61,'#skF_4'(A_60,B_61,C_62),C_62)
      | ~ r2_hidden(A_60,a_2_1_lattice3(B_61,C_62))
      | ~ l3_lattices(B_61)
      | v2_struct_0(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    ! [A_60,B_61,C_62] :
      ( m1_subset_1('#skF_4'(A_60,B_61,C_62),u1_struct_0(B_61))
      | ~ r2_hidden(A_60,a_2_1_lattice3(B_61,C_62))
      | ~ l3_lattices(B_61)
      | v2_struct_0(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_42,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_115,plain,(
    ! [A_107,B_108,D_109,C_110] :
      ( r1_lattices(A_107,B_108,D_109)
      | ~ r2_hidden(D_109,C_110)
      | ~ m1_subset_1(D_109,u1_struct_0(A_107))
      | ~ r3_lattice3(A_107,B_108,C_110)
      | ~ m1_subset_1(B_108,u1_struct_0(A_107))
      | ~ l3_lattices(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_128,plain,(
    ! [A_111,B_112] :
      ( r1_lattices(A_111,B_112,'#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0(A_111))
      | ~ r3_lattice3(A_111,B_112,'#skF_7')
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l3_lattices(A_111)
      | v2_struct_0(A_111) ) ),
    inference(resolution,[status(thm)],[c_42,c_115])).

tff(c_130,plain,(
    ! [B_112] :
      ( r1_lattices('#skF_5',B_112,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_112,'#skF_7')
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_128])).

tff(c_133,plain,(
    ! [B_112] :
      ( r1_lattices('#skF_5',B_112,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_112,'#skF_7')
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_130])).

tff(c_135,plain,(
    ! [B_113] :
      ( r1_lattices('#skF_5',B_113,'#skF_6')
      | ~ r3_lattice3('#skF_5',B_113,'#skF_7')
      | ~ m1_subset_1(B_113,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_133])).

tff(c_147,plain,(
    ! [A_60,C_62] :
      ( r1_lattices('#skF_5','#skF_4'(A_60,'#skF_5',C_62),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_60,'#skF_5',C_62),'#skF_7')
      | ~ r2_hidden(A_60,a_2_1_lattice3('#skF_5',C_62))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_135])).

tff(c_161,plain,(
    ! [A_60,C_62] :
      ( r1_lattices('#skF_5','#skF_4'(A_60,'#skF_5',C_62),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_60,'#skF_5',C_62),'#skF_7')
      | ~ r2_hidden(A_60,a_2_1_lattice3('#skF_5',C_62))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_147])).

tff(c_179,plain,(
    ! [A_118,C_119] :
      ( r1_lattices('#skF_5','#skF_4'(A_118,'#skF_5',C_119),'#skF_6')
      | ~ r3_lattice3('#skF_5','#skF_4'(A_118,'#skF_5',C_119),'#skF_7')
      | ~ r2_hidden(A_118,a_2_1_lattice3('#skF_5',C_119)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_161])).

tff(c_186,plain,(
    ! [A_60] :
      ( r1_lattices('#skF_5','#skF_4'(A_60,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_60,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_32,c_179])).

tff(c_191,plain,(
    ! [A_60] :
      ( r1_lattices('#skF_5','#skF_4'(A_60,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_60,a_2_1_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_186])).

tff(c_192,plain,(
    ! [A_60] :
      ( r1_lattices('#skF_5','#skF_4'(A_60,'#skF_5','#skF_7'),'#skF_6')
      | ~ r2_hidden(A_60,a_2_1_lattice3('#skF_5','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_191])).

tff(c_426,plain,(
    ! [A_169,B_170] :
      ( r1_lattices('#skF_5','#skF_2'(A_169,B_170,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_169,B_170,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_169,B_170,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l3_lattices(A_169)
      | v2_struct_0(A_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_192])).

tff(c_445,plain,(
    ! [A_169,B_170] :
      ( r1_lattices('#skF_5','#skF_2'(A_169,B_170,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_169,B_170,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | v2_struct_0('#skF_5')
      | r4_lattice3(A_169,B_170,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l3_lattices(A_169)
      | v2_struct_0(A_169) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_426])).

tff(c_515,plain,(
    ! [A_179,B_180] :
      ( r1_lattices('#skF_5','#skF_2'(A_179,B_180,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | ~ r2_hidden('#skF_2'(A_179,B_180,a_2_1_lattice3('#skF_5','#skF_7')),a_2_1_lattice3('#skF_5','#skF_7'))
      | r4_lattice3(A_179,B_180,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_180,u1_struct_0(A_179))
      | ~ l3_lattices(A_179)
      | v2_struct_0(A_179) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_445])).

tff(c_528,plain,(
    ! [A_181,B_182] :
      ( r1_lattices('#skF_5','#skF_2'(A_181,B_182,a_2_1_lattice3('#skF_5','#skF_7')),'#skF_6')
      | r4_lattice3(A_181,B_182,a_2_1_lattice3('#skF_5','#skF_7'))
      | ~ m1_subset_1(B_182,u1_struct_0(A_181))
      | ~ l3_lattices(A_181)
      | v2_struct_0(A_181) ) ),
    inference(resolution,[status(thm)],[c_14,c_515])).

tff(c_12,plain,(
    ! [A_23,B_35,C_41] :
      ( ~ r1_lattices(A_23,'#skF_2'(A_23,B_35,C_41),B_35)
      | r4_lattice3(A_23,B_35,C_41)
      | ~ m1_subset_1(B_35,u1_struct_0(A_23))
      | ~ l3_lattices(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_532,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_528,c_12])).

tff(c_535,plain,
    ( r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_532])).

tff(c_536,plain,(
    r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3('#skF_5','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_535])).

tff(c_50,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_48,plain,(
    v4_lattice3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_22,plain,(
    ! [A_45,B_52,C_53] :
      ( m1_subset_1('#skF_3'(A_45,B_52,C_53),u1_struct_0(A_45))
      | k15_lattice3(A_45,B_52) = C_53
      | ~ r4_lattice3(A_45,C_53,B_52)
      | ~ m1_subset_1(C_53,u1_struct_0(A_45))
      | ~ v4_lattice3(A_45)
      | ~ v10_lattices(A_45)
      | ~ l3_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_20,plain,(
    ! [A_45,B_52,C_53] :
      ( r4_lattice3(A_45,'#skF_3'(A_45,B_52,C_53),B_52)
      | k15_lattice3(A_45,B_52) = C_53
      | ~ r4_lattice3(A_45,C_53,B_52)
      | ~ m1_subset_1(C_53,u1_struct_0(A_45))
      | ~ v4_lattice3(A_45)
      | ~ v10_lattices(A_45)
      | ~ l3_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_30,plain,(
    ! [D_65,B_61,C_62] :
      ( r2_hidden(D_65,a_2_1_lattice3(B_61,C_62))
      | ~ r3_lattice3(B_61,D_65,C_62)
      | ~ m1_subset_1(D_65,u1_struct_0(B_61))
      | ~ l3_lattices(B_61)
      | v2_struct_0(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_166,plain,(
    ! [A_114,D_115,B_116,C_117] :
      ( r1_lattices(A_114,D_115,B_116)
      | ~ r2_hidden(D_115,C_117)
      | ~ m1_subset_1(D_115,u1_struct_0(A_114))
      | ~ r4_lattice3(A_114,B_116,C_117)
      | ~ m1_subset_1(B_116,u1_struct_0(A_114))
      | ~ l3_lattices(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_626,plain,(
    ! [B_192,B_194,A_193,D_195,C_191] :
      ( r1_lattices(A_193,D_195,B_194)
      | ~ m1_subset_1(D_195,u1_struct_0(A_193))
      | ~ r4_lattice3(A_193,B_194,a_2_1_lattice3(B_192,C_191))
      | ~ m1_subset_1(B_194,u1_struct_0(A_193))
      | ~ l3_lattices(A_193)
      | v2_struct_0(A_193)
      | ~ r3_lattice3(B_192,D_195,C_191)
      | ~ m1_subset_1(D_195,u1_struct_0(B_192))
      | ~ l3_lattices(B_192)
      | v2_struct_0(B_192) ) ),
    inference(resolution,[status(thm)],[c_30,c_166])).

tff(c_636,plain,(
    ! [B_194,B_192,C_191] :
      ( r1_lattices('#skF_5','#skF_6',B_194)
      | ~ r4_lattice3('#skF_5',B_194,a_2_1_lattice3(B_192,C_191))
      | ~ m1_subset_1(B_194,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_192,'#skF_6',C_191)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_192))
      | ~ l3_lattices(B_192)
      | v2_struct_0(B_192) ) ),
    inference(resolution,[status(thm)],[c_44,c_626])).

tff(c_643,plain,(
    ! [B_194,B_192,C_191] :
      ( r1_lattices('#skF_5','#skF_6',B_194)
      | ~ r4_lattice3('#skF_5',B_194,a_2_1_lattice3(B_192,C_191))
      | ~ m1_subset_1(B_194,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_192,'#skF_6',C_191)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_192))
      | ~ l3_lattices(B_192)
      | v2_struct_0(B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_636])).

tff(c_645,plain,(
    ! [B_196,B_197,C_198] :
      ( r1_lattices('#skF_5','#skF_6',B_196)
      | ~ r4_lattice3('#skF_5',B_196,a_2_1_lattice3(B_197,C_198))
      | ~ m1_subset_1(B_196,u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_197,'#skF_6',C_198)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_197))
      | ~ l3_lattices(B_197)
      | v2_struct_0(B_197) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_643])).

tff(c_660,plain,(
    ! [B_197,C_198,C_53] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_197,C_198),C_53))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3(B_197,C_198),C_53),u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_197,'#skF_6',C_198)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_197))
      | ~ l3_lattices(B_197)
      | v2_struct_0(B_197)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_197,C_198)) = C_53
      | ~ r4_lattice3('#skF_5',C_53,a_2_1_lattice3(B_197,C_198))
      | ~ m1_subset_1(C_53,u1_struct_0('#skF_5'))
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20,c_645])).

tff(c_675,plain,(
    ! [B_197,C_198,C_53] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_197,C_198),C_53))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3(B_197,C_198),C_53),u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_197,'#skF_6',C_198)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_197))
      | ~ l3_lattices(B_197)
      | v2_struct_0(B_197)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_197,C_198)) = C_53
      | ~ r4_lattice3('#skF_5',C_53,a_2_1_lattice3(B_197,C_198))
      | ~ m1_subset_1(C_53,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_48,c_660])).

tff(c_3159,plain,(
    ! [B_524,C_525,C_526] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_524,C_525),C_526))
      | ~ m1_subset_1('#skF_3'('#skF_5',a_2_1_lattice3(B_524,C_525),C_526),u1_struct_0('#skF_5'))
      | ~ r3_lattice3(B_524,'#skF_6',C_525)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_524))
      | ~ l3_lattices(B_524)
      | v2_struct_0(B_524)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_524,C_525)) = C_526
      | ~ r4_lattice3('#skF_5',C_526,a_2_1_lattice3(B_524,C_525))
      | ~ m1_subset_1(C_526,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_675])).

tff(c_3163,plain,(
    ! [B_524,C_525,C_53] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_524,C_525),C_53))
      | ~ r3_lattice3(B_524,'#skF_6',C_525)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_524))
      | ~ l3_lattices(B_524)
      | v2_struct_0(B_524)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_524,C_525)) = C_53
      | ~ r4_lattice3('#skF_5',C_53,a_2_1_lattice3(B_524,C_525))
      | ~ m1_subset_1(C_53,u1_struct_0('#skF_5'))
      | ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_3159])).

tff(c_3166,plain,(
    ! [B_524,C_525,C_53] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_524,C_525),C_53))
      | ~ r3_lattice3(B_524,'#skF_6',C_525)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_524))
      | ~ l3_lattices(B_524)
      | v2_struct_0(B_524)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_524,C_525)) = C_53
      | ~ r4_lattice3('#skF_5',C_53,a_2_1_lattice3(B_524,C_525))
      | ~ m1_subset_1(C_53,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_48,c_3163])).

tff(c_3168,plain,(
    ! [B_527,C_528,C_529] :
      ( r1_lattices('#skF_5','#skF_6','#skF_3'('#skF_5',a_2_1_lattice3(B_527,C_528),C_529))
      | ~ r3_lattice3(B_527,'#skF_6',C_528)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_527))
      | ~ l3_lattices(B_527)
      | v2_struct_0(B_527)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_527,C_528)) = C_529
      | ~ r4_lattice3('#skF_5',C_529,a_2_1_lattice3(B_527,C_528))
      | ~ m1_subset_1(C_529,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3166])).

tff(c_18,plain,(
    ! [A_45,C_53,B_52] :
      ( ~ r1_lattices(A_45,C_53,'#skF_3'(A_45,B_52,C_53))
      | k15_lattice3(A_45,B_52) = C_53
      | ~ r4_lattice3(A_45,C_53,B_52)
      | ~ m1_subset_1(C_53,u1_struct_0(A_45))
      | ~ v4_lattice3(A_45)
      | ~ v10_lattices(A_45)
      | ~ l3_lattices(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3172,plain,(
    ! [B_527,C_528] :
      ( ~ v4_lattice3('#skF_5')
      | ~ v10_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_527,'#skF_6',C_528)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_527))
      | ~ l3_lattices(B_527)
      | v2_struct_0(B_527)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_527,C_528)) = '#skF_6'
      | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3(B_527,C_528))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_3168,c_18])).

tff(c_3175,plain,(
    ! [B_527,C_528] :
      ( v2_struct_0('#skF_5')
      | ~ r3_lattice3(B_527,'#skF_6',C_528)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_527))
      | ~ l3_lattices(B_527)
      | v2_struct_0(B_527)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_527,C_528)) = '#skF_6'
      | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3(B_527,C_528)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_50,c_48,c_3172])).

tff(c_3177,plain,(
    ! [B_530,C_531] :
      ( ~ r3_lattice3(B_530,'#skF_6',C_531)
      | ~ m1_subset_1('#skF_6',u1_struct_0(B_530))
      | ~ l3_lattices(B_530)
      | v2_struct_0(B_530)
      | k15_lattice3('#skF_5',a_2_1_lattice3(B_530,C_531)) = '#skF_6'
      | ~ r4_lattice3('#skF_5','#skF_6',a_2_1_lattice3(B_530,C_531)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3175])).

tff(c_3180,plain,
    ( ~ r3_lattice3('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_536,c_3177])).

tff(c_3183,plain,
    ( v2_struct_0('#skF_5')
    | k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40,c_3180])).

tff(c_3184,plain,(
    k15_lattice3('#skF_5',a_2_1_lattice3('#skF_5','#skF_7')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3183])).

tff(c_28,plain,(
    ! [A_57,B_59] :
      ( k15_lattice3(A_57,a_2_1_lattice3(A_57,B_59)) = k16_lattice3(A_57,B_59)
      | ~ l3_lattices(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3207,plain,
    ( k16_lattice3('#skF_5','#skF_7') = '#skF_6'
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3184,c_28])).

tff(c_3234,plain,
    ( k16_lattice3('#skF_5','#skF_7') = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3207])).

tff(c_3236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38,c_3234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:41:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.25/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.25/2.27  
% 6.25/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.25/2.28  %$ r4_lattice3 > r3_lattice3 > r1_lattices > r2_hidden > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 6.25/2.28  
% 6.25/2.28  %Foreground sorts:
% 6.25/2.28  
% 6.25/2.28  
% 6.25/2.28  %Background operators:
% 6.25/2.28  
% 6.25/2.28  
% 6.25/2.28  %Foreground operators:
% 6.25/2.28  tff(l3_lattices, type, l3_lattices: $i > $o).
% 6.25/2.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.25/2.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.25/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.25/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.25/2.28  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 6.25/2.28  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 6.25/2.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.25/2.28  tff('#skF_7', type, '#skF_7': $i).
% 6.25/2.28  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 6.25/2.28  tff('#skF_5', type, '#skF_5': $i).
% 6.25/2.28  tff('#skF_6', type, '#skF_6': $i).
% 6.25/2.28  tff(a_2_1_lattice3, type, a_2_1_lattice3: ($i * $i) > $i).
% 6.25/2.28  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 6.25/2.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.25/2.28  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 6.25/2.28  tff(v10_lattices, type, v10_lattices: $i > $o).
% 6.25/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.25/2.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.25/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.25/2.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.25/2.28  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 6.25/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.25/2.28  
% 6.58/2.30  tff(f_131, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((r2_hidden(B, C) & r3_lattice3(A, B, C)) => (k16_lattice3(A, C) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_lattice3)).
% 6.58/2.30  tff(f_61, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r4_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, D, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_lattice3)).
% 6.58/2.30  tff(f_111, axiom, (![A, B, C]: ((~v2_struct_0(B) & l3_lattices(B)) => (r2_hidden(A, a_2_1_lattice3(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & r3_lattice3(B, D, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_lattice3)).
% 6.58/2.30  tff(f_43, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) => r1_lattices(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_lattice3)).
% 6.58/2.30  tff(f_89, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d21_lattice3)).
% 6.58/2.30  tff(f_97, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (k16_lattice3(A, B) = k15_lattice3(A, a_2_1_lattice3(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d22_lattice3)).
% 6.58/2.30  tff(c_52, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.58/2.30  tff(c_38, plain, (k16_lattice3('#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.58/2.30  tff(c_46, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.58/2.30  tff(c_44, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.58/2.30  tff(c_40, plain, (r3_lattice3('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.58/2.30  tff(c_14, plain, (![A_23, B_35, C_41]: (r2_hidden('#skF_2'(A_23, B_35, C_41), C_41) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.58/2.30  tff(c_96, plain, (![A_87, B_88, C_89]: (r2_hidden('#skF_2'(A_87, B_88, C_89), C_89) | r4_lattice3(A_87, B_88, C_89) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | ~l3_lattices(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.58/2.30  tff(c_34, plain, (![A_60, B_61, C_62]: ('#skF_4'(A_60, B_61, C_62)=A_60 | ~r2_hidden(A_60, a_2_1_lattice3(B_61, C_62)) | ~l3_lattices(B_61) | v2_struct_0(B_61))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.58/2.30  tff(c_415, plain, (![A_169, B_170, B_171, C_172]: ('#skF_4'('#skF_2'(A_169, B_170, a_2_1_lattice3(B_171, C_172)), B_171, C_172)='#skF_2'(A_169, B_170, a_2_1_lattice3(B_171, C_172)) | ~l3_lattices(B_171) | v2_struct_0(B_171) | r4_lattice3(A_169, B_170, a_2_1_lattice3(B_171, C_172)) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l3_lattices(A_169) | v2_struct_0(A_169))), inference(resolution, [status(thm)], [c_96, c_34])).
% 6.58/2.30  tff(c_32, plain, (![B_61, A_60, C_62]: (r3_lattice3(B_61, '#skF_4'(A_60, B_61, C_62), C_62) | ~r2_hidden(A_60, a_2_1_lattice3(B_61, C_62)) | ~l3_lattices(B_61) | v2_struct_0(B_61))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.58/2.30  tff(c_36, plain, (![A_60, B_61, C_62]: (m1_subset_1('#skF_4'(A_60, B_61, C_62), u1_struct_0(B_61)) | ~r2_hidden(A_60, a_2_1_lattice3(B_61, C_62)) | ~l3_lattices(B_61) | v2_struct_0(B_61))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.58/2.30  tff(c_42, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.58/2.30  tff(c_115, plain, (![A_107, B_108, D_109, C_110]: (r1_lattices(A_107, B_108, D_109) | ~r2_hidden(D_109, C_110) | ~m1_subset_1(D_109, u1_struct_0(A_107)) | ~r3_lattice3(A_107, B_108, C_110) | ~m1_subset_1(B_108, u1_struct_0(A_107)) | ~l3_lattices(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.58/2.30  tff(c_128, plain, (![A_111, B_112]: (r1_lattices(A_111, B_112, '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0(A_111)) | ~r3_lattice3(A_111, B_112, '#skF_7') | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l3_lattices(A_111) | v2_struct_0(A_111))), inference(resolution, [status(thm)], [c_42, c_115])).
% 6.58/2.30  tff(c_130, plain, (![B_112]: (r1_lattices('#skF_5', B_112, '#skF_6') | ~r3_lattice3('#skF_5', B_112, '#skF_7') | ~m1_subset_1(B_112, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_128])).
% 6.58/2.30  tff(c_133, plain, (![B_112]: (r1_lattices('#skF_5', B_112, '#skF_6') | ~r3_lattice3('#skF_5', B_112, '#skF_7') | ~m1_subset_1(B_112, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_130])).
% 6.58/2.30  tff(c_135, plain, (![B_113]: (r1_lattices('#skF_5', B_113, '#skF_6') | ~r3_lattice3('#skF_5', B_113, '#skF_7') | ~m1_subset_1(B_113, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_133])).
% 6.58/2.30  tff(c_147, plain, (![A_60, C_62]: (r1_lattices('#skF_5', '#skF_4'(A_60, '#skF_5', C_62), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_60, '#skF_5', C_62), '#skF_7') | ~r2_hidden(A_60, a_2_1_lattice3('#skF_5', C_62)) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_135])).
% 6.58/2.30  tff(c_161, plain, (![A_60, C_62]: (r1_lattices('#skF_5', '#skF_4'(A_60, '#skF_5', C_62), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_60, '#skF_5', C_62), '#skF_7') | ~r2_hidden(A_60, a_2_1_lattice3('#skF_5', C_62)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_147])).
% 6.58/2.30  tff(c_179, plain, (![A_118, C_119]: (r1_lattices('#skF_5', '#skF_4'(A_118, '#skF_5', C_119), '#skF_6') | ~r3_lattice3('#skF_5', '#skF_4'(A_118, '#skF_5', C_119), '#skF_7') | ~r2_hidden(A_118, a_2_1_lattice3('#skF_5', C_119)))), inference(negUnitSimplification, [status(thm)], [c_52, c_161])).
% 6.58/2.30  tff(c_186, plain, (![A_60]: (r1_lattices('#skF_5', '#skF_4'(A_60, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_60, a_2_1_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_179])).
% 6.58/2.30  tff(c_191, plain, (![A_60]: (r1_lattices('#skF_5', '#skF_4'(A_60, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_60, a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_186])).
% 6.58/2.30  tff(c_192, plain, (![A_60]: (r1_lattices('#skF_5', '#skF_4'(A_60, '#skF_5', '#skF_7'), '#skF_6') | ~r2_hidden(A_60, a_2_1_lattice3('#skF_5', '#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_52, c_191])).
% 6.58/2.30  tff(c_426, plain, (![A_169, B_170]: (r1_lattices('#skF_5', '#skF_2'(A_169, B_170, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_169, B_170, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | r4_lattice3(A_169, B_170, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l3_lattices(A_169) | v2_struct_0(A_169))), inference(superposition, [status(thm), theory('equality')], [c_415, c_192])).
% 6.58/2.30  tff(c_445, plain, (![A_169, B_170]: (r1_lattices('#skF_5', '#skF_2'(A_169, B_170, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_169, B_170, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5') | r4_lattice3(A_169, B_170, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l3_lattices(A_169) | v2_struct_0(A_169))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_426])).
% 6.58/2.30  tff(c_515, plain, (![A_179, B_180]: (r1_lattices('#skF_5', '#skF_2'(A_179, B_180, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | ~r2_hidden('#skF_2'(A_179, B_180, a_2_1_lattice3('#skF_5', '#skF_7')), a_2_1_lattice3('#skF_5', '#skF_7')) | r4_lattice3(A_179, B_180, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_180, u1_struct_0(A_179)) | ~l3_lattices(A_179) | v2_struct_0(A_179))), inference(negUnitSimplification, [status(thm)], [c_52, c_445])).
% 6.58/2.30  tff(c_528, plain, (![A_181, B_182]: (r1_lattices('#skF_5', '#skF_2'(A_181, B_182, a_2_1_lattice3('#skF_5', '#skF_7')), '#skF_6') | r4_lattice3(A_181, B_182, a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1(B_182, u1_struct_0(A_181)) | ~l3_lattices(A_181) | v2_struct_0(A_181))), inference(resolution, [status(thm)], [c_14, c_515])).
% 6.58/2.30  tff(c_12, plain, (![A_23, B_35, C_41]: (~r1_lattices(A_23, '#skF_2'(A_23, B_35, C_41), B_35) | r4_lattice3(A_23, B_35, C_41) | ~m1_subset_1(B_35, u1_struct_0(A_23)) | ~l3_lattices(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.58/2.30  tff(c_532, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_528, c_12])).
% 6.58/2.30  tff(c_535, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_532])).
% 6.58/2.30  tff(c_536, plain, (r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3('#skF_5', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_52, c_535])).
% 6.58/2.30  tff(c_50, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.58/2.30  tff(c_48, plain, (v4_lattice3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.58/2.30  tff(c_22, plain, (![A_45, B_52, C_53]: (m1_subset_1('#skF_3'(A_45, B_52, C_53), u1_struct_0(A_45)) | k15_lattice3(A_45, B_52)=C_53 | ~r4_lattice3(A_45, C_53, B_52) | ~m1_subset_1(C_53, u1_struct_0(A_45)) | ~v4_lattice3(A_45) | ~v10_lattices(A_45) | ~l3_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.58/2.30  tff(c_20, plain, (![A_45, B_52, C_53]: (r4_lattice3(A_45, '#skF_3'(A_45, B_52, C_53), B_52) | k15_lattice3(A_45, B_52)=C_53 | ~r4_lattice3(A_45, C_53, B_52) | ~m1_subset_1(C_53, u1_struct_0(A_45)) | ~v4_lattice3(A_45) | ~v10_lattices(A_45) | ~l3_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.58/2.30  tff(c_30, plain, (![D_65, B_61, C_62]: (r2_hidden(D_65, a_2_1_lattice3(B_61, C_62)) | ~r3_lattice3(B_61, D_65, C_62) | ~m1_subset_1(D_65, u1_struct_0(B_61)) | ~l3_lattices(B_61) | v2_struct_0(B_61))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.58/2.30  tff(c_166, plain, (![A_114, D_115, B_116, C_117]: (r1_lattices(A_114, D_115, B_116) | ~r2_hidden(D_115, C_117) | ~m1_subset_1(D_115, u1_struct_0(A_114)) | ~r4_lattice3(A_114, B_116, C_117) | ~m1_subset_1(B_116, u1_struct_0(A_114)) | ~l3_lattices(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.58/2.30  tff(c_626, plain, (![B_192, B_194, A_193, D_195, C_191]: (r1_lattices(A_193, D_195, B_194) | ~m1_subset_1(D_195, u1_struct_0(A_193)) | ~r4_lattice3(A_193, B_194, a_2_1_lattice3(B_192, C_191)) | ~m1_subset_1(B_194, u1_struct_0(A_193)) | ~l3_lattices(A_193) | v2_struct_0(A_193) | ~r3_lattice3(B_192, D_195, C_191) | ~m1_subset_1(D_195, u1_struct_0(B_192)) | ~l3_lattices(B_192) | v2_struct_0(B_192))), inference(resolution, [status(thm)], [c_30, c_166])).
% 6.58/2.30  tff(c_636, plain, (![B_194, B_192, C_191]: (r1_lattices('#skF_5', '#skF_6', B_194) | ~r4_lattice3('#skF_5', B_194, a_2_1_lattice3(B_192, C_191)) | ~m1_subset_1(B_194, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3(B_192, '#skF_6', C_191) | ~m1_subset_1('#skF_6', u1_struct_0(B_192)) | ~l3_lattices(B_192) | v2_struct_0(B_192))), inference(resolution, [status(thm)], [c_44, c_626])).
% 6.58/2.30  tff(c_643, plain, (![B_194, B_192, C_191]: (r1_lattices('#skF_5', '#skF_6', B_194) | ~r4_lattice3('#skF_5', B_194, a_2_1_lattice3(B_192, C_191)) | ~m1_subset_1(B_194, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5') | ~r3_lattice3(B_192, '#skF_6', C_191) | ~m1_subset_1('#skF_6', u1_struct_0(B_192)) | ~l3_lattices(B_192) | v2_struct_0(B_192))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_636])).
% 6.58/2.30  tff(c_645, plain, (![B_196, B_197, C_198]: (r1_lattices('#skF_5', '#skF_6', B_196) | ~r4_lattice3('#skF_5', B_196, a_2_1_lattice3(B_197, C_198)) | ~m1_subset_1(B_196, u1_struct_0('#skF_5')) | ~r3_lattice3(B_197, '#skF_6', C_198) | ~m1_subset_1('#skF_6', u1_struct_0(B_197)) | ~l3_lattices(B_197) | v2_struct_0(B_197))), inference(negUnitSimplification, [status(thm)], [c_52, c_643])).
% 6.58/2.30  tff(c_660, plain, (![B_197, C_198, C_53]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_197, C_198), C_53)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3(B_197, C_198), C_53), u1_struct_0('#skF_5')) | ~r3_lattice3(B_197, '#skF_6', C_198) | ~m1_subset_1('#skF_6', u1_struct_0(B_197)) | ~l3_lattices(B_197) | v2_struct_0(B_197) | k15_lattice3('#skF_5', a_2_1_lattice3(B_197, C_198))=C_53 | ~r4_lattice3('#skF_5', C_53, a_2_1_lattice3(B_197, C_198)) | ~m1_subset_1(C_53, u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_20, c_645])).
% 6.58/2.30  tff(c_675, plain, (![B_197, C_198, C_53]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_197, C_198), C_53)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3(B_197, C_198), C_53), u1_struct_0('#skF_5')) | ~r3_lattice3(B_197, '#skF_6', C_198) | ~m1_subset_1('#skF_6', u1_struct_0(B_197)) | ~l3_lattices(B_197) | v2_struct_0(B_197) | k15_lattice3('#skF_5', a_2_1_lattice3(B_197, C_198))=C_53 | ~r4_lattice3('#skF_5', C_53, a_2_1_lattice3(B_197, C_198)) | ~m1_subset_1(C_53, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_48, c_660])).
% 6.58/2.30  tff(c_3159, plain, (![B_524, C_525, C_526]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_524, C_525), C_526)) | ~m1_subset_1('#skF_3'('#skF_5', a_2_1_lattice3(B_524, C_525), C_526), u1_struct_0('#skF_5')) | ~r3_lattice3(B_524, '#skF_6', C_525) | ~m1_subset_1('#skF_6', u1_struct_0(B_524)) | ~l3_lattices(B_524) | v2_struct_0(B_524) | k15_lattice3('#skF_5', a_2_1_lattice3(B_524, C_525))=C_526 | ~r4_lattice3('#skF_5', C_526, a_2_1_lattice3(B_524, C_525)) | ~m1_subset_1(C_526, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_675])).
% 6.58/2.30  tff(c_3163, plain, (![B_524, C_525, C_53]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_524, C_525), C_53)) | ~r3_lattice3(B_524, '#skF_6', C_525) | ~m1_subset_1('#skF_6', u1_struct_0(B_524)) | ~l3_lattices(B_524) | v2_struct_0(B_524) | k15_lattice3('#skF_5', a_2_1_lattice3(B_524, C_525))=C_53 | ~r4_lattice3('#skF_5', C_53, a_2_1_lattice3(B_524, C_525)) | ~m1_subset_1(C_53, u1_struct_0('#skF_5')) | ~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_22, c_3159])).
% 6.58/2.30  tff(c_3166, plain, (![B_524, C_525, C_53]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_524, C_525), C_53)) | ~r3_lattice3(B_524, '#skF_6', C_525) | ~m1_subset_1('#skF_6', u1_struct_0(B_524)) | ~l3_lattices(B_524) | v2_struct_0(B_524) | k15_lattice3('#skF_5', a_2_1_lattice3(B_524, C_525))=C_53 | ~r4_lattice3('#skF_5', C_53, a_2_1_lattice3(B_524, C_525)) | ~m1_subset_1(C_53, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_48, c_3163])).
% 6.58/2.30  tff(c_3168, plain, (![B_527, C_528, C_529]: (r1_lattices('#skF_5', '#skF_6', '#skF_3'('#skF_5', a_2_1_lattice3(B_527, C_528), C_529)) | ~r3_lattice3(B_527, '#skF_6', C_528) | ~m1_subset_1('#skF_6', u1_struct_0(B_527)) | ~l3_lattices(B_527) | v2_struct_0(B_527) | k15_lattice3('#skF_5', a_2_1_lattice3(B_527, C_528))=C_529 | ~r4_lattice3('#skF_5', C_529, a_2_1_lattice3(B_527, C_528)) | ~m1_subset_1(C_529, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_52, c_3166])).
% 6.58/2.30  tff(c_18, plain, (![A_45, C_53, B_52]: (~r1_lattices(A_45, C_53, '#skF_3'(A_45, B_52, C_53)) | k15_lattice3(A_45, B_52)=C_53 | ~r4_lattice3(A_45, C_53, B_52) | ~m1_subset_1(C_53, u1_struct_0(A_45)) | ~v4_lattice3(A_45) | ~v10_lattices(A_45) | ~l3_lattices(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.58/2.30  tff(c_3172, plain, (![B_527, C_528]: (~v4_lattice3('#skF_5') | ~v10_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | ~r3_lattice3(B_527, '#skF_6', C_528) | ~m1_subset_1('#skF_6', u1_struct_0(B_527)) | ~l3_lattices(B_527) | v2_struct_0(B_527) | k15_lattice3('#skF_5', a_2_1_lattice3(B_527, C_528))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3(B_527, C_528)) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_3168, c_18])).
% 6.58/2.30  tff(c_3175, plain, (![B_527, C_528]: (v2_struct_0('#skF_5') | ~r3_lattice3(B_527, '#skF_6', C_528) | ~m1_subset_1('#skF_6', u1_struct_0(B_527)) | ~l3_lattices(B_527) | v2_struct_0(B_527) | k15_lattice3('#skF_5', a_2_1_lattice3(B_527, C_528))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3(B_527, C_528)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_50, c_48, c_3172])).
% 6.58/2.30  tff(c_3177, plain, (![B_530, C_531]: (~r3_lattice3(B_530, '#skF_6', C_531) | ~m1_subset_1('#skF_6', u1_struct_0(B_530)) | ~l3_lattices(B_530) | v2_struct_0(B_530) | k15_lattice3('#skF_5', a_2_1_lattice3(B_530, C_531))='#skF_6' | ~r4_lattice3('#skF_5', '#skF_6', a_2_1_lattice3(B_530, C_531)))), inference(negUnitSimplification, [status(thm)], [c_52, c_3175])).
% 6.58/2.30  tff(c_3180, plain, (~r3_lattice3('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5') | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_536, c_3177])).
% 6.58/2.30  tff(c_3183, plain, (v2_struct_0('#skF_5') | k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40, c_3180])).
% 6.58/2.30  tff(c_3184, plain, (k15_lattice3('#skF_5', a_2_1_lattice3('#skF_5', '#skF_7'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_52, c_3183])).
% 6.58/2.30  tff(c_28, plain, (![A_57, B_59]: (k15_lattice3(A_57, a_2_1_lattice3(A_57, B_59))=k16_lattice3(A_57, B_59) | ~l3_lattices(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.58/2.30  tff(c_3207, plain, (k16_lattice3('#skF_5', '#skF_7')='#skF_6' | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3184, c_28])).
% 6.58/2.30  tff(c_3234, plain, (k16_lattice3('#skF_5', '#skF_7')='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3207])).
% 6.58/2.30  tff(c_3236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_38, c_3234])).
% 6.58/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.58/2.30  
% 6.58/2.30  Inference rules
% 6.58/2.30  ----------------------
% 6.58/2.30  #Ref     : 0
% 6.58/2.30  #Sup     : 600
% 6.58/2.30  #Fact    : 0
% 6.58/2.30  #Define  : 0
% 6.58/2.30  #Split   : 4
% 6.58/2.30  #Chain   : 0
% 6.58/2.30  #Close   : 0
% 6.58/2.30  
% 6.58/2.30  Ordering : KBO
% 6.58/2.30  
% 6.58/2.30  Simplification rules
% 6.58/2.30  ----------------------
% 6.58/2.30  #Subsume      : 132
% 6.58/2.30  #Demod        : 599
% 6.58/2.30  #Tautology    : 105
% 6.58/2.30  #SimpNegUnit  : 243
% 6.58/2.30  #BackRed      : 0
% 6.58/2.30  
% 6.58/2.30  #Partial instantiations: 0
% 6.58/2.30  #Strategies tried      : 1
% 6.58/2.30  
% 6.58/2.30  Timing (in seconds)
% 6.58/2.30  ----------------------
% 6.58/2.31  Preprocessing        : 0.32
% 6.58/2.31  Parsing              : 0.18
% 6.58/2.31  CNF conversion       : 0.03
% 6.58/2.31  Main loop            : 1.19
% 6.58/2.31  Inferencing          : 0.47
% 6.58/2.31  Reduction            : 0.34
% 6.58/2.31  Demodulation         : 0.23
% 6.58/2.31  BG Simplification    : 0.05
% 6.58/2.31  Subsumption          : 0.26
% 6.58/2.31  Abstraction          : 0.06
% 6.58/2.31  MUC search           : 0.00
% 6.58/2.31  Cooper               : 0.00
% 6.58/2.31  Total                : 1.55
% 6.58/2.31  Index Insertion      : 0.00
% 6.58/2.31  Index Deletion       : 0.00
% 6.58/2.31  Index Matching       : 0.00
% 6.58/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
