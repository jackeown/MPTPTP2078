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
% DateTime   : Thu Dec  3 10:24:46 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   63 (  93 expanded)
%              Number of leaves         :   29 (  49 expanded)
%              Depth                    :   20
%              Number of atoms          :  168 ( 334 expanded)
%              Number of equality atoms :   18 (  20 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k16_lattice3,type,(
    k16_lattice3: ( $i * $i ) > $i )).

tff(k15_lattice3,type,(
    k15_lattice3: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(a_2_1_lattice3,type,(
    a_2_1_lattice3: ( $i * $i ) > $i )).

tff(r4_lattice3,type,(
    r4_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_lattice3,type,(
    v4_lattice3: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(r3_lattice3,type,(
    r3_lattice3: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
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

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v4_lattice3(A)
      <=> ! [B] :
          ? [C] :
            ( m1_subset_1(C,u1_struct_0(A))
            & r4_lattice3(A,C,B)
            & ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r4_lattice3(A,D,B)
                 => r1_lattices(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattice3)).

tff(f_73,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ! [B] : k16_lattice3(A,B) = k15_lattice3(A,a_2_1_lattice3(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattice3)).

tff(f_105,axiom,(
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

tff(c_40,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_38,plain,(
    r3_lattice3('#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_46,plain,(
    v10_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_44,plain,(
    v4_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_42,plain,(
    l3_lattices('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_12,plain,(
    ! [A_1,B_16] :
      ( m1_subset_1('#skF_1'(A_1,B_16),u1_struct_0(A_1))
      | ~ v4_lattice3(A_1)
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_1,B_16] :
      ( r4_lattice3(A_1,'#skF_1'(A_1,B_16),B_16)
      | ~ v4_lattice3(A_1)
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_27,B_34,C_35] :
      ( m1_subset_1('#skF_4'(A_27,B_34,C_35),u1_struct_0(A_27))
      | k15_lattice3(A_27,B_34) = C_35
      | ~ r4_lattice3(A_27,C_35,B_34)
      | ~ m1_subset_1(C_35,u1_struct_0(A_27))
      | ~ v4_lattice3(A_27)
      | ~ v10_lattices(A_27)
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [A_27,B_34,C_35] :
      ( r4_lattice3(A_27,'#skF_4'(A_27,B_34,C_35),B_34)
      | k15_lattice3(A_27,B_34) = C_35
      | ~ r4_lattice3(A_27,C_35,B_34)
      | ~ m1_subset_1(C_35,u1_struct_0(A_27))
      | ~ v4_lattice3(A_27)
      | ~ v10_lattices(A_27)
      | ~ l3_lattices(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_1,B_16,D_21] :
      ( r1_lattices(A_1,'#skF_1'(A_1,B_16),D_21)
      | ~ r4_lattice3(A_1,D_21,B_16)
      | ~ m1_subset_1(D_21,u1_struct_0(A_1))
      | ~ v4_lattice3(A_1)
      | ~ l3_lattices(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    ! [A_99,C_100,B_101] :
      ( ~ r1_lattices(A_99,C_100,'#skF_4'(A_99,B_101,C_100))
      | k15_lattice3(A_99,B_101) = C_100
      | ~ r4_lattice3(A_99,C_100,B_101)
      | ~ m1_subset_1(C_100,u1_struct_0(A_99))
      | ~ v4_lattice3(A_99)
      | ~ v10_lattices(A_99)
      | ~ l3_lattices(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_126,plain,(
    ! [A_127,B_128,B_129] :
      ( k15_lattice3(A_127,B_128) = '#skF_1'(A_127,B_129)
      | ~ r4_lattice3(A_127,'#skF_1'(A_127,B_129),B_128)
      | ~ m1_subset_1('#skF_1'(A_127,B_129),u1_struct_0(A_127))
      | ~ v10_lattices(A_127)
      | ~ r4_lattice3(A_127,'#skF_4'(A_127,B_128,'#skF_1'(A_127,B_129)),B_129)
      | ~ m1_subset_1('#skF_4'(A_127,B_128,'#skF_1'(A_127,B_129)),u1_struct_0(A_127))
      | ~ v4_lattice3(A_127)
      | ~ l3_lattices(A_127)
      | v2_struct_0(A_127) ) ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_131,plain,(
    ! [A_130,B_131] :
      ( ~ m1_subset_1('#skF_4'(A_130,B_131,'#skF_1'(A_130,B_131)),u1_struct_0(A_130))
      | k15_lattice3(A_130,B_131) = '#skF_1'(A_130,B_131)
      | ~ r4_lattice3(A_130,'#skF_1'(A_130,B_131),B_131)
      | ~ m1_subset_1('#skF_1'(A_130,B_131),u1_struct_0(A_130))
      | ~ v4_lattice3(A_130)
      | ~ v10_lattices(A_130)
      | ~ l3_lattices(A_130)
      | v2_struct_0(A_130) ) ),
    inference(resolution,[status(thm)],[c_16,c_126])).

tff(c_137,plain,(
    ! [A_132,B_133] :
      ( k15_lattice3(A_132,B_133) = '#skF_1'(A_132,B_133)
      | ~ r4_lattice3(A_132,'#skF_1'(A_132,B_133),B_133)
      | ~ m1_subset_1('#skF_1'(A_132,B_133),u1_struct_0(A_132))
      | ~ v4_lattice3(A_132)
      | ~ v10_lattices(A_132)
      | ~ l3_lattices(A_132)
      | v2_struct_0(A_132) ) ),
    inference(resolution,[status(thm)],[c_18,c_131])).

tff(c_141,plain,(
    ! [A_134,B_135] :
      ( k15_lattice3(A_134,B_135) = '#skF_1'(A_134,B_135)
      | ~ m1_subset_1('#skF_1'(A_134,B_135),u1_struct_0(A_134))
      | ~ v10_lattices(A_134)
      | ~ v4_lattice3(A_134)
      | ~ l3_lattices(A_134)
      | v2_struct_0(A_134) ) ),
    inference(resolution,[status(thm)],[c_10,c_137])).

tff(c_156,plain,(
    ! [A_139,B_140] :
      ( k15_lattice3(A_139,B_140) = '#skF_1'(A_139,B_140)
      | ~ v10_lattices(A_139)
      | ~ v4_lattice3(A_139)
      | ~ l3_lattices(A_139)
      | v2_struct_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_12,c_141])).

tff(c_158,plain,(
    ! [B_140] :
      ( k15_lattice3('#skF_6',B_140) = '#skF_1'('#skF_6',B_140)
      | ~ v10_lattices('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_44,c_156])).

tff(c_161,plain,(
    ! [B_140] :
      ( k15_lattice3('#skF_6',B_140) = '#skF_1'('#skF_6',B_140)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_158])).

tff(c_163,plain,(
    ! [B_141] : k15_lattice3('#skF_6',B_141) = '#skF_1'('#skF_6',B_141) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_161])).

tff(c_24,plain,(
    ! [A_39,B_41] :
      ( k15_lattice3(A_39,a_2_1_lattice3(A_39,B_41)) = k16_lattice3(A_39,B_41)
      | ~ l3_lattices(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_190,plain,(
    ! [B_41] :
      ( '#skF_1'('#skF_6',a_2_1_lattice3('#skF_6',B_41)) = k16_lattice3('#skF_6',B_41)
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_24])).

tff(c_218,plain,(
    ! [B_41] :
      ( '#skF_1'('#skF_6',a_2_1_lattice3('#skF_6',B_41)) = k16_lattice3('#skF_6',B_41)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_190])).

tff(c_224,plain,(
    ! [B_142] : '#skF_1'('#skF_6',a_2_1_lattice3('#skF_6',B_142)) = k16_lattice3('#skF_6',B_142) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_218])).

tff(c_238,plain,(
    ! [B_142] :
      ( m1_subset_1(k16_lattice3('#skF_6',B_142),u1_struct_0('#skF_6'))
      | ~ v4_lattice3('#skF_6')
      | ~ l3_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_12])).

tff(c_256,plain,(
    ! [B_142] :
      ( m1_subset_1(k16_lattice3('#skF_6',B_142),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_238])).

tff(c_262,plain,(
    ! [B_143] : m1_subset_1(k16_lattice3('#skF_6',B_143),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_256])).

tff(c_26,plain,(
    ! [A_42,D_63,C_60] :
      ( r3_lattices(A_42,D_63,k16_lattice3(A_42,C_60))
      | ~ r3_lattice3(A_42,D_63,C_60)
      | ~ m1_subset_1(D_63,u1_struct_0(A_42))
      | ~ m1_subset_1(k16_lattice3(A_42,C_60),u1_struct_0(A_42))
      | ~ l3_lattices(A_42)
      | ~ v4_lattice3(A_42)
      | ~ v10_lattices(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_264,plain,(
    ! [D_63,B_143] :
      ( r3_lattices('#skF_6',D_63,k16_lattice3('#skF_6',B_143))
      | ~ r3_lattice3('#skF_6',D_63,B_143)
      | ~ m1_subset_1(D_63,u1_struct_0('#skF_6'))
      | ~ l3_lattices('#skF_6')
      | ~ v4_lattice3('#skF_6')
      | ~ v10_lattices('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_262,c_26])).

tff(c_269,plain,(
    ! [D_63,B_143] :
      ( r3_lattices('#skF_6',D_63,k16_lattice3('#skF_6',B_143))
      | ~ r3_lattice3('#skF_6',D_63,B_143)
      | ~ m1_subset_1(D_63,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_264])).

tff(c_318,plain,(
    ! [D_152,B_153] :
      ( r3_lattices('#skF_6',D_152,k16_lattice3('#skF_6',B_153))
      | ~ r3_lattice3('#skF_6',D_152,B_153)
      | ~ m1_subset_1(D_152,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_269])).

tff(c_36,plain,(
    ~ r3_lattices('#skF_6','#skF_7',k16_lattice3('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_325,plain,
    ( ~ r3_lattice3('#skF_6','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_318,c_36])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_325])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.47  
% 2.59/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.48  %$ r4_lattice3 > r3_lattices > r3_lattice3 > r1_lattices > m1_subset_1 > v4_lattice3 > v2_struct_0 > v10_lattices > l3_lattices > k16_lattice3 > k15_lattice3 > a_2_1_lattice3 > #nlpp > u1_struct_0 > #skF_2 > #skF_4 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_1
% 2.59/1.48  
% 2.59/1.48  %Foreground sorts:
% 2.59/1.48  
% 2.59/1.48  
% 2.59/1.48  %Background operators:
% 2.59/1.48  
% 2.59/1.48  
% 2.59/1.48  %Foreground operators:
% 2.59/1.48  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.59/1.48  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.59/1.48  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.59/1.48  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 2.59/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.48  tff(k16_lattice3, type, k16_lattice3: ($i * $i) > $i).
% 2.59/1.48  tff(k15_lattice3, type, k15_lattice3: ($i * $i) > $i).
% 2.59/1.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.59/1.48  tff('#skF_7', type, '#skF_7': $i).
% 2.59/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.59/1.48  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.59/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.59/1.48  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.59/1.48  tff(a_2_1_lattice3, type, a_2_1_lattice3: ($i * $i) > $i).
% 2.59/1.48  tff(r4_lattice3, type, r4_lattice3: ($i * $i * $i) > $o).
% 2.59/1.48  tff(v4_lattice3, type, v4_lattice3: $i > $o).
% 2.59/1.48  tff(v10_lattices, type, v10_lattices: $i > $o).
% 2.59/1.48  tff('#skF_8', type, '#skF_8': $i).
% 2.59/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.59/1.48  tff(r3_lattice3, type, r3_lattice3: ($i * $i * $i) > $o).
% 2.59/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.48  
% 2.71/1.49  tff(f_123, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (r3_lattice3(A, B, C) => r3_lattices(A, B, k16_lattice3(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_lattice3)).
% 2.71/1.49  tff(f_45, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v4_lattice3(A) <=> (![B]: (?[C]: ((m1_subset_1(C, u1_struct_0(A)) & r4_lattice3(A, C, B)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_lattice3)).
% 2.71/1.49  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k15_lattice3(A, B)) <=> (r4_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r4_lattice3(A, D, B) => r1_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d21_lattice3)).
% 2.71/1.49  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (![B]: (k16_lattice3(A, B) = k15_lattice3(A, a_2_1_lattice3(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d22_lattice3)).
% 2.71/1.49  tff(f_105, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v4_lattice3(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((B = k16_lattice3(A, C)) <=> (r3_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_lattice3(A, D, C) => r3_lattices(A, D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_lattice3)).
% 2.71/1.49  tff(c_40, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.71/1.49  tff(c_38, plain, (r3_lattice3('#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.71/1.49  tff(c_48, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.71/1.49  tff(c_46, plain, (v10_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.71/1.49  tff(c_44, plain, (v4_lattice3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.71/1.49  tff(c_42, plain, (l3_lattices('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.71/1.49  tff(c_12, plain, (![A_1, B_16]: (m1_subset_1('#skF_1'(A_1, B_16), u1_struct_0(A_1)) | ~v4_lattice3(A_1) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.71/1.49  tff(c_10, plain, (![A_1, B_16]: (r4_lattice3(A_1, '#skF_1'(A_1, B_16), B_16) | ~v4_lattice3(A_1) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.71/1.49  tff(c_18, plain, (![A_27, B_34, C_35]: (m1_subset_1('#skF_4'(A_27, B_34, C_35), u1_struct_0(A_27)) | k15_lattice3(A_27, B_34)=C_35 | ~r4_lattice3(A_27, C_35, B_34) | ~m1_subset_1(C_35, u1_struct_0(A_27)) | ~v4_lattice3(A_27) | ~v10_lattices(A_27) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.71/1.49  tff(c_16, plain, (![A_27, B_34, C_35]: (r4_lattice3(A_27, '#skF_4'(A_27, B_34, C_35), B_34) | k15_lattice3(A_27, B_34)=C_35 | ~r4_lattice3(A_27, C_35, B_34) | ~m1_subset_1(C_35, u1_struct_0(A_27)) | ~v4_lattice3(A_27) | ~v10_lattices(A_27) | ~l3_lattices(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.71/1.49  tff(c_8, plain, (![A_1, B_16, D_21]: (r1_lattices(A_1, '#skF_1'(A_1, B_16), D_21) | ~r4_lattice3(A_1, D_21, B_16) | ~m1_subset_1(D_21, u1_struct_0(A_1)) | ~v4_lattice3(A_1) | ~l3_lattices(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.71/1.49  tff(c_76, plain, (![A_99, C_100, B_101]: (~r1_lattices(A_99, C_100, '#skF_4'(A_99, B_101, C_100)) | k15_lattice3(A_99, B_101)=C_100 | ~r4_lattice3(A_99, C_100, B_101) | ~m1_subset_1(C_100, u1_struct_0(A_99)) | ~v4_lattice3(A_99) | ~v10_lattices(A_99) | ~l3_lattices(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.71/1.49  tff(c_126, plain, (![A_127, B_128, B_129]: (k15_lattice3(A_127, B_128)='#skF_1'(A_127, B_129) | ~r4_lattice3(A_127, '#skF_1'(A_127, B_129), B_128) | ~m1_subset_1('#skF_1'(A_127, B_129), u1_struct_0(A_127)) | ~v10_lattices(A_127) | ~r4_lattice3(A_127, '#skF_4'(A_127, B_128, '#skF_1'(A_127, B_129)), B_129) | ~m1_subset_1('#skF_4'(A_127, B_128, '#skF_1'(A_127, B_129)), u1_struct_0(A_127)) | ~v4_lattice3(A_127) | ~l3_lattices(A_127) | v2_struct_0(A_127))), inference(resolution, [status(thm)], [c_8, c_76])).
% 2.71/1.49  tff(c_131, plain, (![A_130, B_131]: (~m1_subset_1('#skF_4'(A_130, B_131, '#skF_1'(A_130, B_131)), u1_struct_0(A_130)) | k15_lattice3(A_130, B_131)='#skF_1'(A_130, B_131) | ~r4_lattice3(A_130, '#skF_1'(A_130, B_131), B_131) | ~m1_subset_1('#skF_1'(A_130, B_131), u1_struct_0(A_130)) | ~v4_lattice3(A_130) | ~v10_lattices(A_130) | ~l3_lattices(A_130) | v2_struct_0(A_130))), inference(resolution, [status(thm)], [c_16, c_126])).
% 2.71/1.49  tff(c_137, plain, (![A_132, B_133]: (k15_lattice3(A_132, B_133)='#skF_1'(A_132, B_133) | ~r4_lattice3(A_132, '#skF_1'(A_132, B_133), B_133) | ~m1_subset_1('#skF_1'(A_132, B_133), u1_struct_0(A_132)) | ~v4_lattice3(A_132) | ~v10_lattices(A_132) | ~l3_lattices(A_132) | v2_struct_0(A_132))), inference(resolution, [status(thm)], [c_18, c_131])).
% 2.71/1.49  tff(c_141, plain, (![A_134, B_135]: (k15_lattice3(A_134, B_135)='#skF_1'(A_134, B_135) | ~m1_subset_1('#skF_1'(A_134, B_135), u1_struct_0(A_134)) | ~v10_lattices(A_134) | ~v4_lattice3(A_134) | ~l3_lattices(A_134) | v2_struct_0(A_134))), inference(resolution, [status(thm)], [c_10, c_137])).
% 2.71/1.49  tff(c_156, plain, (![A_139, B_140]: (k15_lattice3(A_139, B_140)='#skF_1'(A_139, B_140) | ~v10_lattices(A_139) | ~v4_lattice3(A_139) | ~l3_lattices(A_139) | v2_struct_0(A_139))), inference(resolution, [status(thm)], [c_12, c_141])).
% 2.71/1.49  tff(c_158, plain, (![B_140]: (k15_lattice3('#skF_6', B_140)='#skF_1'('#skF_6', B_140) | ~v10_lattices('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_44, c_156])).
% 2.71/1.49  tff(c_161, plain, (![B_140]: (k15_lattice3('#skF_6', B_140)='#skF_1'('#skF_6', B_140) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_158])).
% 2.71/1.49  tff(c_163, plain, (![B_141]: (k15_lattice3('#skF_6', B_141)='#skF_1'('#skF_6', B_141))), inference(negUnitSimplification, [status(thm)], [c_48, c_161])).
% 2.71/1.49  tff(c_24, plain, (![A_39, B_41]: (k15_lattice3(A_39, a_2_1_lattice3(A_39, B_41))=k16_lattice3(A_39, B_41) | ~l3_lattices(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.71/1.49  tff(c_190, plain, (![B_41]: ('#skF_1'('#skF_6', a_2_1_lattice3('#skF_6', B_41))=k16_lattice3('#skF_6', B_41) | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_163, c_24])).
% 2.71/1.49  tff(c_218, plain, (![B_41]: ('#skF_1'('#skF_6', a_2_1_lattice3('#skF_6', B_41))=k16_lattice3('#skF_6', B_41) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_190])).
% 2.71/1.49  tff(c_224, plain, (![B_142]: ('#skF_1'('#skF_6', a_2_1_lattice3('#skF_6', B_142))=k16_lattice3('#skF_6', B_142))), inference(negUnitSimplification, [status(thm)], [c_48, c_218])).
% 2.71/1.49  tff(c_238, plain, (![B_142]: (m1_subset_1(k16_lattice3('#skF_6', B_142), u1_struct_0('#skF_6')) | ~v4_lattice3('#skF_6') | ~l3_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_224, c_12])).
% 2.71/1.49  tff(c_256, plain, (![B_142]: (m1_subset_1(k16_lattice3('#skF_6', B_142), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_238])).
% 2.71/1.49  tff(c_262, plain, (![B_143]: (m1_subset_1(k16_lattice3('#skF_6', B_143), u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_48, c_256])).
% 2.71/1.49  tff(c_26, plain, (![A_42, D_63, C_60]: (r3_lattices(A_42, D_63, k16_lattice3(A_42, C_60)) | ~r3_lattice3(A_42, D_63, C_60) | ~m1_subset_1(D_63, u1_struct_0(A_42)) | ~m1_subset_1(k16_lattice3(A_42, C_60), u1_struct_0(A_42)) | ~l3_lattices(A_42) | ~v4_lattice3(A_42) | ~v10_lattices(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.71/1.49  tff(c_264, plain, (![D_63, B_143]: (r3_lattices('#skF_6', D_63, k16_lattice3('#skF_6', B_143)) | ~r3_lattice3('#skF_6', D_63, B_143) | ~m1_subset_1(D_63, u1_struct_0('#skF_6')) | ~l3_lattices('#skF_6') | ~v4_lattice3('#skF_6') | ~v10_lattices('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_262, c_26])).
% 2.71/1.49  tff(c_269, plain, (![D_63, B_143]: (r3_lattices('#skF_6', D_63, k16_lattice3('#skF_6', B_143)) | ~r3_lattice3('#skF_6', D_63, B_143) | ~m1_subset_1(D_63, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_264])).
% 2.71/1.49  tff(c_318, plain, (![D_152, B_153]: (r3_lattices('#skF_6', D_152, k16_lattice3('#skF_6', B_153)) | ~r3_lattice3('#skF_6', D_152, B_153) | ~m1_subset_1(D_152, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_48, c_269])).
% 2.71/1.49  tff(c_36, plain, (~r3_lattices('#skF_6', '#skF_7', k16_lattice3('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.71/1.49  tff(c_325, plain, (~r3_lattice3('#skF_6', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_318, c_36])).
% 2.71/1.49  tff(c_333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_325])).
% 2.71/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.49  
% 2.71/1.49  Inference rules
% 2.71/1.49  ----------------------
% 2.71/1.49  #Ref     : 0
% 2.71/1.49  #Sup     : 49
% 2.71/1.49  #Fact    : 0
% 2.71/1.49  #Define  : 0
% 2.71/1.49  #Split   : 0
% 2.71/1.49  #Chain   : 0
% 2.71/1.49  #Close   : 0
% 2.71/1.49  
% 2.71/1.49  Ordering : KBO
% 2.71/1.49  
% 2.71/1.49  Simplification rules
% 2.71/1.49  ----------------------
% 2.71/1.49  #Subsume      : 5
% 2.71/1.49  #Demod        : 84
% 2.71/1.49  #Tautology    : 15
% 2.71/1.49  #SimpNegUnit  : 20
% 2.71/1.49  #BackRed      : 0
% 2.71/1.49  
% 2.71/1.49  #Partial instantiations: 0
% 2.71/1.49  #Strategies tried      : 1
% 2.71/1.49  
% 2.71/1.49  Timing (in seconds)
% 2.71/1.49  ----------------------
% 2.71/1.49  Preprocessing        : 0.38
% 2.71/1.49  Parsing              : 0.21
% 2.71/1.49  CNF conversion       : 0.04
% 2.71/1.50  Main loop            : 0.28
% 2.71/1.50  Inferencing          : 0.12
% 2.71/1.50  Reduction            : 0.08
% 2.71/1.50  Demodulation         : 0.05
% 2.71/1.50  BG Simplification    : 0.02
% 2.71/1.50  Subsumption          : 0.05
% 2.71/1.50  Abstraction          : 0.01
% 2.71/1.50  MUC search           : 0.00
% 2.71/1.50  Cooper               : 0.00
% 2.71/1.50  Total                : 0.70
% 2.71/1.50  Index Insertion      : 0.00
% 2.71/1.50  Index Deletion       : 0.00
% 2.71/1.50  Index Matching       : 0.00
% 2.71/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
