%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:58 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 383 expanded)
%              Number of leaves         :   22 ( 137 expanded)
%              Depth                    :   16
%              Number of atoms          :  184 (1685 expanded)
%              Number of equality atoms :   12 (  60 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > l1_orders_2 > #nlpp > u1_struct_0 > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( ( r1_lattice3(A,k1_tarski(C),B)
                   => r1_orders_2(A,B,C) )
                  & ( r1_orders_2(A,B,C)
                   => r1_lattice3(A,k1_tarski(C),B) )
                  & ( r2_lattice3(A,k1_tarski(C),B)
                   => r1_orders_2(A,C,B) )
                  & ( r1_orders_2(A,C,B)
                   => r2_lattice3(A,k1_tarski(C),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(c_42,plain,
    ( r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_88,plain,(
    ~ r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_34,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_112,plain,(
    ! [A_47,B_48,C_49] :
      ( r2_hidden('#skF_4'(A_47,B_48,C_49),B_48)
      | r2_lattice3(A_47,B_48,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0(A_47))
      | ~ l1_orders_2(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_129,plain,(
    ! [A_67,A_68,C_69] :
      ( '#skF_4'(A_67,k1_tarski(A_68),C_69) = A_68
      | r2_lattice3(A_67,k1_tarski(A_68),C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(A_67))
      | ~ l1_orders_2(A_67) ) ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_132,plain,
    ( '#skF_4'('#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_129,c_88])).

tff(c_135,plain,(
    '#skF_4'('#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_132])).

tff(c_24,plain,(
    ! [A_18,B_25,C_26] :
      ( ~ r1_orders_2(A_18,'#skF_4'(A_18,B_25,C_26),C_26)
      | r2_lattice3(A_18,B_25,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_139,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_24])).

tff(c_149,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_139])).

tff(c_150,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_149])).

tff(c_66,plain,
    ( r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_159,plain,
    ( r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_88,c_66])).

tff(c_160,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_60,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_162,plain,
    ( ~ r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_60])).

tff(c_163,plain,(
    ~ r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_88,c_162])).

tff(c_118,plain,(
    ! [A_50,B_51,C_52] :
      ( r2_hidden('#skF_3'(A_50,B_51,C_52),B_51)
      | r1_lattice3(A_50,B_51,C_52)
      | ~ m1_subset_1(C_52,u1_struct_0(A_50))
      | ~ l1_orders_2(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_123,plain,(
    ! [A_50,A_1,C_52] :
      ( '#skF_3'(A_50,k1_tarski(A_1),C_52) = A_1
      | r1_lattice3(A_50,k1_tarski(A_1),C_52)
      | ~ m1_subset_1(C_52,u1_struct_0(A_50))
      | ~ l1_orders_2(A_50) ) ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_166,plain,
    ( '#skF_3'('#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_123,c_163])).

tff(c_169,plain,(
    '#skF_3'('#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_166])).

tff(c_16,plain,(
    ! [A_6,C_14,B_13] :
      ( ~ r1_orders_2(A_6,C_14,'#skF_3'(A_6,B_13,C_14))
      | r1_lattice3(A_6,B_13,C_14)
      | ~ m1_subset_1(C_14,u1_struct_0(A_6))
      | ~ l1_orders_2(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_176,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_16])).

tff(c_186,plain,(
    r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_160,c_176])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_186])).

tff(c_190,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_189,plain,(
    r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_192,plain,(
    ! [A_73,C_74,D_75,B_76] :
      ( r1_orders_2(A_73,C_74,D_75)
      | ~ r2_hidden(D_75,B_76)
      | ~ m1_subset_1(D_75,u1_struct_0(A_73))
      | ~ r1_lattice3(A_73,B_76,C_74)
      | ~ m1_subset_1(C_74,u1_struct_0(A_73))
      | ~ l1_orders_2(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_208,plain,(
    ! [A_77,C_78,C_79] :
      ( r1_orders_2(A_77,C_78,C_79)
      | ~ m1_subset_1(C_79,u1_struct_0(A_77))
      | ~ r1_lattice3(A_77,k1_tarski(C_79),C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(A_77))
      | ~ l1_orders_2(A_77) ) ),
    inference(resolution,[status(thm)],[c_4,c_192])).

tff(c_211,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_189,c_208])).

tff(c_217,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_211])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_217])).

tff(c_221,plain,(
    r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_220,plain,
    ( ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_222,plain,(
    ~ r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_352,plain,(
    ! [A_119,D_120,C_121,B_122] :
      ( r1_orders_2(A_119,D_120,C_121)
      | ~ r2_hidden(D_120,B_122)
      | ~ m1_subset_1(D_120,u1_struct_0(A_119))
      | ~ r2_lattice3(A_119,B_122,C_121)
      | ~ m1_subset_1(C_121,u1_struct_0(A_119))
      | ~ l1_orders_2(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_435,plain,(
    ! [A_124,C_125,C_126] :
      ( r1_orders_2(A_124,C_125,C_126)
      | ~ m1_subset_1(C_125,u1_struct_0(A_124))
      | ~ r2_lattice3(A_124,k1_tarski(C_125),C_126)
      | ~ m1_subset_1(C_126,u1_struct_0(A_124))
      | ~ l1_orders_2(A_124) ) ),
    inference(resolution,[status(thm)],[c_4,c_352])).

tff(c_441,plain,
    ( r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_221,c_435])).

tff(c_445,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_441])).

tff(c_447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_445])).

tff(c_449,plain,(
    r1_orders_2('#skF_5','#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_448,plain,
    ( r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_450,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_448])).

tff(c_36,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | ~ r1_orders_2('#skF_5','#skF_7','#skF_6')
    | ~ r2_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_452,plain,(
    ~ r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_449,c_450,c_36])).

tff(c_476,plain,(
    ! [A_129,B_130,C_131] :
      ( r2_hidden('#skF_3'(A_129,B_130,C_131),B_130)
      | r1_lattice3(A_129,B_130,C_131)
      | ~ m1_subset_1(C_131,u1_struct_0(A_129))
      | ~ l1_orders_2(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_493,plain,(
    ! [A_149,A_150,C_151] :
      ( '#skF_3'(A_149,k1_tarski(A_150),C_151) = A_150
      | r1_lattice3(A_149,k1_tarski(A_150),C_151)
      | ~ m1_subset_1(C_151,u1_struct_0(A_149))
      | ~ l1_orders_2(A_149) ) ),
    inference(resolution,[status(thm)],[c_476,c_2])).

tff(c_496,plain,
    ( '#skF_3'('#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_493,c_452])).

tff(c_499,plain,(
    '#skF_3'('#skF_5',k1_tarski('#skF_7'),'#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_496])).

tff(c_508,plain,
    ( ~ r1_orders_2('#skF_5','#skF_6','#skF_7')
    | r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_16])).

tff(c_518,plain,(
    r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_450,c_508])).

tff(c_520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_452,c_518])).

tff(c_522,plain,(
    ~ r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_521,plain,(
    r1_lattice3('#skF_5',k1_tarski('#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_571,plain,(
    ! [A_180,C_181,D_182,B_183] :
      ( r1_orders_2(A_180,C_181,D_182)
      | ~ r2_hidden(D_182,B_183)
      | ~ m1_subset_1(D_182,u1_struct_0(A_180))
      | ~ r1_lattice3(A_180,B_183,C_181)
      | ~ m1_subset_1(C_181,u1_struct_0(A_180))
      | ~ l1_orders_2(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_587,plain,(
    ! [A_184,C_185,C_186] :
      ( r1_orders_2(A_184,C_185,C_186)
      | ~ m1_subset_1(C_186,u1_struct_0(A_184))
      | ~ r1_lattice3(A_184,k1_tarski(C_186),C_185)
      | ~ m1_subset_1(C_185,u1_struct_0(A_184))
      | ~ l1_orders_2(A_184) ) ),
    inference(resolution,[status(thm)],[c_4,c_571])).

tff(c_593,plain,
    ( r1_orders_2('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_521,c_587])).

tff(c_597,plain,(
    r1_orders_2('#skF_5','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_593])).

tff(c_599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_522,c_597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:19:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.47  
% 2.79/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.48  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > m1_subset_1 > l1_orders_2 > #nlpp > u1_struct_0 > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 2.79/1.48  
% 2.79/1.48  %Foreground sorts:
% 2.79/1.48  
% 2.79/1.48  
% 2.79/1.48  %Background operators:
% 2.79/1.48  
% 2.79/1.48  
% 2.79/1.48  %Foreground operators:
% 2.79/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.79/1.48  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.79/1.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.79/1.48  tff('#skF_7', type, '#skF_7': $i).
% 2.79/1.48  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 2.79/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.79/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.79/1.48  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 2.79/1.48  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.79/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.79/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.79/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.79/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.79/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.48  
% 2.79/1.49  tff(f_85, negated_conjecture, ~(![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((((r1_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, B, C)) & (r1_orders_2(A, B, C) => r1_lattice3(A, k1_tarski(C), B))) & (r2_lattice3(A, k1_tarski(C), B) => r1_orders_2(A, C, B))) & (r1_orders_2(A, C, B) => r2_lattice3(A, k1_tarski(C), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_0)).
% 2.79/1.49  tff(f_60, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 2.79/1.49  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.79/1.49  tff(f_46, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 2.79/1.49  tff(c_42, plain, (r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r1_orders_2('#skF_5', '#skF_6', '#skF_7') | ~r1_orders_2('#skF_5', '#skF_7', '#skF_6') | ~r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.49  tff(c_88, plain, (~r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_42])).
% 2.79/1.49  tff(c_34, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.49  tff(c_32, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.49  tff(c_112, plain, (![A_47, B_48, C_49]: (r2_hidden('#skF_4'(A_47, B_48, C_49), B_48) | r2_lattice3(A_47, B_48, C_49) | ~m1_subset_1(C_49, u1_struct_0(A_47)) | ~l1_orders_2(A_47))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.79/1.49  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.79/1.49  tff(c_129, plain, (![A_67, A_68, C_69]: ('#skF_4'(A_67, k1_tarski(A_68), C_69)=A_68 | r2_lattice3(A_67, k1_tarski(A_68), C_69) | ~m1_subset_1(C_69, u1_struct_0(A_67)) | ~l1_orders_2(A_67))), inference(resolution, [status(thm)], [c_112, c_2])).
% 2.79/1.49  tff(c_132, plain, ('#skF_4'('#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_129, c_88])).
% 2.79/1.49  tff(c_135, plain, ('#skF_4'('#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_132])).
% 2.79/1.49  tff(c_24, plain, (![A_18, B_25, C_26]: (~r1_orders_2(A_18, '#skF_4'(A_18, B_25, C_26), C_26) | r2_lattice3(A_18, B_25, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_18)) | ~l1_orders_2(A_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.79/1.49  tff(c_139, plain, (~r1_orders_2('#skF_5', '#skF_7', '#skF_6') | r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_135, c_24])).
% 2.79/1.49  tff(c_149, plain, (~r1_orders_2('#skF_5', '#skF_7', '#skF_6') | r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_139])).
% 2.79/1.49  tff(c_150, plain, (~r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_88, c_149])).
% 2.79/1.49  tff(c_66, plain, (r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r1_orders_2('#skF_5', '#skF_6', '#skF_7') | r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.49  tff(c_159, plain, (r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_150, c_88, c_66])).
% 2.79/1.49  tff(c_160, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_159])).
% 2.79/1.49  tff(c_60, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7') | ~r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.49  tff(c_162, plain, (~r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_60])).
% 2.79/1.49  tff(c_163, plain, (~r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_150, c_88, c_162])).
% 2.79/1.49  tff(c_118, plain, (![A_50, B_51, C_52]: (r2_hidden('#skF_3'(A_50, B_51, C_52), B_51) | r1_lattice3(A_50, B_51, C_52) | ~m1_subset_1(C_52, u1_struct_0(A_50)) | ~l1_orders_2(A_50))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.79/1.49  tff(c_123, plain, (![A_50, A_1, C_52]: ('#skF_3'(A_50, k1_tarski(A_1), C_52)=A_1 | r1_lattice3(A_50, k1_tarski(A_1), C_52) | ~m1_subset_1(C_52, u1_struct_0(A_50)) | ~l1_orders_2(A_50))), inference(resolution, [status(thm)], [c_118, c_2])).
% 2.79/1.49  tff(c_166, plain, ('#skF_3'('#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_123, c_163])).
% 2.79/1.49  tff(c_169, plain, ('#skF_3'('#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_166])).
% 2.79/1.49  tff(c_16, plain, (![A_6, C_14, B_13]: (~r1_orders_2(A_6, C_14, '#skF_3'(A_6, B_13, C_14)) | r1_lattice3(A_6, B_13, C_14) | ~m1_subset_1(C_14, u1_struct_0(A_6)) | ~l1_orders_2(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.79/1.49  tff(c_176, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7') | r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_169, c_16])).
% 2.79/1.49  tff(c_186, plain, (r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_160, c_176])).
% 2.79/1.49  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163, c_186])).
% 2.79/1.49  tff(c_190, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_159])).
% 2.79/1.49  tff(c_30, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.49  tff(c_189, plain, (r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_159])).
% 2.79/1.49  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.79/1.49  tff(c_192, plain, (![A_73, C_74, D_75, B_76]: (r1_orders_2(A_73, C_74, D_75) | ~r2_hidden(D_75, B_76) | ~m1_subset_1(D_75, u1_struct_0(A_73)) | ~r1_lattice3(A_73, B_76, C_74) | ~m1_subset_1(C_74, u1_struct_0(A_73)) | ~l1_orders_2(A_73))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.79/1.49  tff(c_208, plain, (![A_77, C_78, C_79]: (r1_orders_2(A_77, C_78, C_79) | ~m1_subset_1(C_79, u1_struct_0(A_77)) | ~r1_lattice3(A_77, k1_tarski(C_79), C_78) | ~m1_subset_1(C_78, u1_struct_0(A_77)) | ~l1_orders_2(A_77))), inference(resolution, [status(thm)], [c_4, c_192])).
% 2.79/1.49  tff(c_211, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_189, c_208])).
% 2.79/1.49  tff(c_217, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_211])).
% 2.79/1.49  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_217])).
% 2.79/1.49  tff(c_221, plain, (r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_42])).
% 2.79/1.49  tff(c_220, plain, (~r1_orders_2('#skF_5', '#skF_7', '#skF_6') | r1_orders_2('#skF_5', '#skF_6', '#skF_7') | r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_42])).
% 2.79/1.49  tff(c_222, plain, (~r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_220])).
% 2.79/1.49  tff(c_352, plain, (![A_119, D_120, C_121, B_122]: (r1_orders_2(A_119, D_120, C_121) | ~r2_hidden(D_120, B_122) | ~m1_subset_1(D_120, u1_struct_0(A_119)) | ~r2_lattice3(A_119, B_122, C_121) | ~m1_subset_1(C_121, u1_struct_0(A_119)) | ~l1_orders_2(A_119))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.79/1.49  tff(c_435, plain, (![A_124, C_125, C_126]: (r1_orders_2(A_124, C_125, C_126) | ~m1_subset_1(C_125, u1_struct_0(A_124)) | ~r2_lattice3(A_124, k1_tarski(C_125), C_126) | ~m1_subset_1(C_126, u1_struct_0(A_124)) | ~l1_orders_2(A_124))), inference(resolution, [status(thm)], [c_4, c_352])).
% 2.79/1.49  tff(c_441, plain, (r1_orders_2('#skF_5', '#skF_7', '#skF_6') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_221, c_435])).
% 2.79/1.49  tff(c_445, plain, (r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_441])).
% 2.79/1.49  tff(c_447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_222, c_445])).
% 2.79/1.49  tff(c_449, plain, (r1_orders_2('#skF_5', '#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_220])).
% 2.79/1.49  tff(c_448, plain, (r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_220])).
% 2.79/1.49  tff(c_450, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_448])).
% 2.79/1.49  tff(c_36, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7') | ~r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | ~r1_orders_2('#skF_5', '#skF_7', '#skF_6') | ~r2_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.49  tff(c_452, plain, (~r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_449, c_450, c_36])).
% 2.79/1.49  tff(c_476, plain, (![A_129, B_130, C_131]: (r2_hidden('#skF_3'(A_129, B_130, C_131), B_130) | r1_lattice3(A_129, B_130, C_131) | ~m1_subset_1(C_131, u1_struct_0(A_129)) | ~l1_orders_2(A_129))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.79/1.49  tff(c_493, plain, (![A_149, A_150, C_151]: ('#skF_3'(A_149, k1_tarski(A_150), C_151)=A_150 | r1_lattice3(A_149, k1_tarski(A_150), C_151) | ~m1_subset_1(C_151, u1_struct_0(A_149)) | ~l1_orders_2(A_149))), inference(resolution, [status(thm)], [c_476, c_2])).
% 2.79/1.49  tff(c_496, plain, ('#skF_3'('#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_493, c_452])).
% 2.79/1.49  tff(c_499, plain, ('#skF_3'('#skF_5', k1_tarski('#skF_7'), '#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_496])).
% 2.79/1.49  tff(c_508, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7') | r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_499, c_16])).
% 2.79/1.49  tff(c_518, plain, (r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_450, c_508])).
% 2.79/1.49  tff(c_520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_452, c_518])).
% 2.79/1.49  tff(c_522, plain, (~r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_448])).
% 2.79/1.49  tff(c_521, plain, (r1_lattice3('#skF_5', k1_tarski('#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_448])).
% 2.79/1.49  tff(c_571, plain, (![A_180, C_181, D_182, B_183]: (r1_orders_2(A_180, C_181, D_182) | ~r2_hidden(D_182, B_183) | ~m1_subset_1(D_182, u1_struct_0(A_180)) | ~r1_lattice3(A_180, B_183, C_181) | ~m1_subset_1(C_181, u1_struct_0(A_180)) | ~l1_orders_2(A_180))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.79/1.49  tff(c_587, plain, (![A_184, C_185, C_186]: (r1_orders_2(A_184, C_185, C_186) | ~m1_subset_1(C_186, u1_struct_0(A_184)) | ~r1_lattice3(A_184, k1_tarski(C_186), C_185) | ~m1_subset_1(C_185, u1_struct_0(A_184)) | ~l1_orders_2(A_184))), inference(resolution, [status(thm)], [c_4, c_571])).
% 2.79/1.49  tff(c_593, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_521, c_587])).
% 2.79/1.49  tff(c_597, plain, (r1_orders_2('#skF_5', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_593])).
% 2.79/1.49  tff(c_599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_522, c_597])).
% 2.79/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.49  
% 2.79/1.49  Inference rules
% 2.79/1.49  ----------------------
% 2.79/1.49  #Ref     : 0
% 2.79/1.49  #Sup     : 103
% 2.79/1.49  #Fact    : 0
% 2.79/1.49  #Define  : 0
% 2.79/1.49  #Split   : 9
% 2.79/1.49  #Chain   : 0
% 2.79/1.49  #Close   : 0
% 2.79/1.49  
% 2.79/1.49  Ordering : KBO
% 2.79/1.49  
% 2.79/1.49  Simplification rules
% 2.79/1.49  ----------------------
% 2.79/1.49  #Subsume      : 6
% 2.79/1.49  #Demod        : 92
% 2.79/1.49  #Tautology    : 57
% 2.79/1.49  #SimpNegUnit  : 18
% 2.79/1.49  #BackRed      : 0
% 2.79/1.49  
% 2.79/1.49  #Partial instantiations: 0
% 2.79/1.49  #Strategies tried      : 1
% 2.79/1.49  
% 2.79/1.49  Timing (in seconds)
% 2.79/1.49  ----------------------
% 2.79/1.50  Preprocessing        : 0.32
% 2.79/1.50  Parsing              : 0.17
% 2.79/1.50  CNF conversion       : 0.03
% 2.79/1.50  Main loop            : 0.32
% 2.79/1.50  Inferencing          : 0.13
% 2.79/1.50  Reduction            : 0.08
% 2.79/1.50  Demodulation         : 0.06
% 2.79/1.50  BG Simplification    : 0.02
% 2.79/1.50  Subsumption          : 0.06
% 2.79/1.50  Abstraction          : 0.02
% 2.79/1.50  MUC search           : 0.00
% 2.79/1.50  Cooper               : 0.00
% 2.79/1.50  Total                : 0.68
% 2.79/1.50  Index Insertion      : 0.00
% 2.79/1.50  Index Deletion       : 0.00
% 2.79/1.50  Index Matching       : 0.00
% 2.79/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
