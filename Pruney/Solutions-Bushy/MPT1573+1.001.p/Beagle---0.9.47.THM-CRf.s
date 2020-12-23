%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1573+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:05 EST 2020

% Result     : Theorem 4.90s
% Output     : CNFRefutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :   53 (  95 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  168 ( 423 expanded)
%              Number of equality atoms :   26 (  56 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_lattice3 > r1_yellow_0 > m1_subset_1 > v2_struct_0 > l1_orders_2 > k3_xboole_0 > k1_yellow_0 > #nlpp > u1_struct_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( r1_yellow_0(A,B)
              | r1_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) )
           => k1_yellow_0(A,B) = k1_yellow_0(A,k3_xboole_0(B,u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_yellow_0)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( ( r1_yellow_0(A,B)
            & ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_lattice3(A,B,D)
                <=> r2_lattice3(A,C,D) ) ) )
         => k1_yellow_0(A,B) = k1_yellow_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_yellow_0)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( ( r2_lattice3(A,B,C)
             => r2_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C) )
            & ( r2_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C)
             => r2_lattice3(A,B,C) )
            & ( r1_lattice3(A,B,C)
             => r1_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C) )
            & ( r1_lattice3(A,k3_xboole_0(B,u1_struct_0(A)),C)
             => r1_lattice3(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_yellow_0)).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    k1_yellow_0('#skF_2',k3_xboole_0('#skF_3',u1_struct_0('#skF_2'))) != k1_yellow_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,
    ( r1_yellow_0('#skF_2',k3_xboole_0('#skF_3',u1_struct_0('#skF_2')))
    | r1_yellow_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_62,plain,(
    r1_yellow_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_4,plain,(
    ! [A_3,B_8,C_9] :
      ( m1_subset_1('#skF_1'(A_3,B_8,C_9),u1_struct_0(A_3))
      | k1_yellow_0(A_3,C_9) = k1_yellow_0(A_3,B_8)
      | ~ r1_yellow_0(A_3,B_8)
      | ~ l1_orders_2(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_197,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_lattice3(A_49,B_50,'#skF_1'(A_49,B_50,C_51))
      | r2_lattice3(A_49,C_51,'#skF_1'(A_49,B_50,C_51))
      | k1_yellow_0(A_49,C_51) = k1_yellow_0(A_49,B_50)
      | ~ r1_yellow_0(A_49,B_50)
      | ~ l1_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_11,B_14,C_15] :
      ( r2_lattice3(A_11,B_14,C_15)
      | ~ r2_lattice3(A_11,k3_xboole_0(B_14,u1_struct_0(A_11)),C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_242,plain,(
    ! [A_55,B_56,B_57] :
      ( r2_lattice3(A_55,B_56,'#skF_1'(A_55,B_57,k3_xboole_0(B_56,u1_struct_0(A_55))))
      | ~ m1_subset_1('#skF_1'(A_55,B_57,k3_xboole_0(B_56,u1_struct_0(A_55))),u1_struct_0(A_55))
      | r2_lattice3(A_55,B_57,'#skF_1'(A_55,B_57,k3_xboole_0(B_56,u1_struct_0(A_55))))
      | k1_yellow_0(A_55,k3_xboole_0(B_56,u1_struct_0(A_55))) = k1_yellow_0(A_55,B_57)
      | ~ r1_yellow_0(A_55,B_57)
      | ~ l1_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_197,c_18])).

tff(c_252,plain,(
    ! [A_3,B_56,B_8] :
      ( r2_lattice3(A_3,B_56,'#skF_1'(A_3,B_8,k3_xboole_0(B_56,u1_struct_0(A_3))))
      | r2_lattice3(A_3,B_8,'#skF_1'(A_3,B_8,k3_xboole_0(B_56,u1_struct_0(A_3))))
      | k1_yellow_0(A_3,k3_xboole_0(B_56,u1_struct_0(A_3))) = k1_yellow_0(A_3,B_8)
      | ~ r1_yellow_0(A_3,B_8)
      | ~ l1_orders_2(A_3)
      | v2_struct_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_4,c_242])).

tff(c_265,plain,(
    ! [A_3,B_56] :
      ( k1_yellow_0(A_3,k3_xboole_0(B_56,u1_struct_0(A_3))) = k1_yellow_0(A_3,B_56)
      | ~ r1_yellow_0(A_3,B_56)
      | ~ l1_orders_2(A_3)
      | v2_struct_0(A_3)
      | r2_lattice3(A_3,B_56,'#skF_1'(A_3,B_56,k3_xboole_0(B_56,u1_struct_0(A_3)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_252])).

tff(c_315,plain,(
    ! [A_61,B_62] :
      ( k1_yellow_0(A_61,k3_xboole_0(B_62,u1_struct_0(A_61))) = k1_yellow_0(A_61,B_62)
      | ~ r1_yellow_0(A_61,B_62)
      | ~ l1_orders_2(A_61)
      | v2_struct_0(A_61)
      | r2_lattice3(A_61,B_62,'#skF_1'(A_61,B_62,k3_xboole_0(B_62,u1_struct_0(A_61)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_252])).

tff(c_20,plain,(
    ! [A_11,B_14,C_15] :
      ( r2_lattice3(A_11,k3_xboole_0(B_14,u1_struct_0(A_11)),C_15)
      | ~ r2_lattice3(A_11,B_14,C_15)
      | ~ m1_subset_1(C_15,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_172,plain,(
    ! [A_46,C_47,B_48] :
      ( ~ r2_lattice3(A_46,C_47,'#skF_1'(A_46,B_48,C_47))
      | ~ r2_lattice3(A_46,B_48,'#skF_1'(A_46,B_48,C_47))
      | k1_yellow_0(A_46,C_47) = k1_yellow_0(A_46,B_48)
      | ~ r1_yellow_0(A_46,B_48)
      | ~ l1_orders_2(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_180,plain,(
    ! [A_11,B_48,B_14] :
      ( ~ r2_lattice3(A_11,B_48,'#skF_1'(A_11,B_48,k3_xboole_0(B_14,u1_struct_0(A_11))))
      | k1_yellow_0(A_11,k3_xboole_0(B_14,u1_struct_0(A_11))) = k1_yellow_0(A_11,B_48)
      | ~ r1_yellow_0(A_11,B_48)
      | ~ r2_lattice3(A_11,B_14,'#skF_1'(A_11,B_48,k3_xboole_0(B_14,u1_struct_0(A_11))))
      | ~ m1_subset_1('#skF_1'(A_11,B_48,k3_xboole_0(B_14,u1_struct_0(A_11))),u1_struct_0(A_11))
      | ~ l1_orders_2(A_11)
      | v2_struct_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_20,c_172])).

tff(c_503,plain,(
    ! [A_74,B_75] :
      ( ~ r2_lattice3(A_74,B_75,'#skF_1'(A_74,B_75,k3_xboole_0(B_75,u1_struct_0(A_74))))
      | ~ m1_subset_1('#skF_1'(A_74,B_75,k3_xboole_0(B_75,u1_struct_0(A_74))),u1_struct_0(A_74))
      | k1_yellow_0(A_74,k3_xboole_0(B_75,u1_struct_0(A_74))) = k1_yellow_0(A_74,B_75)
      | ~ r1_yellow_0(A_74,B_75)
      | ~ l1_orders_2(A_74)
      | v2_struct_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_315,c_180])).

tff(c_540,plain,(
    ! [A_76,B_77] :
      ( ~ m1_subset_1('#skF_1'(A_76,B_77,k3_xboole_0(B_77,u1_struct_0(A_76))),u1_struct_0(A_76))
      | k1_yellow_0(A_76,k3_xboole_0(B_77,u1_struct_0(A_76))) = k1_yellow_0(A_76,B_77)
      | ~ r1_yellow_0(A_76,B_77)
      | ~ l1_orders_2(A_76)
      | v2_struct_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_265,c_503])).

tff(c_616,plain,(
    ! [A_81,B_82] :
      ( k1_yellow_0(A_81,k3_xboole_0(B_82,u1_struct_0(A_81))) = k1_yellow_0(A_81,B_82)
      | ~ r1_yellow_0(A_81,B_82)
      | ~ l1_orders_2(A_81)
      | v2_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_4,c_540])).

tff(c_622,plain,
    ( ~ r1_yellow_0('#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_22])).

tff(c_637,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_62,c_622])).

tff(c_639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_637])).

tff(c_640,plain,(
    r1_yellow_0('#skF_2',k3_xboole_0('#skF_3',u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_767,plain,(
    ! [A_110,B_111,C_112] :
      ( r2_lattice3(A_110,B_111,'#skF_1'(A_110,B_111,C_112))
      | r2_lattice3(A_110,C_112,'#skF_1'(A_110,B_111,C_112))
      | k1_yellow_0(A_110,C_112) = k1_yellow_0(A_110,B_111)
      | ~ r1_yellow_0(A_110,B_111)
      | ~ l1_orders_2(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1071,plain,(
    ! [A_135,B_136,C_137] :
      ( r2_lattice3(A_135,B_136,'#skF_1'(A_135,k3_xboole_0(B_136,u1_struct_0(A_135)),C_137))
      | ~ m1_subset_1('#skF_1'(A_135,k3_xboole_0(B_136,u1_struct_0(A_135)),C_137),u1_struct_0(A_135))
      | r2_lattice3(A_135,C_137,'#skF_1'(A_135,k3_xboole_0(B_136,u1_struct_0(A_135)),C_137))
      | k1_yellow_0(A_135,k3_xboole_0(B_136,u1_struct_0(A_135))) = k1_yellow_0(A_135,C_137)
      | ~ r1_yellow_0(A_135,k3_xboole_0(B_136,u1_struct_0(A_135)))
      | ~ l1_orders_2(A_135)
      | v2_struct_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_767,c_18])).

tff(c_1081,plain,(
    ! [A_3,B_136,C_9] :
      ( r2_lattice3(A_3,B_136,'#skF_1'(A_3,k3_xboole_0(B_136,u1_struct_0(A_3)),C_9))
      | r2_lattice3(A_3,C_9,'#skF_1'(A_3,k3_xboole_0(B_136,u1_struct_0(A_3)),C_9))
      | k1_yellow_0(A_3,k3_xboole_0(B_136,u1_struct_0(A_3))) = k1_yellow_0(A_3,C_9)
      | ~ r1_yellow_0(A_3,k3_xboole_0(B_136,u1_struct_0(A_3)))
      | ~ l1_orders_2(A_3)
      | v2_struct_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_4,c_1071])).

tff(c_1259,plain,(
    ! [A_3,B_136] :
      ( k1_yellow_0(A_3,k3_xboole_0(B_136,u1_struct_0(A_3))) = k1_yellow_0(A_3,B_136)
      | ~ r1_yellow_0(A_3,k3_xboole_0(B_136,u1_struct_0(A_3)))
      | ~ l1_orders_2(A_3)
      | v2_struct_0(A_3)
      | r2_lattice3(A_3,B_136,'#skF_1'(A_3,k3_xboole_0(B_136,u1_struct_0(A_3)),B_136)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1081])).

tff(c_1309,plain,(
    ! [A_152,B_153] :
      ( k1_yellow_0(A_152,k3_xboole_0(B_153,u1_struct_0(A_152))) = k1_yellow_0(A_152,B_153)
      | ~ r1_yellow_0(A_152,k3_xboole_0(B_153,u1_struct_0(A_152)))
      | ~ l1_orders_2(A_152)
      | v2_struct_0(A_152)
      | r2_lattice3(A_152,B_153,'#skF_1'(A_152,k3_xboole_0(B_153,u1_struct_0(A_152)),B_153)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1081])).

tff(c_6,plain,(
    ! [A_3,C_9,B_8] :
      ( ~ r2_lattice3(A_3,C_9,'#skF_1'(A_3,B_8,C_9))
      | ~ r2_lattice3(A_3,B_8,'#skF_1'(A_3,B_8,C_9))
      | k1_yellow_0(A_3,C_9) = k1_yellow_0(A_3,B_8)
      | ~ r1_yellow_0(A_3,B_8)
      | ~ l1_orders_2(A_3)
      | v2_struct_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1357,plain,(
    ! [A_156,B_157] :
      ( ~ r2_lattice3(A_156,k3_xboole_0(B_157,u1_struct_0(A_156)),'#skF_1'(A_156,k3_xboole_0(B_157,u1_struct_0(A_156)),B_157))
      | k1_yellow_0(A_156,k3_xboole_0(B_157,u1_struct_0(A_156))) = k1_yellow_0(A_156,B_157)
      | ~ r1_yellow_0(A_156,k3_xboole_0(B_157,u1_struct_0(A_156)))
      | ~ l1_orders_2(A_156)
      | v2_struct_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_1309,c_6])).

tff(c_1845,plain,(
    ! [A_179,B_180] :
      ( k1_yellow_0(A_179,k3_xboole_0(B_180,u1_struct_0(A_179))) = k1_yellow_0(A_179,B_180)
      | ~ r1_yellow_0(A_179,k3_xboole_0(B_180,u1_struct_0(A_179)))
      | ~ r2_lattice3(A_179,B_180,'#skF_1'(A_179,k3_xboole_0(B_180,u1_struct_0(A_179)),B_180))
      | ~ m1_subset_1('#skF_1'(A_179,k3_xboole_0(B_180,u1_struct_0(A_179)),B_180),u1_struct_0(A_179))
      | ~ l1_orders_2(A_179)
      | v2_struct_0(A_179) ) ),
    inference(resolution,[status(thm)],[c_20,c_1357])).

tff(c_1884,plain,(
    ! [A_181,B_182] :
      ( ~ m1_subset_1('#skF_1'(A_181,k3_xboole_0(B_182,u1_struct_0(A_181)),B_182),u1_struct_0(A_181))
      | k1_yellow_0(A_181,k3_xboole_0(B_182,u1_struct_0(A_181))) = k1_yellow_0(A_181,B_182)
      | ~ r1_yellow_0(A_181,k3_xboole_0(B_182,u1_struct_0(A_181)))
      | ~ l1_orders_2(A_181)
      | v2_struct_0(A_181) ) ),
    inference(resolution,[status(thm)],[c_1259,c_1845])).

tff(c_1898,plain,(
    ! [A_183,C_184] :
      ( k1_yellow_0(A_183,k3_xboole_0(C_184,u1_struct_0(A_183))) = k1_yellow_0(A_183,C_184)
      | ~ r1_yellow_0(A_183,k3_xboole_0(C_184,u1_struct_0(A_183)))
      | ~ l1_orders_2(A_183)
      | v2_struct_0(A_183) ) ),
    inference(resolution,[status(thm)],[c_4,c_1884])).

tff(c_1901,plain,
    ( k1_yellow_0('#skF_2',k3_xboole_0('#skF_3',u1_struct_0('#skF_2'))) = k1_yellow_0('#skF_2','#skF_3')
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_640,c_1898])).

tff(c_1912,plain,
    ( k1_yellow_0('#skF_2',k3_xboole_0('#skF_3',u1_struct_0('#skF_2'))) = k1_yellow_0('#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1901])).

tff(c_1914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22,c_1912])).

%------------------------------------------------------------------------------
