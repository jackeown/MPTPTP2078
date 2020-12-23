%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:12 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 172 expanded)
%              Number of leaves         :   27 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  156 ( 545 expanded)
%              Number of equality atoms :   33 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_lattices > m1_subset_1 > v8_lattices > v6_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v6_lattices(A)
          & v8_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => r1_lattices(A,k4_lattices(A,B,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

tff(f_87,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k4_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

tff(f_53,axiom,(
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

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v8_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,k2_lattices(A,B,C),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    v6_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_30,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_37,plain,(
    ! [A_33] :
      ( l1_lattices(A_33)
      | ~ l3_lattices(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_41,plain,(
    l1_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_37])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_313,plain,(
    ! [A_54,B_55,C_56] :
      ( k4_lattices(A_54,B_55,C_56) = k2_lattices(A_54,B_55,C_56)
      | ~ m1_subset_1(C_56,u1_struct_0(A_54))
      | ~ m1_subset_1(B_55,u1_struct_0(A_54))
      | ~ l1_lattices(A_54)
      | ~ v6_lattices(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_325,plain,(
    ! [B_55] :
      ( k4_lattices('#skF_3',B_55,'#skF_5') = k2_lattices('#skF_3',B_55,'#skF_5')
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_313])).

tff(c_341,plain,(
    ! [B_55] :
      ( k4_lattices('#skF_3',B_55,'#skF_5') = k2_lattices('#skF_3',B_55,'#skF_5')
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_41,c_325])).

tff(c_347,plain,(
    ! [B_57] :
      ( k4_lattices('#skF_3',B_57,'#skF_5') = k2_lattices('#skF_3',B_57,'#skF_5')
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_341])).

tff(c_387,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_5') = k2_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_347])).

tff(c_24,plain,(
    ~ r1_lattices('#skF_3',k4_lattices('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_144,plain,(
    ! [A_49,C_50,B_51] :
      ( k4_lattices(A_49,C_50,B_51) = k4_lattices(A_49,B_51,C_50)
      | ~ m1_subset_1(C_50,u1_struct_0(A_49))
      | ~ m1_subset_1(B_51,u1_struct_0(A_49))
      | ~ l1_lattices(A_49)
      | ~ v6_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_152,plain,(
    ! [B_51] :
      ( k4_lattices('#skF_3',B_51,'#skF_5') = k4_lattices('#skF_3','#skF_5',B_51)
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_144])).

tff(c_160,plain,(
    ! [B_51] :
      ( k4_lattices('#skF_3',B_51,'#skF_5') = k4_lattices('#skF_3','#skF_5',B_51)
      | ~ m1_subset_1(B_51,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_41,c_152])).

tff(c_166,plain,(
    ! [B_52] :
      ( k4_lattices('#skF_3',B_52,'#skF_5') = k4_lattices('#skF_3','#skF_5',B_52)
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_160])).

tff(c_199,plain,(
    k4_lattices('#skF_3','#skF_5','#skF_4') = k4_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_166])).

tff(c_16,plain,(
    ! [A_22,B_23,C_24] :
      ( m1_subset_1(k4_lattices(A_22,B_23,C_24),u1_struct_0(A_22))
      | ~ m1_subset_1(C_24,u1_struct_0(A_22))
      | ~ m1_subset_1(B_23,u1_struct_0(A_22))
      | ~ l1_lattices(A_22)
      | ~ v6_lattices(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_203,plain,
    ( m1_subset_1(k4_lattices('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_lattices('#skF_3')
    | ~ v6_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_16])).

tff(c_207,plain,
    ( m1_subset_1(k4_lattices('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_41,c_26,c_28,c_203])).

tff(c_208,plain,(
    m1_subset_1(k4_lattices('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_207])).

tff(c_42,plain,(
    ! [A_34] :
      ( l2_lattices(A_34)
      | ~ l3_lattices(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_46,plain,(
    l2_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_42])).

tff(c_51,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_lattices(A_41,B_42,C_43)
      | k1_lattices(A_41,B_42,C_43) != C_43
      | ~ m1_subset_1(C_43,u1_struct_0(A_41))
      | ~ m1_subset_1(B_42,u1_struct_0(A_41))
      | ~ l2_lattices(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_61,plain,(
    ! [B_42] :
      ( r1_lattices('#skF_3',B_42,'#skF_4')
      | k1_lattices('#skF_3',B_42,'#skF_4') != '#skF_4'
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3'))
      | ~ l2_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_51])).

tff(c_71,plain,(
    ! [B_42] :
      ( r1_lattices('#skF_3',B_42,'#skF_4')
      | k1_lattices('#skF_3',B_42,'#skF_4') != '#skF_4'
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_61])).

tff(c_72,plain,(
    ! [B_42] :
      ( r1_lattices('#skF_3',B_42,'#skF_4')
      | k1_lattices('#skF_3',B_42,'#skF_4') != '#skF_4'
      | ~ m1_subset_1(B_42,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_71])).

tff(c_217,plain,
    ( r1_lattices('#skF_3',k4_lattices('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k1_lattices('#skF_3',k4_lattices('#skF_3','#skF_4','#skF_5'),'#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_208,c_72])).

tff(c_230,plain,(
    k1_lattices('#skF_3',k4_lattices('#skF_3','#skF_4','#skF_5'),'#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_217])).

tff(c_438,plain,(
    k1_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_5'),'#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_230])).

tff(c_440,plain,(
    k4_lattices('#skF_3','#skF_5','#skF_4') = k2_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_199])).

tff(c_327,plain,(
    ! [B_55] :
      ( k4_lattices('#skF_3',B_55,'#skF_4') = k2_lattices('#skF_3',B_55,'#skF_4')
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_313])).

tff(c_345,plain,(
    ! [B_55] :
      ( k4_lattices('#skF_3',B_55,'#skF_4') = k2_lattices('#skF_3',B_55,'#skF_4')
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_41,c_327])).

tff(c_581,plain,(
    ! [B_61] :
      ( k4_lattices('#skF_3',B_61,'#skF_4') = k2_lattices('#skF_3',B_61,'#skF_4')
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_345])).

tff(c_605,plain,(
    k4_lattices('#skF_3','#skF_5','#skF_4') = k2_lattices('#skF_3','#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_581])).

tff(c_625,plain,(
    k2_lattices('#skF_3','#skF_5','#skF_4') = k2_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_605])).

tff(c_32,plain,(
    v8_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_503,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_lattices(A_58,k2_lattices(A_58,B_59,C_60),C_60) = C_60
      | ~ m1_subset_1(C_60,u1_struct_0(A_58))
      | ~ m1_subset_1(B_59,u1_struct_0(A_58))
      | ~ v8_lattices(A_58)
      | ~ l3_lattices(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_517,plain,(
    ! [B_59] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_59,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_59,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_503])).

tff(c_535,plain,(
    ! [B_59] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_59,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_59,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_517])).

tff(c_689,plain,(
    ! [B_62] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_62,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_535])).

tff(c_716,plain,(
    k1_lattices('#skF_3',k2_lattices('#skF_3','#skF_5','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_689])).

tff(c_737,plain,(
    k1_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_5'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_716])).

tff(c_739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_438,c_737])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:45:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.42  
% 2.68/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.42  %$ r1_lattices > m1_subset_1 > v8_lattices > v6_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.68/1.42  
% 2.68/1.42  %Foreground sorts:
% 2.68/1.42  
% 2.68/1.42  
% 2.68/1.42  %Background operators:
% 2.68/1.42  
% 2.68/1.42  
% 2.68/1.42  %Foreground operators:
% 2.68/1.42  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.68/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.68/1.42  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.68/1.42  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.68/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.68/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.42  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 2.68/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.68/1.42  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.68/1.42  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.68/1.42  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.68/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.68/1.42  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.68/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.42  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.68/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.68/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.42  
% 2.68/1.43  tff(f_118, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, k4_lattices(A, B, C), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_lattices)).
% 2.68/1.43  tff(f_87, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.68/1.43  tff(f_100, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 2.68/1.43  tff(f_38, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k4_lattices(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 2.68/1.43  tff(f_81, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k4_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_lattices)).
% 2.68/1.43  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 2.68/1.43  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 2.68/1.43  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.68/1.43  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.68/1.43  tff(c_34, plain, (v6_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.68/1.43  tff(c_30, plain, (l3_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.68/1.43  tff(c_37, plain, (![A_33]: (l1_lattices(A_33) | ~l3_lattices(A_33))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.68/1.43  tff(c_41, plain, (l1_lattices('#skF_3')), inference(resolution, [status(thm)], [c_30, c_37])).
% 2.68/1.43  tff(c_26, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.68/1.43  tff(c_313, plain, (![A_54, B_55, C_56]: (k4_lattices(A_54, B_55, C_56)=k2_lattices(A_54, B_55, C_56) | ~m1_subset_1(C_56, u1_struct_0(A_54)) | ~m1_subset_1(B_55, u1_struct_0(A_54)) | ~l1_lattices(A_54) | ~v6_lattices(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.68/1.43  tff(c_325, plain, (![B_55]: (k4_lattices('#skF_3', B_55, '#skF_5')=k2_lattices('#skF_3', B_55, '#skF_5') | ~m1_subset_1(B_55, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_313])).
% 2.68/1.43  tff(c_341, plain, (![B_55]: (k4_lattices('#skF_3', B_55, '#skF_5')=k2_lattices('#skF_3', B_55, '#skF_5') | ~m1_subset_1(B_55, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_41, c_325])).
% 2.68/1.43  tff(c_347, plain, (![B_57]: (k4_lattices('#skF_3', B_57, '#skF_5')=k2_lattices('#skF_3', B_57, '#skF_5') | ~m1_subset_1(B_57, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_341])).
% 2.68/1.43  tff(c_387, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_5')=k2_lattices('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_28, c_347])).
% 2.68/1.43  tff(c_24, plain, (~r1_lattices('#skF_3', k4_lattices('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.68/1.43  tff(c_144, plain, (![A_49, C_50, B_51]: (k4_lattices(A_49, C_50, B_51)=k4_lattices(A_49, B_51, C_50) | ~m1_subset_1(C_50, u1_struct_0(A_49)) | ~m1_subset_1(B_51, u1_struct_0(A_49)) | ~l1_lattices(A_49) | ~v6_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.68/1.43  tff(c_152, plain, (![B_51]: (k4_lattices('#skF_3', B_51, '#skF_5')=k4_lattices('#skF_3', '#skF_5', B_51) | ~m1_subset_1(B_51, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_144])).
% 2.68/1.43  tff(c_160, plain, (![B_51]: (k4_lattices('#skF_3', B_51, '#skF_5')=k4_lattices('#skF_3', '#skF_5', B_51) | ~m1_subset_1(B_51, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_41, c_152])).
% 2.68/1.43  tff(c_166, plain, (![B_52]: (k4_lattices('#skF_3', B_52, '#skF_5')=k4_lattices('#skF_3', '#skF_5', B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_160])).
% 2.68/1.43  tff(c_199, plain, (k4_lattices('#skF_3', '#skF_5', '#skF_4')=k4_lattices('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_28, c_166])).
% 2.68/1.43  tff(c_16, plain, (![A_22, B_23, C_24]: (m1_subset_1(k4_lattices(A_22, B_23, C_24), u1_struct_0(A_22)) | ~m1_subset_1(C_24, u1_struct_0(A_22)) | ~m1_subset_1(B_23, u1_struct_0(A_22)) | ~l1_lattices(A_22) | ~v6_lattices(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.68/1.43  tff(c_203, plain, (m1_subset_1(k4_lattices('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_199, c_16])).
% 2.68/1.43  tff(c_207, plain, (m1_subset_1(k4_lattices('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_41, c_26, c_28, c_203])).
% 2.68/1.43  tff(c_208, plain, (m1_subset_1(k4_lattices('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_36, c_207])).
% 2.68/1.43  tff(c_42, plain, (![A_34]: (l2_lattices(A_34) | ~l3_lattices(A_34))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.68/1.43  tff(c_46, plain, (l2_lattices('#skF_3')), inference(resolution, [status(thm)], [c_30, c_42])).
% 2.68/1.43  tff(c_51, plain, (![A_41, B_42, C_43]: (r1_lattices(A_41, B_42, C_43) | k1_lattices(A_41, B_42, C_43)!=C_43 | ~m1_subset_1(C_43, u1_struct_0(A_41)) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l2_lattices(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.68/1.43  tff(c_61, plain, (![B_42]: (r1_lattices('#skF_3', B_42, '#skF_4') | k1_lattices('#skF_3', B_42, '#skF_4')!='#skF_4' | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_51])).
% 2.68/1.43  tff(c_71, plain, (![B_42]: (r1_lattices('#skF_3', B_42, '#skF_4') | k1_lattices('#skF_3', B_42, '#skF_4')!='#skF_4' | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_61])).
% 2.68/1.43  tff(c_72, plain, (![B_42]: (r1_lattices('#skF_3', B_42, '#skF_4') | k1_lattices('#skF_3', B_42, '#skF_4')!='#skF_4' | ~m1_subset_1(B_42, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_71])).
% 2.68/1.43  tff(c_217, plain, (r1_lattices('#skF_3', k4_lattices('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k1_lattices('#skF_3', k4_lattices('#skF_3', '#skF_4', '#skF_5'), '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_208, c_72])).
% 2.68/1.43  tff(c_230, plain, (k1_lattices('#skF_3', k4_lattices('#skF_3', '#skF_4', '#skF_5'), '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_24, c_217])).
% 2.68/1.43  tff(c_438, plain, (k1_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_5'), '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_387, c_230])).
% 2.68/1.43  tff(c_440, plain, (k4_lattices('#skF_3', '#skF_5', '#skF_4')=k2_lattices('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_387, c_199])).
% 2.68/1.43  tff(c_327, plain, (![B_55]: (k4_lattices('#skF_3', B_55, '#skF_4')=k2_lattices('#skF_3', B_55, '#skF_4') | ~m1_subset_1(B_55, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_313])).
% 2.68/1.43  tff(c_345, plain, (![B_55]: (k4_lattices('#skF_3', B_55, '#skF_4')=k2_lattices('#skF_3', B_55, '#skF_4') | ~m1_subset_1(B_55, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_41, c_327])).
% 2.68/1.43  tff(c_581, plain, (![B_61]: (k4_lattices('#skF_3', B_61, '#skF_4')=k2_lattices('#skF_3', B_61, '#skF_4') | ~m1_subset_1(B_61, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_345])).
% 2.68/1.43  tff(c_605, plain, (k4_lattices('#skF_3', '#skF_5', '#skF_4')=k2_lattices('#skF_3', '#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_581])).
% 2.68/1.43  tff(c_625, plain, (k2_lattices('#skF_3', '#skF_5', '#skF_4')=k2_lattices('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_440, c_605])).
% 2.68/1.43  tff(c_32, plain, (v8_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.68/1.43  tff(c_503, plain, (![A_58, B_59, C_60]: (k1_lattices(A_58, k2_lattices(A_58, B_59, C_60), C_60)=C_60 | ~m1_subset_1(C_60, u1_struct_0(A_58)) | ~m1_subset_1(B_59, u1_struct_0(A_58)) | ~v8_lattices(A_58) | ~l3_lattices(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.68/1.43  tff(c_517, plain, (![B_59]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_59, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_59, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_503])).
% 2.68/1.43  tff(c_535, plain, (![B_59]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_59, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_59, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_517])).
% 2.68/1.43  tff(c_689, plain, (![B_62]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_62, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_62, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_535])).
% 2.68/1.43  tff(c_716, plain, (k1_lattices('#skF_3', k2_lattices('#skF_3', '#skF_5', '#skF_4'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_26, c_689])).
% 2.68/1.43  tff(c_737, plain, (k1_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_5'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_625, c_716])).
% 2.68/1.43  tff(c_739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_438, c_737])).
% 2.68/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.43  
% 2.68/1.43  Inference rules
% 2.68/1.43  ----------------------
% 2.68/1.43  #Ref     : 0
% 2.68/1.43  #Sup     : 137
% 2.68/1.43  #Fact    : 0
% 2.68/1.43  #Define  : 0
% 2.68/1.43  #Split   : 4
% 2.68/1.43  #Chain   : 0
% 2.68/1.43  #Close   : 0
% 2.68/1.43  
% 2.68/1.43  Ordering : KBO
% 2.68/1.43  
% 2.68/1.43  Simplification rules
% 2.68/1.43  ----------------------
% 2.68/1.43  #Subsume      : 1
% 2.68/1.43  #Demod        : 130
% 2.68/1.43  #Tautology    : 35
% 2.68/1.43  #SimpNegUnit  : 60
% 2.68/1.43  #BackRed      : 6
% 2.68/1.43  
% 2.68/1.43  #Partial instantiations: 0
% 2.68/1.43  #Strategies tried      : 1
% 2.68/1.43  
% 2.68/1.43  Timing (in seconds)
% 2.68/1.43  ----------------------
% 2.68/1.44  Preprocessing        : 0.32
% 2.68/1.44  Parsing              : 0.16
% 2.68/1.44  CNF conversion       : 0.02
% 2.68/1.44  Main loop            : 0.34
% 2.68/1.44  Inferencing          : 0.11
% 2.68/1.44  Reduction            : 0.11
% 2.68/1.44  Demodulation         : 0.08
% 2.68/1.44  BG Simplification    : 0.02
% 2.68/1.44  Subsumption          : 0.06
% 2.68/1.44  Abstraction          : 0.03
% 3.04/1.44  MUC search           : 0.00
% 3.04/1.44  Cooper               : 0.00
% 3.04/1.44  Total                : 0.70
% 3.04/1.44  Index Insertion      : 0.00
% 3.04/1.44  Index Deletion       : 0.00
% 3.04/1.44  Index Matching       : 0.00
% 3.04/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
