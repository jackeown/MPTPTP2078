%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:12 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 210 expanded)
%              Number of leaves         :   27 (  87 expanded)
%              Depth                    :   13
%              Number of atoms          :  153 ( 674 expanded)
%              Number of equality atoms :   32 (  60 expanded)
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

tff(f_116,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).

tff(f_85,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k4_lattices(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k2_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattices)).

tff(c_28,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_34,plain,(
    v6_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_30,plain,(
    l3_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_37,plain,(
    ! [A_33] :
      ( l1_lattices(A_33)
      | ~ l3_lattices(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_41,plain,(
    l1_lattices('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_37])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_239,plain,(
    ! [A_54,B_55,C_56] :
      ( k4_lattices(A_54,B_55,C_56) = k2_lattices(A_54,B_55,C_56)
      | ~ m1_subset_1(C_56,u1_struct_0(A_54))
      | ~ m1_subset_1(B_55,u1_struct_0(A_54))
      | ~ l1_lattices(A_54)
      | ~ v6_lattices(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_247,plain,(
    ! [B_55] :
      ( k4_lattices('#skF_3',B_55,'#skF_5') = k2_lattices('#skF_3',B_55,'#skF_5')
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_239])).

tff(c_255,plain,(
    ! [B_55] :
      ( k4_lattices('#skF_3',B_55,'#skF_5') = k2_lattices('#skF_3',B_55,'#skF_5')
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_41,c_247])).

tff(c_261,plain,(
    ! [B_57] :
      ( k4_lattices('#skF_3',B_57,'#skF_5') = k2_lattices('#skF_3',B_57,'#skF_5')
      | ~ m1_subset_1(B_57,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_255])).

tff(c_293,plain,(
    k4_lattices('#skF_3','#skF_4','#skF_5') = k2_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_261])).

tff(c_24,plain,(
    ~ r1_lattices('#skF_3',k4_lattices('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_299,plain,(
    ~ r1_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_24])).

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

tff(c_298,plain,(
    k4_lattices('#skF_3','#skF_5','#skF_4') = k2_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_199])).

tff(c_249,plain,(
    ! [B_55] :
      ( k4_lattices('#skF_3',B_55,'#skF_4') = k2_lattices('#skF_3',B_55,'#skF_4')
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_3'))
      | ~ l1_lattices('#skF_3')
      | ~ v6_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_239])).

tff(c_259,plain,(
    ! [B_55] :
      ( k4_lattices('#skF_3',B_55,'#skF_4') = k2_lattices('#skF_3',B_55,'#skF_4')
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_41,c_249])).

tff(c_330,plain,(
    ! [B_61] :
      ( k4_lattices('#skF_3',B_61,'#skF_4') = k2_lattices('#skF_3',B_61,'#skF_4')
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_259])).

tff(c_345,plain,(
    k4_lattices('#skF_3','#skF_5','#skF_4') = k2_lattices('#skF_3','#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_330])).

tff(c_362,plain,(
    k2_lattices('#skF_3','#skF_5','#skF_4') = k2_lattices('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_345])).

tff(c_16,plain,(
    ! [A_22,B_23,C_24] :
      ( m1_subset_1(k2_lattices(A_22,B_23,C_24),u1_struct_0(A_22))
      | ~ m1_subset_1(C_24,u1_struct_0(A_22))
      | ~ m1_subset_1(B_23,u1_struct_0(A_22))
      | ~ l1_lattices(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_371,plain,
    ( m1_subset_1(k2_lattices('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_3'))
    | ~ l1_lattices('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_16])).

tff(c_375,plain,
    ( m1_subset_1(k2_lattices('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_26,c_28,c_371])).

tff(c_376,plain,(
    m1_subset_1(k2_lattices('#skF_3','#skF_4','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_375])).

tff(c_42,plain,(
    ! [A_34] :
      ( l2_lattices(A_34)
      | ~ l3_lattices(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

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

tff(c_398,plain,
    ( r1_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k1_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_5'),'#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_376,c_72])).

tff(c_422,plain,(
    k1_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_5'),'#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_299,c_398])).

tff(c_32,plain,(
    v8_lattices('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_304,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_lattices(A_58,k2_lattices(A_58,B_59,C_60),C_60) = C_60
      | ~ m1_subset_1(C_60,u1_struct_0(A_58))
      | ~ m1_subset_1(B_59,u1_struct_0(A_58))
      | ~ v8_lattices(A_58)
      | ~ l3_lattices(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_314,plain,(
    ! [B_59] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_59,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_59,u1_struct_0('#skF_3'))
      | ~ v8_lattices('#skF_3')
      | ~ l3_lattices('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_304])).

tff(c_324,plain,(
    ! [B_59] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_59,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_59,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_314])).

tff(c_428,plain,(
    ! [B_62] :
      ( k1_lattices('#skF_3',k2_lattices('#skF_3',B_62,'#skF_4'),'#skF_4') = '#skF_4'
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_324])).

tff(c_446,plain,(
    k1_lattices('#skF_3',k2_lattices('#skF_3','#skF_5','#skF_4'),'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_428])).

tff(c_464,plain,(
    k1_lattices('#skF_3',k2_lattices('#skF_3','#skF_4','#skF_5'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_446])).

tff(c_466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_422,c_464])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:07:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.33  
% 2.51/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.33  %$ r1_lattices > m1_subset_1 > v8_lattices > v6_lattices > v2_struct_0 > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k2_lattices > k1_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.51/1.33  
% 2.51/1.33  %Foreground sorts:
% 2.51/1.33  
% 2.51/1.33  
% 2.51/1.33  %Background operators:
% 2.51/1.33  
% 2.51/1.33  
% 2.51/1.33  %Foreground operators:
% 2.51/1.33  tff(l3_lattices, type, l3_lattices: $i > $o).
% 2.51/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.51/1.33  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 2.51/1.33  tff(l2_lattices, type, l2_lattices: $i > $o).
% 2.51/1.33  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.51/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.33  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 2.51/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.51/1.33  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 2.51/1.33  tff(l1_lattices, type, l1_lattices: $i > $o).
% 2.51/1.33  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 2.51/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.33  tff(v6_lattices, type, v6_lattices: $i > $o).
% 2.51/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.33  tff(v8_lattices, type, v8_lattices: $i > $o).
% 2.51/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.51/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.33  
% 2.51/1.35  tff(f_116, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => r1_lattices(A, k4_lattices(A, B, C), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_lattices)).
% 2.51/1.35  tff(f_85, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l3_lattices)).
% 2.51/1.35  tff(f_98, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 2.51/1.35  tff(f_38, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k4_lattices(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_lattices)).
% 2.51/1.35  tff(f_79, axiom, (![A, B, C]: ((((~v2_struct_0(A) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k2_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_lattices)).
% 2.51/1.35  tff(f_53, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_lattices)).
% 2.51/1.35  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattices)).
% 2.51/1.35  tff(c_28, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.51/1.35  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.51/1.35  tff(c_34, plain, (v6_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.51/1.35  tff(c_30, plain, (l3_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.51/1.35  tff(c_37, plain, (![A_33]: (l1_lattices(A_33) | ~l3_lattices(A_33))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.51/1.35  tff(c_41, plain, (l1_lattices('#skF_3')), inference(resolution, [status(thm)], [c_30, c_37])).
% 2.51/1.35  tff(c_26, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.51/1.35  tff(c_239, plain, (![A_54, B_55, C_56]: (k4_lattices(A_54, B_55, C_56)=k2_lattices(A_54, B_55, C_56) | ~m1_subset_1(C_56, u1_struct_0(A_54)) | ~m1_subset_1(B_55, u1_struct_0(A_54)) | ~l1_lattices(A_54) | ~v6_lattices(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.51/1.35  tff(c_247, plain, (![B_55]: (k4_lattices('#skF_3', B_55, '#skF_5')=k2_lattices('#skF_3', B_55, '#skF_5') | ~m1_subset_1(B_55, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_239])).
% 2.51/1.35  tff(c_255, plain, (![B_55]: (k4_lattices('#skF_3', B_55, '#skF_5')=k2_lattices('#skF_3', B_55, '#skF_5') | ~m1_subset_1(B_55, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_41, c_247])).
% 2.51/1.35  tff(c_261, plain, (![B_57]: (k4_lattices('#skF_3', B_57, '#skF_5')=k2_lattices('#skF_3', B_57, '#skF_5') | ~m1_subset_1(B_57, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_255])).
% 2.51/1.35  tff(c_293, plain, (k4_lattices('#skF_3', '#skF_4', '#skF_5')=k2_lattices('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_28, c_261])).
% 2.51/1.35  tff(c_24, plain, (~r1_lattices('#skF_3', k4_lattices('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.51/1.35  tff(c_299, plain, (~r1_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_24])).
% 2.51/1.35  tff(c_144, plain, (![A_49, C_50, B_51]: (k4_lattices(A_49, C_50, B_51)=k4_lattices(A_49, B_51, C_50) | ~m1_subset_1(C_50, u1_struct_0(A_49)) | ~m1_subset_1(B_51, u1_struct_0(A_49)) | ~l1_lattices(A_49) | ~v6_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.51/1.35  tff(c_152, plain, (![B_51]: (k4_lattices('#skF_3', B_51, '#skF_5')=k4_lattices('#skF_3', '#skF_5', B_51) | ~m1_subset_1(B_51, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_144])).
% 2.51/1.35  tff(c_160, plain, (![B_51]: (k4_lattices('#skF_3', B_51, '#skF_5')=k4_lattices('#skF_3', '#skF_5', B_51) | ~m1_subset_1(B_51, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_41, c_152])).
% 2.51/1.35  tff(c_166, plain, (![B_52]: (k4_lattices('#skF_3', B_52, '#skF_5')=k4_lattices('#skF_3', '#skF_5', B_52) | ~m1_subset_1(B_52, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_160])).
% 2.51/1.35  tff(c_199, plain, (k4_lattices('#skF_3', '#skF_5', '#skF_4')=k4_lattices('#skF_3', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_28, c_166])).
% 2.51/1.35  tff(c_298, plain, (k4_lattices('#skF_3', '#skF_5', '#skF_4')=k2_lattices('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_199])).
% 2.51/1.35  tff(c_249, plain, (![B_55]: (k4_lattices('#skF_3', B_55, '#skF_4')=k2_lattices('#skF_3', B_55, '#skF_4') | ~m1_subset_1(B_55, u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | ~v6_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_239])).
% 2.51/1.35  tff(c_259, plain, (![B_55]: (k4_lattices('#skF_3', B_55, '#skF_4')=k2_lattices('#skF_3', B_55, '#skF_4') | ~m1_subset_1(B_55, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_41, c_249])).
% 2.51/1.35  tff(c_330, plain, (![B_61]: (k4_lattices('#skF_3', B_61, '#skF_4')=k2_lattices('#skF_3', B_61, '#skF_4') | ~m1_subset_1(B_61, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_259])).
% 2.51/1.35  tff(c_345, plain, (k4_lattices('#skF_3', '#skF_5', '#skF_4')=k2_lattices('#skF_3', '#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_330])).
% 2.51/1.35  tff(c_362, plain, (k2_lattices('#skF_3', '#skF_5', '#skF_4')=k2_lattices('#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_345])).
% 2.51/1.35  tff(c_16, plain, (![A_22, B_23, C_24]: (m1_subset_1(k2_lattices(A_22, B_23, C_24), u1_struct_0(A_22)) | ~m1_subset_1(C_24, u1_struct_0(A_22)) | ~m1_subset_1(B_23, u1_struct_0(A_22)) | ~l1_lattices(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.51/1.35  tff(c_371, plain, (m1_subset_1(k2_lattices('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_3')) | ~l1_lattices('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_362, c_16])).
% 2.51/1.35  tff(c_375, plain, (m1_subset_1(k2_lattices('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_26, c_28, c_371])).
% 2.51/1.35  tff(c_376, plain, (m1_subset_1(k2_lattices('#skF_3', '#skF_4', '#skF_5'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_36, c_375])).
% 2.51/1.35  tff(c_42, plain, (![A_34]: (l2_lattices(A_34) | ~l3_lattices(A_34))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.51/1.35  tff(c_46, plain, (l2_lattices('#skF_3')), inference(resolution, [status(thm)], [c_30, c_42])).
% 2.51/1.35  tff(c_51, plain, (![A_41, B_42, C_43]: (r1_lattices(A_41, B_42, C_43) | k1_lattices(A_41, B_42, C_43)!=C_43 | ~m1_subset_1(C_43, u1_struct_0(A_41)) | ~m1_subset_1(B_42, u1_struct_0(A_41)) | ~l2_lattices(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.51/1.35  tff(c_61, plain, (![B_42]: (r1_lattices('#skF_3', B_42, '#skF_4') | k1_lattices('#skF_3', B_42, '#skF_4')!='#skF_4' | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | ~l2_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_51])).
% 2.51/1.35  tff(c_71, plain, (![B_42]: (r1_lattices('#skF_3', B_42, '#skF_4') | k1_lattices('#skF_3', B_42, '#skF_4')!='#skF_4' | ~m1_subset_1(B_42, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_61])).
% 2.51/1.35  tff(c_72, plain, (![B_42]: (r1_lattices('#skF_3', B_42, '#skF_4') | k1_lattices('#skF_3', B_42, '#skF_4')!='#skF_4' | ~m1_subset_1(B_42, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_71])).
% 2.51/1.35  tff(c_398, plain, (r1_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k1_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_5'), '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_376, c_72])).
% 2.51/1.35  tff(c_422, plain, (k1_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_5'), '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_299, c_398])).
% 2.51/1.35  tff(c_32, plain, (v8_lattices('#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.51/1.35  tff(c_304, plain, (![A_58, B_59, C_60]: (k1_lattices(A_58, k2_lattices(A_58, B_59, C_60), C_60)=C_60 | ~m1_subset_1(C_60, u1_struct_0(A_58)) | ~m1_subset_1(B_59, u1_struct_0(A_58)) | ~v8_lattices(A_58) | ~l3_lattices(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.51/1.35  tff(c_314, plain, (![B_59]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_59, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_59, u1_struct_0('#skF_3')) | ~v8_lattices('#skF_3') | ~l3_lattices('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_304])).
% 2.51/1.35  tff(c_324, plain, (![B_59]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_59, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_59, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_314])).
% 2.51/1.35  tff(c_428, plain, (![B_62]: (k1_lattices('#skF_3', k2_lattices('#skF_3', B_62, '#skF_4'), '#skF_4')='#skF_4' | ~m1_subset_1(B_62, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_36, c_324])).
% 2.51/1.35  tff(c_446, plain, (k1_lattices('#skF_3', k2_lattices('#skF_3', '#skF_5', '#skF_4'), '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_26, c_428])).
% 2.51/1.35  tff(c_464, plain, (k1_lattices('#skF_3', k2_lattices('#skF_3', '#skF_4', '#skF_5'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_362, c_446])).
% 2.51/1.35  tff(c_466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_422, c_464])).
% 2.51/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.35  
% 2.51/1.35  Inference rules
% 2.51/1.35  ----------------------
% 2.51/1.35  #Ref     : 0
% 2.51/1.35  #Sup     : 81
% 2.51/1.35  #Fact    : 0
% 2.51/1.35  #Define  : 0
% 2.51/1.35  #Split   : 4
% 2.51/1.35  #Chain   : 0
% 2.51/1.35  #Close   : 0
% 2.51/1.35  
% 2.51/1.35  Ordering : KBO
% 2.51/1.35  
% 2.51/1.35  Simplification rules
% 2.51/1.35  ----------------------
% 2.51/1.35  #Subsume      : 0
% 2.51/1.35  #Demod        : 64
% 2.51/1.35  #Tautology    : 31
% 2.51/1.35  #SimpNegUnit  : 36
% 2.51/1.35  #BackRed      : 2
% 2.51/1.35  
% 2.51/1.35  #Partial instantiations: 0
% 2.51/1.35  #Strategies tried      : 1
% 2.51/1.35  
% 2.51/1.35  Timing (in seconds)
% 2.51/1.35  ----------------------
% 2.51/1.35  Preprocessing        : 0.33
% 2.51/1.35  Parsing              : 0.17
% 2.51/1.35  CNF conversion       : 0.02
% 2.51/1.35  Main loop            : 0.24
% 2.51/1.35  Inferencing          : 0.08
% 2.51/1.35  Reduction            : 0.08
% 2.51/1.35  Demodulation         : 0.05
% 2.51/1.35  BG Simplification    : 0.02
% 2.51/1.35  Subsumption          : 0.04
% 2.51/1.35  Abstraction          : 0.02
% 2.51/1.35  MUC search           : 0.00
% 2.51/1.35  Cooper               : 0.00
% 2.51/1.35  Total                : 0.60
% 2.51/1.35  Index Insertion      : 0.00
% 2.51/1.35  Index Deletion       : 0.00
% 2.51/1.35  Index Matching       : 0.00
% 2.51/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
